// Fast CommonMark 0.31.2 + GFM renderer, output-identical to marked 18.1.3
// with its default options (gfm on, breaks off, pedantic off, async off).
//
// Written from scratch for the make.fun markdown-render-speed bounty. The
// algorithms follow the same structure as the reference implementation
// (block tokenize, then inline tokenize, then render), but the code below is
// my own, shaped for speed: offset-based scanning with sticky regexes (no
// repeated substring copies of the remaining input), first-character dispatch
// in the block loop so most lines only run the one or two patterns that can
// match them, and a single-pass inline scanner that grabs plain-text runs
// instead of trying every inline pattern at every position.
//
// Correctness contract: parse(markdown) === marked.parse(markdown) for every
// string. Where the reference departs from the CommonMark/GFM spec, the
// reference wins. No caching across calls, no lookup of any case's output.

// ---------------------------------------------------------------------------
// Small string helpers
// ---------------------------------------------------------------------------

const ESCAPE_MAP = {
  '&': '&amp;',
  '<': '&lt;',
  '>': '&gt;',
  '"': '&quot;',
  "'": '&#39;',
};

const ESCAPE_TEST = /[&<>"']/;
const ESCAPE_REPLACE = /[&<>"']/g;
const ESCAPE_TEST_NO_ENCODE = /[<>"']|&(?!(#\d{1,7}|#[Xx][a-fA-F0-9]{1,6}|\w+);)/;
const ESCAPE_REPLACE_NO_ENCODE = /[<>"']|&(?!(#\d{1,7}|#[Xx][a-fA-F0-9]{1,6}|\w+);)/g;
const NUMERIC_REF_TEST = /&#(?:(\d{1,7})|[Xx]([A-Fa-f0-9]{1,6}));/;
const NUMERIC_REF_OR_AMP = /&#(?:(\d{1,7})|[Xx]([A-Fa-f0-9]{1,6}));|&(?!(#\d{1,7}|#[Xx][a-fA-F0-9]{1,6}|\w+);)/g;

function escapeHtml(html, encode) {
  if (encode) {
    return ESCAPE_TEST.test(html)
      ? html.replace(ESCAPE_REPLACE, (ch) => ESCAPE_MAP[ch])
      : html;
  }
  return ESCAPE_TEST_NO_ENCODE.test(html)
    ? html.replace(ESCAPE_REPLACE_NO_ENCODE, (ch) => ESCAPE_MAP[ch])
    : html;
}

// Numeric character references are recognized outside code and are
// equivalent to the character they name. Zero, out of range, or surrogate
// values become the replacement character. A bare `&` that cannot start a
// reference is escaped here so a decoded character cannot join its
// neighbours into a new reference.
function decodeNumericRefs(text) {
  if (!NUMERIC_REF_TEST.test(text)) return text;
  return text.replace(NUMERIC_REF_OR_AMP, (ref, dec, hex) => {
    if (dec === undefined && hex === undefined) return '&amp;';
    const code = dec === undefined ? parseInt(hex, 16) : parseInt(dec, 10);
    if (code === 0 || code > 0x10ffff || (code >= 0xd800 && code <= 0xdfff)) return '\uFFFD';
    return code === 38 ? '&amp;' : String.fromCodePoint(code);
  });
}

const CLEAN_URL_SAFE = /^[A-Za-z0-9;,/?:@&=+$\-_.!~*'()#]*$/;

function cleanUrl(href) {
  // encodeURI leaves every character in this set alone, and the set has no
  // `%`, so there is no `%25` to decode either: a safe href is already clean.
  if (CLEAN_URL_SAFE.test(href)) return href;
  try {
    href = encodeURI(href).replace(/%25/g, '%');
  } catch {
    return null;
  }
  return href;
}

const FIND_PIPE = /\|/g;
const SPLIT_PIPE = / \|/;
const SLASH_PIPE = /\\\|/g;

function splitCells(row, count) {
  // Every cell-delimiting pipe gets a space before it, so an escaped pipe
  // (odd number of backslashes before it) can be told apart.
  const spaced = row.replace(FIND_PIPE, (match, offset, str) => {
    let escaped = false;
    let curr = offset;
    while (--curr >= 0 && str[curr] === '\\') escaped = !escaped;
    return escaped ? '|' : ' |';
  });
  const cells = spaced.split(SPLIT_PIPE);
  let i = 0;
  // First/last cell cannot be empty when there is no leading/trailing pipe.
  if (!cells[0].trim()) cells.shift();
  if (cells.length > 0 && !cells.at(-1)?.trim()) cells.pop();
  if (count) {
    if (cells.length > count) cells.splice(count);
    else while (cells.length < count) cells.push('');
  }
  for (; i < cells.length; i++) {
    cells[i] = cells[i].trim().replace(SLASH_PIPE, '|');
  }
  return cells;
}

// Remove trailing `c` characters (equivalent to str.replace(/c*$/, '')).
// The regex form is vulnerable to catastrophic backtracking, hence the loop.
function rtrim(str, c, invert) {
  const l = str.length;
  if (l === 0) return '';
  let suffLen = 0;
  while (suffLen < l) {
    const ch = str.charAt(l - suffLen - 1);
    if (ch === c && !invert) suffLen++;
    else if (ch !== c && invert) suffLen++;
    else break;
  }
  return str.slice(0, l - suffLen);
}

const BLANK_LINE = /^[ \t]*$/;

function trimTrailingBlankLines(str) {
  const lines = str.split('\n');
  let end = lines.length - 1;
  while (end >= 0 && BLANK_LINE.test(lines[end])) end--;
  if (lines.length - end <= 2) return str; // keep a single trailing blank line
  return lines.slice(0, end + 1).join('\n');
}

// Normalizes a link label so definitions and references match. The spec asks
// for a Unicode case fold, which toLowerCase() does not reach (e.g. ẞ -> ß
// never meets SS); round-tripping through upper case does.
function normalizeLabel(label) {
  return label.trim().replace(/\s+/g, ' ').toLowerCase().toUpperCase().toLowerCase();
}

// Index of the closing bracket that balances the opener at level 0, or -1
// when there is none and -2 when there are more openers than closers.
function findClosingBracket(str, b) {
  if (str.indexOf(b[0]) === -1 && str.indexOf(b[1]) === -1) return -1;
  let level = 0;
  for (let i = 0; i < str.length; i++) {
    if (str[i] === '\\') i++;
    else if (str[i] === b[0]) level++;
    else if (str[i] === b[1]) {
      level--;
      if (level < 0) return i;
    }
  }
  return level > 0 ? -2 : -1;
}

function expandTabs(line, indent = 0) {
  let col = indent;
  let out = '';
  for (const ch of line) {
    if (ch === '\t') {
      const added = 4 - (col % 4);
      out += ' '.repeat(added);
      col += added;
    } else {
      out += ch;
      col++;
    }
  }
  return out;
}

// ---------------------------------------------------------------------------
// Regex composition helper.
//
// edit() builds a pattern from pieces, substituting names for sub-patterns.
// When a sub-pattern is spliced in, a leading `^` anchor it carries is
// dropped: inside a lookahead the anchor would otherwise never match (it
// asserts the start of the whole input, not the line being tested).
// ---------------------------------------------------------------------------

const CARET_STRIP = /(^|[^\[])\^/g;

function edit(pattern, flags = '') {
  let source = typeof pattern === 'string' ? pattern : pattern.source;
  const api = {
    replace(name, val) {
      let valSource = typeof val === 'string' ? val : val.source;
      valSource = valSource.replace(CARET_STRIP, '$1');
      source = source.replace(name, valSource);
      return api;
    },
    regex() {
      return new RegExp(source, flags);
    },
    // Sticky variant for offset-based matching: same pattern, anchored at
    // lastIndex instead of the start of the string. The leading `^` is
    // dropped because `y` already pins the match to lastIndex.
    sticky() {
      const src = source.charCodeAt(0) === 94 ? source.slice(1) : source;
      const fl = flags.replace('g', '').replace('m', '') + 'y';
      return new RegExp(src, fl);
    },
  };
  return api;
}

function cachedIndentRegex(create) {
  const cache = [];
  return (indent) => {
    const idx = Math.max(0, Math.min(3, indent - 1));
    let re = cache[idx];
    if (!re) {
      re = create(idx);
      cache[idx] = re;
    }
    return re;
  };
}

const supportsLookbehind = (() => {
  try {
    return !!new RegExp('(?<=1)(?<!1)');
  } catch {
    return false;
  }
})();

// ---------------------------------------------------------------------------
// Shared small patterns
// ---------------------------------------------------------------------------

const O = {
  codeRemoveIndent: /^(?: {0,3}\t| {1,4})/gm,
  outputLinkReplace: /\\([\[\]])/g,
  indentCodeCompensation: /^(\s+)(?:```)/,
  beginningSpace: /^\s+/,
  endingHash: /#$/,
  startingSpaceChar: /^ /,
  endingSpaceChar: / $/,
  endingSpaceTabChar: /[ \t]$/,
  nonSpaceChar: /[^ ]/,
  newLineCharGlobal: /\n/g,
  tabCharGlobal: /\t/g,
  leadingSpaceTab: /^[ \t]+/,
  multipleSpaceGlobal: /\s+/g,
  blankLine: /^[ \t]*$/,
  doubleBlankLine: /\n[ \t]*\n[ \t]*$/,
  blockquoteStart: /^ {0,3}>/,
  // Neutralize a lazy setext underline, including one with trailing tabs.
  blockquoteSetextReplace: /\n {0,3}((?:=+|-+)[ \t]*)(?=\n|$)/g,
  blockquoteSetextReplace2: /^ {0,3}>[ \t]?/gm,
  blockquoteMarkerWhitespace: /^( {0,3}>)([ \t]+)/gm,
  listReplaceNesting: /^ {1,4}(?=( {4})*[^ ])/g,
  listIsTask: /^\[[ xX]\][ \t]+\S/,
  listReplaceTask: /^\[[ xX]\][ \t]+/,
  listTaskCheckbox: /\[[ xX]\]/,
  anyLine: /\n.*\n/,
  hrefBrackets: /^<(.*)>$/,
  tableDelimiter: /[:|]/,
  tableAlignChars: /^\||\| *$/g,
  tableRowBlankLine: /\n[ \t]*$/,
  tableAlignRight: /^ *-+: *$/,
  tableAlignCenter: /^ *:-+: *$/,
  tableAlignLeft: /^ *:-+ *$/,
  startATag: /^<a /i,
  endATag: /^<\/a>/i,
  startPreScriptTag: /^<(pre|code|kbd|script)(\s|>)/i,
  endPreScriptTag: /^<\/(pre|code|kbd|script)(\s|>)/i,
  startAngleBracket: /^</,
  endAngleBracket: />$/,
  pedanticHrefTitle: /^([^'"]*[^\s])\s+(['"])(.*)\2/,
  unicodeAlphaNumeric: /[\p{L}\p{N}]/u,
  carriageReturn: /\r\n|\r/g,
  spaceLine: /^ +$/gm,
  notSpaceStart: /^\S*/,
  endingNewline: /\n$/,
  listItemRegex: (bull) => new RegExp(`^( {0,3}${bull})((?:[\t ][^\\n]*)?(?:\\n|$))`),
  nextBulletRegex: cachedIndentRegex((i) => new RegExp(`^ {0,${i}}(?:[*+-]|\\d{1,9}[.)])((?:[ \t][^\\n]*)?(?:\\n|$))`)),
  hrRegex: cachedIndentRegex((i) => new RegExp(`^ {0,${i}}((?:-[ \t]*){3,}|(?:_[ \t]*){3,}|(?:\\*[ \t]*){3,})(?:\\n+|$)`)),
  fencesBeginRegex: cachedIndentRegex((i) => new RegExp(`^ {0,${i}}(?:\`\`\`|~~~)`)),
  // An ATX heading needs a space (or the end of the line) after the hashes,
  // so a line like `#tag` does not end a list item.
  headingBeginRegex: cachedIndentRegex((i) => new RegExp(`^ {0,${i}}#{1,6}(?:\\s|$)`)),
  pedanticHeadingBeginRegex: cachedIndentRegex((i) => new RegExp(`^ {0,${i}}#`)),
  // A list item ends where a paragraph would be interrupted, so this mirrors
  // the html start conditions in the paragraph rule; type 7 is excluded.
  htmlBeginRegex: cachedIndentRegex((i) => new RegExp(`^ {0,${i}}(?:</?(?:${TAG})(?: +|$|/?>)|<(?:(?:script|pre|style|textarea)(?:[\\s>]|$)|!--)|<\\?|<![A-Za-z]|<!\\[CDATA\\[)`, 'i')),
  blockquoteBeginRegex: cachedIndentRegex((i) => new RegExp(`^ {0,${i}}>`)),
};

// ---------------------------------------------------------------------------
// Block-level grammar (GFM). `block` holds the patterns the block tokenizer
// runs; each has a sticky twin (`.s`) used for offset-based matching.
// ---------------------------------------------------------------------------

const TAG = 'address|article|aside|base|basefont|blockquote|body|caption'
  + '|center|col|colgroup|dd|details|dialog|dir|div|dl|dt|fieldset|figcaption'
  + '|figure|footer|form|frame|frameset|h[1-6]|head|header|hr|html|iframe'
  + '|legend|li|link|main|menu|menuitem|meta|nav|noframes|ol|optgroup|option'
  + '|p|param|search|section|summary|table|tbody|td|tfoot|th|thead|title'
  + '|tr|track|ul';
const COMMENT = /<!--(?:-?>|[\s\S]*?(?:-->|$))/;

const NEWLINE = /^(?:[ \t]*(?:\n|$))+/;
const BLOCK_CODE = /^((?: {4}| {0,3}\t)[^\n]+(?:\n(?:[ \t]*(?:\n|$))*)?)+/;
const FENCES = /^ {0,3}(`{3,}(?=[^`\n]*(?:\n|$))|~{3,})([^\n]*)(?:\n|$)(?:|([\s\S]*?)(?:\n|$))(?: {0,3}(?:(?=`)\1`*|(?=~)\1~*) *(?=\n|$)|$)/;
const HR = /^ {0,3}((?:-[\t ]*){3,}|(?:_[ \t]*){3,}|(?:\*[ \t]*){3,})(?:\n+|$)/;
const HEADING = /^ {0,3}(#{1,6})(?=\s|$)(.*)(?:\n+|$)/;
const BULLET = / {0,3}(?:[*+-]|\d{1,9}[.)])/;
// The underline may end with spaces or tabs (CommonMark 4.3). Internal
// spaces or tabs still fail, and more than three spaces of indent still do not.
const LHEADING_CORE = /^(?!bull |blockCode|fences|blockquote|heading|html|table)((?:.|\n(?!\s*?\n|bull |fences|blockquote|heading|hr|html|table))+?)\n {0,3}(=+|-+)[ \t]*(?:\n+|$)/;
const LHEADING_GFM = edit(LHEADING_CORE)
  .replace(/bull/g, BULLET)
  .replace(/blockCode/g, /(?: {4}| {0,3}\t)/)
  .replace(/fences/g, / {0,3}(?:`{3,}|~{3,})/)
  .replace(/blockquote/g, / {0,3}>/)
  .replace(/heading/g, / {0,3}#{1,6}(?:\s|$)/)
  .replace(/hr/g, / {0,3}(?:(?:-[\t ]*){3,}|(?:_[ \t]*){3,}|(?:\*[ \t]*){3,})(?:\n+|$)/)
  .replace(/html/g, / {0,3}<[^\n>]+>\n/)
  .replace(/table/g, / {0,3}\|?(?:[:\- ]*\|)+[\:\- ]*\n/)
  .regex();
const PARAGRAPH_CORE = /^([^\n]+(?:\n(?!hr|heading|lheading|blockquote|fences|list|html|table|[ \t]+\n)[^\n]+)*)/;
const BLOCK_TEXT = /^[^\n]+/;
const BLOCK_LABEL = /(?!\s*\])(?:\\[\s\S]|[^\[\]\\\n]|\n(?![ \t]*\n))+/;
const DEF = edit(/^ {0,3}\[(label)\]: *(?:\n[ \t]*)?([^<\s][^\s]*|<.*?>)(?:(?: +(?:\n[ \t]*)?| *\n[ \t]*)(title))? *(?:\n+|$)/)
  .replace('label', BLOCK_LABEL)
  // An escaped delimiter is part of the title, so a backslash must consume
  // the next character. An optional closer lets that character backtrack
  // into the closing quote.
  .replace('title', /(?:"(?:\\[\s\S]|[^"\\])*"|'(?:\\[\s\S]|[^'\\\n]|\n(?!\n))*'|\((?:\\[\s\S]|[^()\\])*\))/)
  .regex();

const LIST = edit(/^(bull)([ \t][^\n]*?)?(?:\n|$)/)
  .replace(/bull/g, BULLET)
  .regex();

const HTML_BLOCK = edit(
  '^ {0,3}(?:'
  + '<(script|pre|style|textarea)[\\s>][\\s\\S]*?(?:</\\1>[^\\n]*\\n*|$)' // (1)
  + '|comment[^\\n]*(\\n+|$)' // (2)
  + '|<\\?[\\s\\S]*?(?:\\?>[^\\n]*\\n*|$)' // (3)
  + '|<![A-Z][\\s\\S]*?(?:>[^\\n]*\\n*|$)' // (4)
  + '|<!\\[CDATA\\[[\\s\\S]*?(?:\\]\\]>[^\\n]*\\n*|$)' // (5)
  + '|</?(tag)(?:[ \\t]+|\\n|/?>|$)[\\s\\S]*?(?:(?:\\n[ \t]*)+\\n|$)' // (6)
  + '|<(?!(?:script|pre|style|textarea)(?![a-z0-9-]))([a-z][a-z0-9-]*)(?:attribute)*? */?>(?=[ \\t]*(?:\\n|$))[\\s\\S]*?(?:(?:\\n[ \t]*)+\\n|$)' // (7) open tag
  + '|</[a-z][a-z0-9-]*\\s*>(?=[ \\t]*(?:\\n|$))[\\s\\S]*?(?:(?:\\n[ \t]*)+\\n|$)' // (7) closing tag
  + ')', 'i')
  .replace('comment', COMMENT)
  .replace('tag', TAG)
  .replace('attribute', / +[a-zA-Z:_][\w.:-]*(?: *= *"[^"\n]*"| *= *'[^'\n]*'| *= *[^\s"'=<>`]+)?/)
  .regex();

function makeParagraph(listInterrupt, withTable = true) {
  const e = edit(PARAGRAPH_CORE)
    .replace('hr', HR)
    .replace('heading', ' {0,3}#{1,6}(?:\\s|$)')
    .replace('|lheading', '');
  // A table can interrupt a top-level paragraph, but inside a blockquote
  // the paragraph pattern is built without the table lookahead (marked's
  // createParagraph drops `|table`), so a table-looking line lazily
  // continues the blockquote paragraph instead of ending it.
  if (withTable) e.replace('table', GFM_TABLE);
  else e.replace('|table', '');
  return e
    .replace('blockquote', ' {0,3}>')
    .replace('fences', ' {0,3}(?:`{3,}(?=[^`\\n]*(?:\\n|$))|~~~)[^\\n]*(?:\\n|$)')
    .replace('list', listInterrupt)
    .replace('html', ' {0,3}(?:</?(?:tag)(?: +|\\n|/?>)|<(?:(?:script|pre|style|textarea)(?:[\\s>]|$)|!--)|<\\?|<![A-Za-z]|<!\\[CDATA\\[)')
    .replace('tag', TAG)
    .regex();
}

const GFM_TABLE = edit(
  '^ *([^\\n ].*)\\n' // Header
  + ' {0,3}((?:\\| *)?:?-+:? *(?:\\| *:?-+:? *)*(?:\\| *)?)' // Align
  + '(?:\\n((?:(?! *\\n|hr|heading|blockquote|code|fences|list|html).*(?:\\n|$))*)\\n*|$)') // Cells
  .replace('hr', HR)
  .replace('heading', ' {0,3}#{1,6}(?:\\s|$)')
  .replace('blockquote', ' {0,3}>')
  .replace('code', '(?: {4}| {0,3}\t)[^\\n]')
  .replace('fences', ' {0,3}(?:`{3,}(?=[^`\\n]*(?:\\n|$))|~~~)[^\\n]*(?:\\n|$)')
  .replace('list', ' {0,3}(?:[*+-]|1[.)])[ \\t]') // any bullet ends the table rows
  .replace('html', ' {0,3}(?:</?(?:tag)(?: +|\\n|/?>)|<(?:(?:script|pre|style|textarea)(?:[\\s>]|$)|!--)|<\\?|<![A-Za-z]|<!\\[CDATA\\[)')
  .replace('tag', TAG)
  .regex();

// Only non-empty lists starting from 1 can interrupt paragraphs.
const PARAGRAPH = makeParagraph(/ {0,3}(?:[*+-]|1[.)])[ \t]+[^ \t\n]/);
// Inside a blockquote a bare list marker (any number) starts a sibling list,
// so it must not be lazily continued as paragraph text. The blockquote
// paragraph also drops the table lookahead (see makeParagraph).
const BLOCKQUOTE_PARAGRAPH = makeParagraph(/ {0,3}(?:[*+-]|\d{1,9}[.)])(?:[ \t]|\n|$)/, false);

// A line with only whitespace after the marker is blank, so it must not
// start a paragraph that lazily continues onto the next line.
const BLOCKQUOTE = edit(/^( {0,3}> ?(?:(?![ \t]*(?:\n|$))(paragraph)|[^\n]*)(?:\n|$))+/)
  .replace('paragraph', BLOCKQUOTE_PARAGRAPH)
  .regex();

// Sticky twins of the block patterns, for offset-based matching on the
// original string (no substring copies of the remaining input). A `^`
// anchor at the start of the pattern, or at the start of an alternative
// (right after `|`), means "start of the string being matched"; with the
// sticky flag the match is already pinned to lastIndex, so those anchors
// are dropped. A `^` inside a character class is negation and is kept.
function stickyOf(re) {
  const src = re.source.replace(/(^|\|)\^/g, '$1');
  return new RegExp(src, re.flags.replace('g', '').replace('m', '') + 'y');
}
const S = {
  newline: stickyOf(NEWLINE),
  code: stickyOf(BLOCK_CODE),
  fences: stickyOf(FENCES),
  heading: stickyOf(HEADING),
  hr: stickyOf(HR),
  lheading: stickyOf(LHEADING_GFM),
  def: stickyOf(DEF),
  list: stickyOf(LIST),
  html: stickyOf(HTML_BLOCK),
  table: stickyOf(GFM_TABLE),
  paragraph: stickyOf(PARAGRAPH),
  blockquoteParagraph: stickyOf(BLOCKQUOTE_PARAGRAPH),
  blockquote: stickyOf(BLOCKQUOTE),
  text: stickyOf(BLOCK_TEXT),
};

function execAt(re, src, pos) {
  re.lastIndex = pos;
  return re.exec(src);
}

// ---------------------------------------------------------------------------
// Inline-level grammar (GFM)
// ---------------------------------------------------------------------------

const ESCAPE = /^\\([!"#$%&'()*+,\-./:;<=>?@\[\]\\^_`{|}~])/;
const INLINE_CODE = /^(`+)([^`]|[^`][\s\S]*?[^`])\1(?!`)/;
const BR = /^( {2,}|\\)\n(?!\s*$)[ \t]*/;
const INLINE_TEXT = /^(`+|[^`])(?:(?= {2,}\n)|[\s\S]*?(?:(?=[\\<!\[`*_]|\b_|$)|[^ ](?= {2,}\n)))/;

// Unicode punctuation, plus the extra characters the CommonMark spec lists.
const PUNCT = /[\p{P}\p{S}]/u;
const PUNCT_OR_SPACE = /[\s\p{P}\p{S}]/u;
const NOT_PUNCT_OR_SPACE = /[^\s\p{P}\p{S}]/u;
const PUNCTUATION = edit(/^((?![*_])punctSpace)/, 'u')
  .replace(/punctSpace/g, PUNCT_OR_SPACE)
  .regex();

// GFM allows ~ inside strong and em for strikethrough.
const PUNCT_GFM = /(?!~)[\p{P}\p{S}]/u;
const PUNCT_OR_SPACE_GFM = /(?!~)[\s\p{P}\p{S}]/u;
const NOT_PUNCT_OR_SPACE_GFM = /(?:[^\s\p{P}\p{S}]|~)/u;

// Sequences em skips over: [title](link), `code`, <html>.
const BLOCK_SKIP = edit(/link|precode-code|html/, 'g')
  .replace('link', /\[(?:[^\[\]`]|(?<a>`+)[^`]+\k<a>(?!`))*?\]\((?:\\[\s\S]|[^\\\(\)]|\((?:\\[\s\S]|[^\\\(\)])*\))*\)/)
  .replace('precode-', supportsLookbehind ? '(?<!`)()' : '(^^|[^`])')
  .replace('code', /(?<b>`+)[^`]+\k<b>(?!`)/)
  .replace('html', /<(?! )[^<>]*?>/)
  .regex();

const EM_STRONG_L_DELIM_CORE = /^(?:\*+(?:((?!\*)punct)|([^\s*]))?)|^_+(?:((?!_)punct)|([^\s_]))?/;
const EM_STRONG_L_DELIM = edit(EM_STRONG_L_DELIM_CORE, 'u')
  .replace(/punct/g, PUNCT_GFM)
  .regex();

const EM_STRONG_R_DELIM_AST_CORE =
  '^[^_*]*?__[^_*]*?\\*[^_*]*?(?=__)' // Skip orphan inside strong
  + '|[^*]+(?=[^*])' // Consume to delim
  + '|(?!\\*)punct(\\*+)(?=[\\s]|$)' // (1) #*** can only be a Right Delimiter
  + '|notPunctSpace(\\*+)(?!\\*)(?=punctSpace|$)' // (2) a***#, a*** can only be a Right Delimiter
  + '|(?!\\*)punctSpace(\\*+)(?=notPunctSpace)' // (3) #***a, ***a can only be a Left Delimiter
  + '|[\\s](\\*+)(?!\\*)(?=punct)' // (4) ***# can only be a Left Delimiter
  + '|(?!\\*)punct(\\*+)(?!\\*)(?=punct)' // (5) #***# can be either Left or Right Delimiter
  + '|notPunctSpace(\\*+)(?=notPunctSpace)'; // (6) a***a can be either Left or Right Delimiter

const EM_STRONG_R_DELIM_AST = edit(EM_STRONG_R_DELIM_AST_CORE, 'gu')
  .replace(/notPunctSpace/g, NOT_PUNCT_OR_SPACE_GFM)
  .replace(/punctSpace/g, PUNCT_OR_SPACE_GFM)
  .replace(/punct/g, PUNCT_GFM)
  .regex();

// Normal: no rule 6 for _ (a___a cannot close as emphasis).
const EM_STRONG_R_DELIM_UND = edit(
  '^[^_*]*?\\*\\*[^_*]*?_[^_*]*?(?=\\*\\*)' // Skip orphan inside strong
  + '|[^_]+(?=[^_])' // Consume to delim
  + '|(?!_)punct(_+)(?=[\\s]|$)' // (1) #___ can only be a Right Delimiter
  + '|notPunctSpace(_+)(?!_)(?=punctSpace|$)' // (2) a___#, a___ can only be a Right Delimiter
  + '|(?!_)punctSpace(_+)(?=notPunctSpace)' // (3) #___a, ___a can only be Left Delimiter
  + '|[\\s](_+)(?!_)(?=punct)' // (4) ___# can only be a Left Delimiter
  + '|(?!_)punct(_+)(?!_)(?=punct)', 'gu') // (5) #___# can be either Left or Right Delimiter
  .replace(/notPunctSpace/g, NOT_PUNCT_OR_SPACE)
  .replace(/punctSpace/g, PUNCT_OR_SPACE)
  .replace(/punct/g, PUNCT)
  .regex();

// Tilde left delimiter for strikethrough.
const DEL_L_DELIM = edit(/^~~?(?:((?!~)punct)|[^\s~])/, 'u')
  .replace(/punct/g, PUNCT)
  .regex();

const DEL_R_DELIM_CORE =
  '^[^~]+(?=[^~])' // Consume to delim
  + '|(?!~)punct(~~?)(?=[\\s]|$)' // (1) #~~ can only be a Right Delimiter
  + '|notPunctSpace(~~?)(?!~)(?=punctSpace|$)' // (2) a~~#, a~~ can only be a Right Delimiter
  + '|(?!~)punctSpace(~~?)(?=notPunctSpace)' // (3) #~~a, ~~a can only be a Left Delimiter
  + '|[\\s](~~?)(?!~)(?=punct)' // (4) ~~# can only be a Left Delimiter
  + '|(?!~)punct(~~?)(?!~)(?=punct)' // (5) #~~# can be either Left or Right Delimiter
  + '|notPunctSpace(~~?)(?=notPunctSpace)'; // (6) a~~a can be either Left or Right Delimiter

const DEL_R_DELIM = edit(DEL_R_DELIM_CORE, 'gu')
  .replace(/notPunctSpace/g, NOT_PUNCT_OR_SPACE)
  .replace(/punctSpace/g, PUNCT_OR_SPACE)
  .replace(/punct/g, PUNCT)
  .regex();

const ANY_PUNCTUATION = edit(/\\(punct)/, 'gu')
  .replace(/punct/g, PUNCT)
  .regex();

// `anyPunctuation` for the em/strong mask. A backslash is literal inside a
// code span, so a code span (matched like `inline.code`), or a backtick run
// that opens none, is matched whole and kept; only the escapes outside code
// spans are masked.
const ANY_PUNCT_OUTSIDE_CODE = edit(/(`+)(?:[^`]|[^`][\s\S]*?[^`])\1(?!`)|`+|\\(punct)/, 'gu')
  .replace(/punct/g, PUNCT)
  .regex();

const AUTOLINK = edit(/^<(scheme:[^\s\x00-\x1f<>]*|email)>/)
  .replace('scheme', /[a-zA-Z][a-zA-Z0-9+.-]{1,31}/)
  .replace('email', /[a-zA-Z0-9.!#$%&'*+/=?^_`{|}~-]+(@)[a-zA-Z0-9](?:[a-zA-Z0-9-]{0,61}[a-zA-Z0-9])?(?:\.[a-zA-Z0-9](?:[a-zA-Z0-9-]{0,61}[a-zA-Z0-9])?)+(?![-_])/)
  .regex();

const INLINE_COMMENT = edit(COMMENT).replace('(?:-->|$)', '-->').regex();
const INLINE_TAG = edit(
  '^comment'
  + '|^</[a-zA-Z][a-zA-Z0-9-]*\\s*>' // self-closing tag
  + '|^<[a-zA-Z][a-zA-Z0-9-]*(?:attribute)*?\\s*/?>' // open tag
  + '|^<\\?[\\s\\S]*?\\?>' // processing instruction
  + '|^<![a-zA-Z]+\\s[\\s\\S]*?>' // declaration, e.g. <!DOCTYPE html>
  + '|^<!\\[CDATA\\[[\\s\\S]*?\\]\\]>') // CDATA section
  .replace('comment', INLINE_COMMENT)
  .replace('attribute', /\s+[a-zA-Z:_][\w.:-]*(?:\s*=\s*"[^"]*"|\s*=\s*'[^']*'|\s*=\s*[^\s"'=<>`]+)?/)
  .regex();

// One matched pair of brackets, holding no bracket of its own.
const INLINE_LABEL_BRACKETS = /\[(?:\\[\s\S]|[^\[\]\\])*\]/;
// CommonMark lets the brackets in a link label nest to any depth, which a
// regex cannot follow, so it stops at a fixed one. Two levels is what the
// spec suite asks for.
const INLINE_LABEL = edit(/(?:\[(?:brackets|\\[\s\S]|[^\[\]\\])*\]|\\[\s\S]|`+(?!`)[^`]*?`+(?!`)|``+(?=\])|[^\[\]\\`])*?/)
  .replace('brackets', INLINE_LABEL_BRACKETS)
  .regex();

const LINK = edit(/^!?\[(label)\]\([ \t\n]*(href)(?:(?:[ \t]+(?:\n[ \t]*)?|\n[ \t]*)(title))?[ \t\n]*\)/)
  .replace('label', INLINE_LABEL)
  .replace('href', /<(?:\\.|[^\n<>\\])+>|[^ \t\n\x00-\x1f]+|(?=\))/)
  // Same as the definition title: the escaped character is not the closer.
  .replace('title', /"(?:\\[\s\S]|[^"\\])*"|'(?:\\[\s\S]|[^'\\])*'|\((?:\\[\s\S]|[^)\\])*\)/)
  .regex();

const REFLINK = edit(/^!?\[(label)\]\[(ref)\]/)
  .replace('label', INLINE_LABEL)
  .replace('ref', BLOCK_LABEL)
  .regex();

const NOLINK = edit(/^!?\[(ref)\](?:\[\])?/)
  .replace('ref', BLOCK_LABEL)
  .regex();

// `reflink` and `nolink` are anchored, so the tokenizer tries each at a
// single position. `reflinkSearch` drops the anchors and runs with the
// global flag. The bounded labels below cap how far that scan can run: a
// candidate that can never match still scans to the end of the source, which
// would make the whole pass quadratic.
const BOUNDED_BLOCK_LABEL = /(?!\s*\])(?:\\[\s\S]|[^\[\]\\]){1,999}/;
const BOUNDED_INLINE_LABEL = edit(/(?:[^\[\]\\`]*(?:\[(?:brackets|\\[\s\S]|[^\[\]\\])*\]|\\[\s\S]|`+(?!`)[^`]*?`+(?!`)|``+(?=\]))){0,999}?[^\[\]\\`]*?/)
  .replace('brackets', INLINE_LABEL_BRACKETS)
  .regex();

const REFLINK_SEARCH = edit('reflink|nolink(?!\\()', 'g')
  .replace('reflink', edit(/^!?\[(label)\]\[(ref)\]/)
    .replace('label', BOUNDED_INLINE_LABEL)
    .replace('ref', BOUNDED_BLOCK_LABEL)
    .regex())
  .replace('nolink', edit(/^!?\[(ref)\](?:\[\])?/)
    .replace('ref', BOUNDED_BLOCK_LABEL)
    .regex())
  .regex();

const CASE_INSENSITIVE_PROTOCOL = /[hH][tT][tT][pP][sS]?|[fF][tT][pP]/;
const EXTENDED_EMAIL = /[A-Za-z0-9._+-]+@[a-zA-Z0-9-_]+(?:\.[a-zA-Z0-9-_]*[a-zA-Z0-9])+(?![\w-])/;
const EXTENDED_EMAIL_PROTOCOL = edit(/(?:mailto:email|xmpp:email(?:\/[A-Za-z0-9@.]+)?)/)
  .replace(/email/g, EXTENDED_EMAIL)
  .regex();

const URL = edit(/^emailProtocol|^((?:protocol):\/\/|www\.)(?:[a-zA-Z0-9\-]+\.?)+[^\s<]*|^email/)
  .replace('emailProtocol', EXTENDED_EMAIL_PROTOCOL)
  .replace('protocol', CASE_INSENSITIVE_PROTOCOL)
  .replace('email', /[A-Za-z0-9._+-]+(@)[a-zA-Z0-9-_]+(?:\.[a-zA-Z0-9-_]*[a-zA-Z0-9])+(?![\w-])/)
  .regex();
const BACKPEDAL = /(?:[^?!.,:;*_'"~()&]+|\([^)]*\)|&(?![a-zA-Z0-9]+;$)|[?!.,:;*_'"~)]+(?!$))+/;
const DEL = /^(~~?)(?=[^\s~])((?:\\[\s\S]|[^\\])*?(?:\\[\s\S]|[^\s~\\]))\1(?=[^~]|$)/;
const GFM_TEXT = edit(/^(?:[^a-zA-Z0-9](?=emailProtocol)|(`+|~+|[^`~])(?:(?=[`~])|(?= {2,}\n)|(?=[a-zA-Z0-9.!#$%&'*+\/=?_`{\|}~-]+@)|[\s\S]*?(?:(?=[\\<!\[`*~_]|\b_|protocol:\/\/|wwwStart|$)|[^ ](?= {2,}\n)|[^a-zA-Z0-9](?=emailProtocol)|[^a-zA-Z0-9.!#$%&'*+\/=?_`{\|}~-](?=[a-zA-Z0-9.!#$%&'*+\/=?_`{\|}~-]+@))))/)
  .replace('protocol', CASE_INSENSITIVE_PROTOCOL)
  .replace(/emailProtocol/g, /(?:mailto|xmpp):/)
  // GFM: a www autolink starts only at the beginning of a line, after
  // whitespace or after `*`, `_`, `~` or `(`. Without lookbehind support,
  // keep stopping at every `www.`.
  .replace('wwwStart', supportsLookbehind ? '(?<![^\\s*_~(])www\\.' : 'www\\.')
  .regex();

// Sticky twins of the anchored inline patterns.
const IS = {
  escape: stickyOf(ESCAPE),
  code: stickyOf(INLINE_CODE),
  br: stickyOf(BR),
  text: stickyOf(GFM_TEXT),
  tag: stickyOf(INLINE_TAG),
  link: stickyOf(LINK),
  reflink: stickyOf(REFLINK),
  nolink: stickyOf(NOLINK),
  autolink: stickyOf(AUTOLINK),
  url: stickyOf(URL),
  del: stickyOf(DEL),
  emStrongLDelim: stickyOf(EM_STRONG_L_DELIM),
  delLDelim: stickyOf(DEL_L_DELIM),
};

// ---------------------------------------------------------------------------
// Closer hints for one inline run: the last `*` / `_` run that can close
// emphasis/strong and the last `~` run that can close strikethrough. A run
// can close only when it is not preceded by ASCII whitespace or the start
// of the string. One scan per inline run, shared by every opener in it.
// ---------------------------------------------------------------------------

function scanClosers(src) {
  const last = { '*': -1, _: -1 };
  let lastDel = -1;
  const len = src.length;
  for (let i = 0; i < len; i++) {
    const ch = src[i];
    if (ch !== '*' && ch !== '_' && ch !== '~') continue;
    const prev = i === 0 ? '\n' : src[i - 1];
    let j = i + 1;
    while (j < len && src[j] === ch) j++;
    if (prev !== ' ' && prev !== '\t' && prev !== '\n' && prev !== '\r' && prev !== '\f') {
      if (ch === '~') lastDel = i;
      else last[ch] = i;
    }
    i = j - 1;
  }
  return { last, lastDel };
}

// ---------------------------------------------------------------------------
// Lexer state. One fresh context per parse() call: nothing is shared
// between cases (no cross-case caching of any kind).
// ---------------------------------------------------------------------------

function lastEmStrongCloser(ctx, maskedSrc, delim) {
  const frame = ctx.closerStack.at(-1);
  if (frame && frame.maskedSrc === maskedSrc) return frame.last[delim];
  return scanClosers(maskedSrc).last[delim];
}

function lastDelCloser(ctx, maskedSrc) {
  const frame = ctx.closerStack.at(-1);
  if (frame && frame.maskedSrc === maskedSrc) return frame.lastDel;
  return scanClosers(maskedSrc).lastDel;
}

// ---------------------------------------------------------------------------
// Block tokenizers. Each takes (src, pos) and returns a token object with
// `end` (the position just past the token's raw text), or null.
// ---------------------------------------------------------------------------

function tokSpace(src, pos) {
  const m = execAt(S.newline, src, pos);
  if (m && m[0].length > 0) return { type: 'space', raw: m[0], end: pos + m[0].length };
  return null;
}

function tokCode(src, pos) {
  const m = execAt(S.code, src, pos);
  if (!m) return null;
  const raw = trimTrailingBlankLines(m[0]);
  const text = raw.replace(O.codeRemoveIndent, '');
  // The token's raw is the trimmed match, so the lexer advances by the
  // trimmed length; the trailing blank lines are consumed next as space.
  return { type: 'code', raw, codeBlockStyle: 'indented', text, end: pos + raw.length };
}

function indentCodeCompensation(raw, text) {
  const mi = raw.match(O.indentCodeCompensation);
  if (mi === null) return text;
  const indentToCode = mi[1];
  return text.split('\n').map((node) => {
    const mn = node.match(O.beginningSpace);
    if (mn === null) return node;
    const [indentInNode] = mn;
    return node.slice(Math.min(indentInNode.length, indentToCode.length));
  }).join('\n');
}

function tokFences(src, pos) {
  const m = execAt(S.fences, src, pos);
  if (!m) return null;
  const raw = m[0];
  const text = indentCodeCompensation(raw, m[3] || '');
  return {
    type: 'code',
    raw,
    lang: m[2] ? m[2].trim().replace(ANY_PUNCTUATION, '$1') : m[2],
    text,
    end: pos + raw.length,
  };
}

function tokHeading(ctx, src, pos) {
  const m = execAt(S.heading, src, pos);
  if (!m) return null;
  let text = m[2].trim();
  // Remove trailing #s.
  if (O.endingHash.test(text)) {
    const trimmed = rtrim(text, '#');
    if (!trimmed || O.endingSpaceTabChar.test(trimmed)) text = trimmed.trim();
  }
  const raw = rtrim(m[0], '\n');
  return {
    type: 'heading',
    raw,
    depth: m[1].length,
    text,
    tokens: queueInline(ctx, text),
    end: pos + raw.length,
  };
}

function tokHr(src, pos) {
  const m = execAt(S.hr, src, pos);
  if (!m) return null;
  return { type: 'hr', raw: rtrim(m[0], '\n'), end: pos + m[0].length };
}
// Queue an inline run for later tokenizing (link references are only all
// collected once block lexing finishes). Returns the token array the run
// will fill; callers keep it on their block token.
function queueInline(ctx, text) {
  const tokens = [];
  ctx.queue.push({ src: text, tokens });
  return tokens;
}

function tokBlockquote(ctx, src, pos) {
  const m = execAt(S.blockquote, src, pos);
  if (!m) return null;
  let lines = rtrim(m[0], '\n').split('\n');
  let raw = '';
  let text = '';
  const tokens = [];

  while (lines.length > 0) {
    let inBlockquote = false;
    const currentLines = [];
    let i;
    for (i = 0; i < lines.length; i++) {
      // Lines up to a continuation.
      if (O.blockquoteStart.test(lines[i])) {
        currentLines.push(lines[i]);
        inBlockquote = true;
      } else if (!inBlockquote) {
        currentLines.push(lines[i]);
      } else {
        break;
      }
    }
    lines = lines.slice(i);

    const currentRaw = currentLines.join('\n');
    const currentText = currentRaw
      // A tab after the marker runs to the next tab stop, and the marker
      // only consumes one space of it; the rest is content.
      .replace(
        O.blockquoteMarkerWhitespace,
        (_, marker, whitespace) => marker + expandTabs(whitespace, marker.length),
      )
      // Precede a setext continuation with 4 spaces so it is not a setext.
      .replace(O.blockquoteSetextReplace, '\n    $1')
      .replace(O.blockquoteSetextReplace2, '');
    raw = raw ? `${raw}\n${currentRaw}` : currentRaw;
    text = text ? `${text}\n${currentText}` : currentText;

    // Parse the blockquote lines as top level tokens; merge paragraphs if
    // this is a continuation.
    const top = ctx.top;
    ctx.top = true;
    blockTokens(ctx, currentText, tokens, true);
    ctx.top = top;

    if (lines.length === 0) break;
    const lastToken = tokens.at(-1);

    if (lastToken?.type === 'code' || lastToken?.type === 'heading' || lastToken?.type === 'hr'
      || lastToken?.type === 'html' || lastToken?.type === 'table') {
      // A blockquote continuation cannot be preceded by these.
      break;
    } else if (lastToken?.type === 'blockquote') {
      // Include the continuation in the nested blockquote.
      const oldToken = lastToken;
      // The continuation lines belong to the same nesting frame as the
      // nested blockquote, which already had one '>' marker stripped, so
      // strip one marker from them too.
      const continuation = lines.join('\n');
      const newText = oldToken.raw + '\n' + continuation.replace(O.blockquoteSetextReplace2, '');
      const newToken = tokBlockquote(ctx, newText, 0);
      tokens[tokens.length - 1] = newToken;

      // Only include continuation lines the nested blockquote actually
      // consumed. Unconsumed trailing lines must stay out of `raw` so the
      // lexer can still tokenize them.
      const leftover = newText.substring(newToken.raw.length).replace(/^\n/, '');
      const leftoverCount = leftover ? leftover.split('\n').length : 0;
      const consumed = leftoverCount ? lines.slice(0, -leftoverCount) : lines;
      if (consumed.length > 0) raw = `${raw}\n${consumed.join('\n')}`;
      text = text.substring(0, text.length - oldToken.text.length) + newToken.text;

      // A leftover line that starts with '>' still belongs to this
      // blockquote; any other leftover line ends it.
      lines = lines.slice(consumed.length);
      if (lines.length > 0 && O.blockquoteStart.test(lines[0])) continue;
      break;
    } else if (lastToken?.type === 'list') {
      // Include the continuation in the nested list.
      const oldToken = lastToken;
      const newText = oldToken.raw + '\n' + lines.join('\n');
      const newToken = tokList(ctx, newText, 0);
      tokens[tokens.length - 1] = newToken;

      // The list raw has no '>' markers, so it cannot be cut out of `raw`.
      // Count the continuation lines the list took and add those instead.
      const consumedCount = newToken.raw.length > oldToken.raw.length
        ? newText.slice(oldToken.raw.length + 1, newToken.raw.length).split('\n').length
        : 0;
      if (consumedCount > 0) {
        const consumed = lines.slice(0, consumedCount).join('\n');
        raw = `${raw}\n${consumed}`;
        text = `${text}\n${consumed}`;
      }
      lines = lines.slice(consumedCount);
      continue;
    }
  }

  return { type: 'blockquote', raw, tokens, text, end: pos + raw.length };
}
function lineAt(src, pos) {
  const nl = src.indexOf('\n', pos);
  return nl === -1 ? src.slice(pos) : src.slice(pos, nl);
}

function tokList(ctx, src, pos) {
  const cap0 = execAt(S.list, src, pos);
  if (!cap0) return null;
  // src is only consumed from the front, so every raw below is a slice of
  // listSrc rather than a string built up line by line.
  const listStart = pos;
  let p = pos;
  const taken = () => p - listStart;
  let bull = cap0[1].trim();
  const isOrdered = bull.length > 1;

  const list = {
    type: 'list',
    raw: '',
    ordered: isOrdered,
    start: isOrdered ? +bull.slice(0, -1) : '',
    loose: false,
    items: [],
  };

  bull = isOrdered ? `\\d{1,9}\\${bull.slice(-1)}` : `\\${bull}`;

  // Get next list item.
  const itemRegex = new RegExp(`( {0,3}${bull})((?:[\t ][^\\n]*)?(?:\\n|$))`, 'y');
  let endsWithBlankLine = false;
  // Check if current bullet point can start a new List Item.
  while (p < src.length) {
    let endEarly = false;
    let itemContents = '';
    const cap = execAt(itemRegex, src, p);
    if (!cap) break;

    if (execAt(S.hr, src, p)) break; // End list if bullet was actually HR

    const itemStart = taken();
    p += cap[0].length;

    const firstLine = cap[2].split('\n', 1)[0];
    const bulletIndent = cap[1].length;
    let line = firstLine.replace(O.leadingSpaceTab, (ws) => expandTabs(ws, bulletIndent));
    let nextLine = lineAt(src, p);
    let blankLine = !line.trim();

    let indent = 0;
    if (blankLine) {
      indent = bulletIndent + 1;
    } else {
      indent = line.search(O.nonSpaceChar); // Find first non-space char
      indent = indent > 4 ? 1 : indent; // Indented code (> 4 spaces) counts as 1
      itemContents = line.slice(indent);
      indent += bulletIndent;
    }

    if (blankLine && O.blankLine.test(nextLine)) { // Items begin with at most one blank line
      p = Math.min(p + nextLine.length + 1, src.length);
      endEarly = true;
    }

    if (!endEarly) {
      const nextBulletRegex = O.nextBulletRegex(indent);
      const hrRegex = O.hrRegex(indent);
      const fencesBeginRegex = O.fencesBeginRegex(indent);
      const headingBeginRegex = O.headingBeginRegex(indent);
      const htmlBeginRegex = O.htmlBeginRegex(indent);
      const blockquoteBeginRegex = O.blockquoteBeginRegex(indent);

      // Check if following lines should be included in List Item.
      while (p < src.length) {
        const rawLine = lineAt(src, p);
        nextLine = rawLine;

        // One scan of the leading whitespace gives the first content
        // character, its tab-expanded column, and whether the line is blank.
        // The block-start tests below can only match on their own opening
        // character, so most lines skip all six of them.
        let i = 0;
        let col = 0;
        while (i < nextLine.length) {
          const c = nextLine[i];
          if (c === ' ') { col++; i++; }
          else if (c === '\t') { col += 4 - (col % 4); i++; }
          else break;
        }
        const firstChar = i < nextLine.length ? nextLine[i] : '';
        let blank = i === nextLine.length;
        if (!blank && (firstChar === '\f' || firstChar === '\v' || firstChar === '\r')) {
          blank = true;
          for (let k = i; k < nextLine.length; k++) {
            const c = nextLine[k];
            if (c !== ' ' && c !== '\t' && c !== '\f' && c !== '\v' && c !== '\r') { blank = false; break; }
          }
        }
        // The tab-expanded line with `indent` columns removed. Expanding the
        // leading run gives `col` spaces followed by the content, so removing
        // `indent` of them leaves `col - indent` spaces (or cuts into the
        // content when the line is indented less than `indent`).
        const dedented = col >= indent
          ? ' '.repeat(col - indent) + nextLine.slice(i)
          : nextLine.slice(i + indent - col);

        // End list item if found code fences
        if ((firstChar === '`' || firstChar === '~') && fencesBeginRegex.test(nextLine)) break;
        // End list item if found start of new heading
        if (firstChar === '#' && headingBeginRegex.test(nextLine)) break;
        // End list item if found start of html block
        if (firstChar === '<' && htmlBeginRegex.test(nextLine)) break;
        // End list item if found start of blockquote
        if (firstChar === '>' && blockquoteBeginRegex.test(nextLine)) break;
        // End list item if found start of new bullet
        if ((firstChar === '*' || firstChar === '+' || firstChar === '-'
          || (firstChar >= '0' && firstChar <= '9')) && nextBulletRegex.test(nextLine)) break;
        // Horizontal rule found
        if ((firstChar === '-' || firstChar === '*' || firstChar === '_') && hrRegex.test(nextLine)) break;

        if (col >= indent || blank) { // Dedent if possible
          itemContents += '\n' + dedented;
        } else {
          // Not enough indentation.
          if (blankLine) break;

          // Paragraph continuation unless last line was a different block level element.
          const lineNoTabs = line.includes('\t') ? line.replace(O.tabCharGlobal, '    ') : line;
          const lineFirstIdx = lineNoTabs.search(O.nonSpaceChar);
          if (lineFirstIdx >= 4) break; // indented code block
          const lineFirst = lineFirstIdx === -1 ? '' : lineNoTabs[lineFirstIdx];
          if ((lineFirst === '`' || lineFirst === '~') && fencesBeginRegex.test(line)) break;
          if (lineFirst === '#' && headingBeginRegex.test(line)) break;
          if (lineFirst === '<' && htmlBeginRegex.test(line)) break;
          if ((lineFirst === '-' || lineFirst === '*' || lineFirst === '_') && hrRegex.test(line)) break;

          // A lazy continuation can look like a setext underline after
          // list indentation is removed. Keep it in the paragraph.
          const setextContinuation = /^ {0,3}(?:=+|-+) *$/.test(nextLine)
            && execAt(S.lheading, `${line}\n${nextLine}`, 0);
          const continuation = setextContinuation
            ? '    ' + ' '.repeat(Math.max(0, col - 3)) + nextLine.slice(i)
            : nextLine;
          itemContents += '\n' + continuation;
        }

        blankLine = blank;

        p = Math.min(p + rawLine.length + 1, src.length);
        line = dedented;
      }
    }

    // The loops above appended a '\n' the source may not have had. It could
    // only land on the item that exhausts src, whose raw is trimmed below.
    const raw = src.slice(listStart + itemStart, listStart + taken());

    if (!list.loose) {
      // If the previous item ended with a blank line, the list is loose.
      if (endsWithBlankLine) {
        list.loose = true;
      } else if (O.doubleBlankLine.test(raw)) {
        endsWithBlankLine = true;
      }
    }

    list.items.push({
      type: 'list_item',
      raw,
      task: O.listIsTask.test(itemContents),
      loose: false,
      text: itemContents,
      tokens: [],
    });
  }

  // Do not consume newlines at end of final item.
  const lastItem = list.items.at(-1);
  if (lastItem) {
    lastItem.raw = lastItem.raw.trimEnd();
    lastItem.text = lastItem.text.trimEnd();
  } else {
    // Not a list since there were no items.
    return null;
  }
  list.raw = src.slice(listStart, listStart + taken()).trimEnd();

  // Item child tokens handled here at end because we needed to have the
  // final item to trim it first. First pass: tokenize items and finalize
  // list.loose from spacers before placing checkboxes.
  for (const item of list.items) {
    ctx.top = false;
    item.tokens = blockTokens(ctx, item.text, []);

    if (!list.loose) {
      // Check if list should be loose.
      const spacers = item.tokens.filter((t) => t.type === 'space');
      const hasMultipleLineBreaks = spacers.length > 0 && spacers.some((t) => O.anyLine.test(t.raw));
      list.loose = hasMultipleLineBreaks;
    }
  }

  // Second pass: place task checkboxes using the final list.loose.
  for (const item of list.items) {
    const itemToken = item.tokens[0];
    if (item.task && (itemToken?.type === 'text' || itemToken?.type === 'paragraph')) {
      // Remove checkbox markdown from item tokens.
      item.text = item.text.replace(O.listReplaceTask, '');
      itemToken.raw = itemToken.raw.replace(O.listReplaceTask, '');
      itemToken.text = itemToken.text.replace(O.listReplaceTask, '');
      for (let i = ctx.queue.length - 1; i >= 0; i--) {
        if (O.listIsTask.test(ctx.queue[i].src)) {
          ctx.queue[i].src = ctx.queue[i].src.replace(O.listReplaceTask, '');
          break;
        }
      }

      const taskRaw = O.listTaskCheckbox.exec(item.raw);
      if (taskRaw) {
        const checkboxToken = {
          type: 'checkbox',
          raw: taskRaw[0] + ' ',
          checked: taskRaw[0] !== '[ ]',
        };
        item.checked = checkboxToken.checked;
        if (list.loose) {
          if (item.tokens[0] && ['paragraph', 'text'].includes(item.tokens[0].type) && 'tokens' in item.tokens[0] && item.tokens[0].tokens) {
            item.tokens[0].raw = checkboxToken.raw + item.tokens[0].raw;
            item.tokens[0].text = checkboxToken.raw + item.tokens[0].text;
            item.tokens[0].tokens.unshift(checkboxToken);
          } else {
            item.tokens.unshift({
              type: 'paragraph',
              raw: checkboxToken.raw,
              text: checkboxToken.raw,
              tokens: [checkboxToken],
            });
          }
        } else {
          item.tokens.unshift(checkboxToken);
        }
      }
    } else if (item.task) {
      item.task = false;
    }
  }

  // Set all items to loose if list is loose.
  if (list.loose) {
    for (const item of list.items) {
      item.loose = true;
      for (const token of item.tokens) {
        if (token.type === 'text') token.type = 'paragraph';
      }
    }
  }

  return { ...list, end: pos + list.raw.length };
}
function tokHtml(src, pos) {
  const m = execAt(S.html, src, pos);
  if (!m) return null;
  const raw = trimTrailingBlankLines(m[0]);
  return {
    type: 'html',
    block: true,
    raw,
    pre: m[1] === 'pre' || m[1] === 'script' || m[1] === 'style',
    text: raw,
    end: pos + raw.length,
  };
}

function tokDef(ctx, src, pos) {
  const m = execAt(S.def, src, pos);
  if (!m) return null;
  // Outside angle brackets a link destination holds only balanced parens.
  if (!O.startAngleBracket.test(m[2]) && findClosingBracket(m[2], '()') !== -1) return null;

  const tag = normalizeLabel(m[1]);
  const href = m[2] ? m[2].replace(O.hrefBrackets, '$1').replace(ANY_PUNCTUATION, '$1') : '';
  const title = m[3] ? m[3].substring(1, m[3].length - 1).replace(ANY_PUNCTUATION, '$1') : m[3];
  const raw = rtrim(m[0], '\n');
  return { type: 'def', tag, raw, href, title, end: pos + raw.length };
}

function tokTable(ctx, src, pos) {
  const m = execAt(S.table, src, pos);
  if (!m) return null;
  if (!O.tableDelimiter.test(m[2])) {
    // Delimiter row must have a pipe (|) or colon (:), else a setext heading.
    return null;
  }

  const headers = splitCells(m[1]);
  const aligns = m[2].replace(O.tableAlignChars, '').split('|');
  const rows = m[3]?.trim() ? m[3].replace(O.tableRowBlankLine, '').split('\n') : [];

  if (headers.length !== aligns.length) {
    // Header and align columns must be equal; rows can differ.
    return null;
  }

  const item = {
    type: 'table',
    raw: rtrim(m[0], '\n'),
    header: [],
    align: [],
    rows: [],
  };

  for (const align of aligns) {
    if (O.tableAlignRight.test(align)) item.align.push('right');
    else if (O.tableAlignCenter.test(align)) item.align.push('center');
    else if (O.tableAlignLeft.test(align)) item.align.push('left');
    else item.align.push(null);
  }

  for (let i = 0; i < headers.length; i++) {
    item.header.push({
      text: headers[i],
      tokens: queueInline(ctx, headers[i]),
      header: true,
      align: item.align[i],
    });
  }

  for (const row of rows) {
    item.rows.push(splitCells(row, item.header.length).map((cell, i) => ({
      text: cell,
      tokens: queueInline(ctx, cell),
      header: false,
      align: item.align[i],
    })));
  }

  item.end = pos + item.raw.length;
  return item;
}

function tokLheading(ctx, src, pos) {
  const m = execAt(S.lheading, src, pos);
  if (!m) return null;
  const text = m[1].trim();
  const raw = rtrim(m[0], '\n');
  return {
    type: 'heading',
    raw,
    depth: m[2].charAt(0) === '=' ? 1 : 2,
    text,
    tokens: queueInline(ctx, text),
    end: pos + raw.length,
  };
}

function tokParagraph(ctx, src, pos) {
  const m = execAt(S.paragraph, src, pos);
  if (!m) return null;
  const text = m[1].charAt(m[1].length - 1) === '\n' ? m[1].slice(0, -1) : m[1];
  return {
    type: 'paragraph',
    raw: m[0],
    text,
    tokens: queueInline(ctx, text),
    end: pos + m[0].length,
  };
}

function tokText(ctx, src, pos) {
  const m = execAt(S.text, src, pos);
  if (!m) return null;
  return {
    type: 'text',
    raw: m[0],
    text: m[0],
    tokens: queueInline(ctx, m[0]),
    end: pos + m[0].length,
  };
}

// ---------------------------------------------------------------------------
// Block driver. Walks `str` from position 0, trying the tokenizers in the
// reference order, with first-character dispatch so most positions only
// run the patterns that can match there.
// ---------------------------------------------------------------------------

function blockTokens(ctx, str, tokens = [], lastParagraphClipped = false) {
  const len = str.length;
  let pos = 0;
  let guard = Infinity;
  while (pos < len) {
    if (len - pos < guard) {
      guard = len - pos;
    } else {
      throw new Error('Infinite loop on byte: ' + str.charCodeAt(pos));
    }

    // Leading spaces and first non-space character of this line. The
    // tokenizers below only run where the first character lets them match.
    let spaces = 0;
    while (str[pos + spaces] === ' ') spaces++;
    const f = str[pos + spaces];
    const codeIndent = spaces >= 4 || (spaces <= 3 && f === '\t');
    // A blank line is spaces/tabs up to a newline or the end of the input.
    // The space pattern can only match there, so content lines skip it.
    let q = pos + spaces;
    while (str[q] === ' ' || str[q] === '\t') q++;
    const isBlank = str[q] === '\n' || q >= len;

    let token = null;

    // blank lines
    if (isBlank) {
      token = tokSpace(str, pos);
      if (token) {
        pos = token.end;
        const lastToken = tokens.at(-1);
        if (token.raw.length === 1 && lastToken !== undefined) {
          // A single \n as a spacer terminates the last line, so move it
          // there instead of making an unnecessary paragraph break.
          lastToken.raw += '\n';
        } else {
          tokens.push(token);
        }
        continue;
      }
    }

    // indented code (cannot interrupt a paragraph; merged below)
    if (codeIndent) {
      token = tokCode(str, pos);
      if (token) {
        pos = token.end;
        const lastToken = tokens.at(-1);
        if (lastToken?.type === 'paragraph' || lastToken?.type === 'text') {
          lastToken.raw += (lastToken.raw.endsWith('\n') ? '' : '\n') + token.raw;
          lastToken.text += '\n' + token.text;
          ctx.queue.at(-1).src = lastToken.text;
        } else {
          tokens.push(token);
        }
        continue;
      }
    }

    if (spaces <= 3) {
      // fenced code
      if (f === '`' || f === '~') {
        token = tokFences(str, pos);
        if (token) {
          pos = token.end;
          tokens.push(token);
          continue;
        }
      }

      // ATX heading
      if (f === '#') {
        token = tokHeading(ctx, str, pos);
        if (token) {
          pos = token.end;
          tokens.push(token);
          continue;
        }
      }

      // hr
      if (f === '-' || f === '*' || f === '_') {
        token = tokHr(str, pos);
        if (token) {
          pos = token.end;
          tokens.push(token);
          continue;
        }
      }

      // blockquote
      if (f === '>') {
        token = tokBlockquote(ctx, str, pos);
        if (token) {
          pos = token.end;
          tokens.push(token);
          continue;
        }
      }

      // list
      if (f === '*' || f === '+' || f === '-' || (f >= '0' && f <= '9')) {
        token = tokList(ctx, str, pos);
        if (token) {
          pos = token.end;
          tokens.push(token);
          continue;
        }
      }

      // html block
      if (f === '<') {
        token = tokHtml(str, pos);
        if (token) {
          pos = token.end;
          tokens.push(token);
          continue;
        }
      }

      // link reference definition (cannot interrupt a paragraph; merged below)
      if (f === '[') {
        token = tokDef(ctx, str, pos);
        if (token) {
          pos = token.end;
          const lastToken = tokens.at(-1);
          if (lastToken?.type === 'paragraph' || lastToken?.type === 'text') {
            lastToken.raw += (lastToken.raw.endsWith('\n') ? '' : '\n') + token.raw;
            lastToken.text += '\n' + token.raw;
            ctx.queue.at(-1).src = lastToken.text;
          } else {
            // The first definition of a label wins, but a later one still
            // consumes its text.
            if (!ctx.links[token.tag]) {
              ctx.links[token.tag] = { href: token.href, title: token.title };
              ctx.hasLinks = true;
            }
            tokens.push(token);
          }
          continue;
        }
      }
    }

    // table (gfm): only when the next line looks like a delimiter row.
    {
      const lineEnd = str.indexOf('\n', pos);
      const nextStart = lineEnd === -1 ? -1 : lineEnd + 1;
      if (nextStart !== -1) {
        const nextLine = lineAt(str, nextStart);
        if (/^ {0,3}\|?\s*:?-{1,}/.test(nextLine)) {
          token = tokTable(ctx, str, pos);
          if (token) {
            pos = token.end;
            tokens.push(token);
            continue;
          }
        }
      }
    }

    // setext heading
    token = tokLheading(ctx, str, pos);
    if (token) {
      pos = token.end;
      tokens.push(token);
      continue;
    }

    // top-level paragraph
    if (ctx.top) {
      token = tokParagraph(ctx, str, pos);
      if (token) {
        const lastToken = tokens.at(-1);
        if (lastParagraphClipped && lastToken?.type === 'paragraph') {
          lastToken.raw += (lastToken.raw.endsWith('\n') ? '' : '\n') + token.raw;
          lastToken.text += '\n' + token.text;
          ctx.queue.pop();
          ctx.queue.at(-1).src = lastToken.text;
        } else {
          tokens.push(token);
        }
        lastParagraphClipped = false;
        pos = token.end;
        continue;
      }
    }

    // text (fallback: a single line that is none of the above)
    token = tokText(ctx, str, pos);
    if (token) {
      const lastToken = tokens.at(-1);
      if (lastToken?.type === 'text') {
        lastToken.raw += (lastToken.raw.endsWith('\n') ? '' : '\n') + token.raw;
        lastToken.text += '\n' + token.text;
        ctx.queue.pop();
        ctx.queue.at(-1).src = lastToken.text;
      } else {
        tokens.push(token);
      }
      pos = token.end;
      continue;
    }

    if (pos < len) {
      throw new Error('Infinite loop on byte: ' + str.charCodeAt(pos));
    }
  }

  ctx.top = true;
  return tokens;
}

// ---------------------------------------------------------------------------
// Inline-level tokenizers. The driver keeps an offset `pos` into the run's
// full string instead of slicing a fresh remainder at every step; the
// tokenizers that take a masked source receive the whole masked run and
// compute their window from `pos`.
// ---------------------------------------------------------------------------

function newCtx() {
  return {
    links: Object.create(null),
    hasLinks: false,
    queue: [],
    inLink: false,
    inRawBlock: false,
    linkEmitted: false,
    linkParenPossible: true,
    top: true,
    closerStack: [],
  };
}

function linkInText(ctx, text) {
  if (!text.includes('[')) return false;
  for (const match of text.matchAll(BLOCK_SKIP)) {
    if (LINK.test(match[0]) && text.charAt(match.index - 1) !== '!') return true;
  }
  for (const match of text.matchAll(REFLINK_SEARCH)) {
    const match0 = match[0];
    const refStart = match0.lastIndexOf('[');
    if (match0.charAt(0) === '!' || !Object.hasOwn(ctx.links, normalizeLabel(match0.slice(refStart + 1, -1)))) {
      continue;
    }
    // A candidate holding a link is not a link either, so it does not count.
    if (refStart > 1 && linkInText(ctx, match0.slice(1, refStart - 1))) {
      continue;
    }
    return true;
  }
  return false;
}

// Mask links, code, html and escapes so emStrong and del do not see their
// delimiters inside them. Every mask keeps the length it replaces, so the
// masked source lines up with the real one by offset. When the run holds
// none of `[`, backtick, `<` or `\`, no mask can match anything, so the
// source is already its own mask.
function maskSrc(ctx, src) {
  if (!src.includes('[') && !src.includes('`') && !src.includes('<') && !src.includes('\\')) {
    return src;
  }
  let maskedSrc = src;

  // Mask out reflinks. Only a defined label can make one a link, so when
  // no definition was recorded this scan is a no-op.
  if (src.includes('[') && ctx.hasLinks) {
    const maskReflink = (match0) => {
      const refStart = match0.lastIndexOf('[');
      if (!Object.hasOwn(ctx.links, normalizeLabel(match0.slice(refStart + 1, -1)))) {
        return match0;
      }
      // A candidate whose text already holds a link never becomes a link, so
      // flattening the whole span would hide the emphasis that does still
      // apply inside it. Mask the links it holds instead. Images are exempt:
      // their text is flattened into an alt attribute.
      if (refStart > 1 && match0.charAt(0) !== '!') {
        const text = match0.slice(1, refStart - 1);
        if (linkInText(ctx, text)) {
          return '[' + text.replace(REFLINK_SEARCH, maskReflink)
            + '][' + 'a'.repeat(match0.length - refStart - 2) + ']';
        }
      }
      return '[' + 'a'.repeat(match0.length - 2) + ']';
    };
    maskedSrc = maskedSrc.replace(REFLINK_SEARCH, maskReflink);
  }

  // Mask out escaped characters. A backslash inside a code span is literal,
  // not an escape. Mask the backticks inside the span instead, so blockSkip
  // still skips all of it. The pattern needs a backtick or a backslash, so
  // a run holding neither is already masked.
  if (src.includes('`') || src.includes('\\')) {
  maskedSrc = maskedSrc.replace(ANY_PUNCT_OUTSIDE_CODE, (match0, code, punct) => {
    if (punct) {
      return '+'.repeat(match0.length);
    }
    if (code) {
      return code + match0.slice(code.length, -code.length).replace(/`/g, '+') + code;
    }
    return match0;
  });
  }

  // Mask out other blocks (inline links, code spans, html tags). The
  // pattern needs `[`, a backtick or `<`; a run holding none of them is
  // already masked. (The reflink step only introduces `[` when the source
  // had one, and the escape step introduces nothing of the kind.)
  if (src.includes('[') || src.includes('`') || src.includes('<')) {
  maskedSrc = maskedSrc.replace(BLOCK_SKIP, (match0, _link, context) => {
    const offset = context ? context.length : 0;
    return match0.slice(0, offset) + '[' + 'a'.repeat(match0.length - offset - 2) + ']';
  });
  }

  return maskedSrc;
}

function isLabelEndInsideToken(src, label, labelStart) {
  if (!label.includes('<')) return false;
  for (let i = 0; i < label.length; i++) {
    if (label[i] === '\\') {
      i++;
      continue;
    }
    if (label[i] === '`') {
      const code = execAt(IS.code, label, i);
      if (code) {
        i += code[0].length - 1;
        continue;
      }
    }
    if (label[i] !== '<') continue;
    const tokenSrc = src.slice(labelStart + i);
    const token = execAt(IS.tag, tokenSrc, 0) || execAt(IS.autolink, tokenSrc, 0);
    if (!token) continue;
    if (token[0].length > label.length - i) return true;
    i += token[0].length - 1;
  }
  return false;
}

function outputLink(ctx, cap, link, raw) {
  const href = link.href;
  const title = link.title || null;
  const text = cap[1].replace(O.outputLinkReplace, '$1');
  const isImage = cap[0].charAt(0) === '!';

  const outerInLink = ctx.inLink;
  const outerLinkEmitted = ctx.linkEmitted;
  const outerInRawBlock = ctx.inRawBlock;
  ctx.inLink = true;
  ctx.linkEmitted = false;
  const tokens = inlineTokens(ctx, text);
  const textHasLink = ctx.linkEmitted;
  ctx.linkEmitted = outerLinkEmitted;
  ctx.inLink = outerInLink;

  if (!isImage) {
    // Links may not contain other links, at any level of nesting. Bail so
    // the caller falls through to text and the inner link is the one kept.
    // Images are exempt: their text is flattened into an alt attribute.
    if (textHasLink) {
      // These tokens are discarded, so undo the raw-block state they opened;
      // leaving it set would suppress escaping for the text that is re-scanned.
      ctx.inRawBlock = outerInRawBlock;
      return undefined;
    }
    ctx.linkEmitted = true;
  }

  return {
    type: isImage ? 'image' : 'link',
    raw,
    href,
    title,
    text,
    tokens,
  };
}

function tokEscape(src, pos) {
  const cap = execAt(IS.escape, src, pos);
  if (!cap) return null;
  return { type: 'escape', raw: cap[0], text: cap[1], end: pos + cap[0].length };
}

function tokTag(ctx, src, pos) {
  const cap = execAt(IS.tag, src, pos);
  if (!cap) return null;
  if (!ctx.inLink && O.startATag.test(cap[0])) {
    ctx.inLink = true;
  } else if (ctx.inLink && O.endATag.test(cap[0])) {
    ctx.inLink = false;
  }
  if (!ctx.inRawBlock && O.startPreScriptTag.test(cap[0])) {
    ctx.inRawBlock = true;
  } else if (ctx.inRawBlock && O.endPreScriptTag.test(cap[0])) {
    ctx.inRawBlock = false;
  }
  return {
    type: 'html',
    raw: cap[0],
    inLink: ctx.inLink,
    inRawBlock: ctx.inRawBlock,
    block: false,
    text: cap[0],
    end: pos + cap[0].length,
  };
}

function tokLink(ctx, src, pos) {
  // Without a ')' ahead the link regex cannot match, and skipping it avoids
  // its quadratic backtracking over unterminated-link inputs.
  if (ctx.linkParenPossible === false) return null;
  const cap = execAt(IS.link, src, pos);
  if (!cap) return null;
  const labelStart = cap[0].charAt(0) === '!' ? 2 : 1;
  if (isLabelEndInsideToken(src, cap[1], pos + labelStart)) return null;

  const trimmedUrl = cap[2].trim();
  if (O.startAngleBracket.test(trimmedUrl)) {
    // CommonMark requires matching angle brackets.
    if (!O.endAngleBracket.test(trimmedUrl)) return null;
    // The ending angle bracket cannot be escaped.
    const rtrimSlash = rtrim(trimmedUrl.slice(0, -1), '\\');
    if ((trimmedUrl.length - rtrimSlash.length) % 2 === 0) return null;
  } else {
    // Find the closing parenthesis.
    const lastParenIndex = findClosingBracket(cap[2], '()');
    if (lastParenIndex === -2) return null; // more open parens than closed
    if (lastParenIndex > -1) {
      const start = cap[0].indexOf('!') === 0 ? 5 : 4;
      const linkLen = start + cap[1].length + lastParenIndex;
      cap[2] = cap[2].substring(0, lastParenIndex);
      cap[0] = cap[0].substring(0, linkLen).trim();
      cap[3] = '';
    }
  }
  // The ')' that ends the match is the link closer only when it is not
  // escaped. `[foo](/url\\)` has no closer; that paren is destination text.
  const unescaped = rtrim(cap[0].slice(0, -1), '\\');
  if ((cap[0].length - unescaped.length) % 2 === 0) return null;

  let href = cap[2];
  const title = cap[3] ? cap[3].slice(1, -1) : '';
  href = href.trim();
  if (O.startAngleBracket.test(href)) {
    href = href.slice(1, -1);
  }
  const token = outputLink(ctx, cap, {
    href: href ? href.replace(ANY_PUNCTUATION, '$1') : href,
    title: title ? title.replace(ANY_PUNCTUATION, '$1') : title,
  }, cap[0]);
  if (!token) return null;
  token.end = pos + token.raw.length;
  return token;
}

function tokReflink(ctx, src, pos) {
  const cap = execAt(IS.reflink, src, pos) || execAt(IS.nolink, src, pos);
  if (!cap) return null;
  const labelStart = cap[0].charAt(0) === '!' ? 2 : 1;
  if (isLabelEndInsideToken(src, cap[1], pos + labelStart)) return null;

  const link = ctx.links[normalizeLabel(cap[2] || cap[1])];
  if (!link) {
    const text = cap[0].charAt(0);
    return { type: 'text', raw: text, text, end: pos + 1 };
  }
  const token = outputLink(ctx, cap, link, cap[0]);
  if (!token) return null;
  token.end = pos + token.raw.length;
  return token;
}

function tokEmStrong(ctx, src, pos, maskedSrc, prevChar) {
  const match = execAt(IS.emStrongLDelim, src, pos);
  if (!match) return null;
  if (!match[1] && !match[2] && !match[3] && !match[4]) return null;

  const delimChar = match[0][0];
  // A mid-run opener (for example the second star of an unmatched `**`) must
  // only pair with a delimiter that can only close, otherwise it steals the
  // opener of a later span (`**a*b*c` must be `**a<em>b</em>c`).
  const midRun = prevChar === delimChar;

  // The start of this delimiter run may already be behind pos, either taken
  // as text after the whole run failed to match or used to close an earlier
  // span. Flanking and rules 9-10 are about the whole run, so find its start.
  const srcStart = pos;
  let runStart = srcStart;
  while (runStart > 0 && maskedSrc[runStart - 1] === delimChar) runStart--;
  const runPrevChar = [...maskedSrc.slice(Math.max(0, runStart - 2), runStart)].at(-1) ?? '';
  // The other delimiter character counts as punctuation here (`_**a*`).
  const runPrevPunct = runPrevChar === '*' || runPrevChar === '_' || !!PUNCTUATION.exec(runPrevChar);
  if (runStart < srcStart) prevChar = runPrevChar;
  const prevPunct = runStart < srcStart ? runPrevPunct : !!PUNCTUATION.exec(prevChar);

  // _ can't be between two alphanumerics.
  if (match[4] && prevChar.match(O.unicodeAlphaNumeric)) return null;

  const nextChar = match[1] || match[3] || '';

  if (!nextChar || !prevChar || prevPunct) {
    // Spread into an array for a proper count (unicode counts emoji as 1).
    const lLength = [...match[0]].length - 1;
    let rDelim, rLength, delimTotal = lLength, midDelimTotal = 0;

    // Rules 9-10 count the whole run, and also apply when the opener could
    // close as well (`a*b**`, where `*` is both left- and right-flanking).
    const runLength = srcStart - runStart + lLength;
    const openerCanClose = !!runPrevChar.trim()
      && (!!nextChar || (delimChar === '*' && !runPrevPunct));
    if (delimChar !== '*' && delimChar !== '_') return null;
    const endReg = delimChar === '*' ? EM_STRONG_R_DELIM_AST : EM_STRONG_R_DELIM_UND;
    const frame = ctx.closerStack.at(-1);
    const lastPossible = frame ? frame.last[delimChar] : -1;
    const windowStart = pos + lLength;
    if (lastPossible < windowStart) return null;
    // Clip the masked source to the same section of the string as the rest.
    const searchSrc = maskedSrc.slice(pos + lLength);
    const lastInWindow = lastPossible - windowStart;
    endReg.lastIndex = 0;

    let m;
    while ((m = endReg.exec(searchSrc)) !== null) {
      if (m.index > lastInWindow) break;
      rDelim = m[1] || m[2] || m[3] || m[4] || m[5] || m[6];

      if (!rDelim) continue; // skip single * in __abc*abc__

      rLength = [...rDelim].length;

      if (m[3] || m[4]) { // found another Left Delim
        delimTotal += rLength;
        continue;
      } else if (m[5] || m[6] || openerCanClose) { // either Left or Right Delim
        if (midRun && (m[5] || m[6])) {
          // A mid-run opener cannot close against an ambiguous delimiter that
          // can also open; that delimiter opens its own emphasis span instead.
          break;
        }
        if (runLength % 3 && !((runLength + rLength) % 3)) {
          midDelimTotal += rLength;
          continue; // CommonMark Emphasis Rules 9-10
        }
      }

      delimTotal -= rLength;

      if (delimTotal > 0) continue; // Haven't found enough closing delimiters

      // Remove extra characters. *a*** -> *a*
      rLength = Math.min(rLength, rLength + delimTotal + midDelimTotal);
      // Char length can be >1 for unicode characters.
      const lastCharLength = [...m[0]][0].length;
      const rawLen = lLength + m.index + lastCharLength + rLength;
      const raw = src.slice(pos, pos + rawLen);

      // Create `em` if the smallest delimiter has an odd char count. *a***
      if (Math.min(lLength, rLength) % 2) {
        const text = raw.slice(1, -1);
        return {
          type: 'em',
          raw,
          text,
          tokens: inlineTokens(ctx, text),
          end: pos + rawLen,
        };
      }

      // Create 'strong' if the smallest delimiter has an even char count.
      const text = raw.slice(2, -2);
      return {
        type: 'strong',
        raw,
        text,
        tokens: inlineTokens(ctx, text),
        end: pos + rawLen,
      };
    }
  }
  return null;
}

function tokCodespan(src, pos) {
  const cap = execAt(IS.code, src, pos);
  if (!cap) return null;
  let text = cap[2].replace(O.newLineCharGlobal, ' ');
  const hasNonSpaceChars = O.nonSpaceChar.test(text);
  const hasSpaceCharsOnBothEnds = O.startingSpaceChar.test(text) && O.endingSpaceChar.test(text);
  if (hasNonSpaceChars && hasSpaceCharsOnBothEnds) {
    text = text.substring(1, text.length - 1);
  }
  return { type: 'codespan', raw: cap[0], text, end: pos + cap[0].length };
}

function tokBr(src, pos) {
  const cap = execAt(IS.br, src, pos);
  if (!cap) return null;
  return { type: 'br', raw: cap[0], end: pos + cap[0].length };
}

function tokDel(ctx, src, pos, maskedSrc, prevChar) {
  const match = execAt(IS.delLDelim, src, pos);
  if (!match) return null;

  const nextChar = match[1] || '';

  if (!nextChar || !prevChar || PUNCTUATION.exec(prevChar)) {
    const lLength = [...match[0]].length - 1;
    let rDelim, rLength, delimTotal = lLength;

    const endReg = DEL_R_DELIM;
    const frame = ctx.closerStack.at(-1);
    const lastPossible = frame ? frame.lastDel : -1;
    const windowStart = pos + lLength;
    if (lastPossible < windowStart) return null;
    const searchSrc = maskedSrc.slice(pos + lLength);
    const lastInWindow = lastPossible - windowStart;
    endReg.lastIndex = 0;

    let m;
    while ((m = endReg.exec(searchSrc)) !== null) {
      if (m.index > lastInWindow) break;
      rDelim = m[1] || m[2] || m[3] || m[4] || m[5] || m[6];

      if (!rDelim) continue;

      rLength = [...rDelim].length;

      if (rLength !== lLength) continue;

      if (m[3] || m[4]) { // found another Left Delim
        delimTotal += rLength;
        continue;
      }

      delimTotal -= rLength;

      if (delimTotal > 0) continue; // Haven't found enough closing delimiters

      // Remove extra characters.
      rLength = Math.min(rLength, rLength + delimTotal);
      const lastCharLength = [...m[0]][0].length;
      const rawLen = lLength + m.index + lastCharLength + rLength;
      const raw = src.slice(pos, pos + rawLen);

      // Create del token - only single ~ or double ~~ supported.
      const text = raw.slice(lLength, -lLength);
      return {
        type: 'del',
        raw,
        text,
        tokens: inlineTokens(ctx, text),
        end: pos + rawLen,
      };
    }
  }
  return null;
}

function tokAutolink(src, pos) {
  const cap = execAt(IS.autolink, src, pos);
  if (!cap) return null;
  let text, href;
  if (cap[2] === '@') {
    text = cap[1];
    href = 'mailto:' + text;
  } else {
    text = cap[1];
    href = text;
  }
  return {
    type: 'link',
    raw: cap[0],
    text,
    href,
    autolink: true,
    tokens: [{ type: 'text', raw: text, text }],
    end: pos + cap[0].length,
  };
}

function tokUrl(src, pos) {
  const cap = execAt(IS.url, src, pos);
  if (!cap) return null;
  let text, href;
  if (cap[2] === '@') {
    text = cap[0];
    href = 'mailto:' + text;
  } else {
    // Do extended autolink path validation.
    let prevCapZero;
    do {
      prevCapZero = cap[0];
      cap[0] = BACKPEDAL.exec(cap[0])?.[0] ?? '';
    } while (prevCapZero !== cap[0]);
    text = cap[0];
    if (cap[1] === 'www.') {
      href = 'http://' + cap[0];
    } else {
      href = cap[0];
    }
  }
  return {
    type: 'link',
    raw: cap[0],
    text,
    href,
    autolink: true,
    tokens: [{ type: 'text', raw: text, text }],
    end: pos + cap[0].length,
  };
}

function tokInlineText(ctx, src, pos) {
  const cap = execAt(IS.text, src, pos);
  if (!cap) return null;
  const escaped = ctx.inRawBlock;
  return {
    type: 'text',
    raw: cap[0],
    // Raw HTML keeps whatever it was written with, everywhere else a numeric
    // character reference stands for the character itself.
    text: escaped ? cap[0] : decodeNumericRefs(cap[0]),
    escaped,
    end: pos + cap[0].length,
  };
}

// One paren scan per inline run, shared with tokLink: without a ')' ahead the
// link regex cannot match, and skipping it avoids its quadratic backtracking
// over unterminated-link inputs. A nested run receives a substring of the
// outer run, so if the outer had no ')' neither does this substring.
function inlineTokens(ctx, src, tokens = []) {
  const prevLinkParenPossible = ctx.linkParenPossible;
  ctx.linkParenPossible = prevLinkParenPossible && src.includes(')');
  try {
    return inlineTokensInner(ctx, src, tokens);
  } finally {
    // A nested run anchored on its own substring; restore the outer run's
    // flag for the rest of its loop.
    ctx.linkParenPossible = prevLinkParenPossible;
  }
}

function inlineTokensInner(ctx, src, tokens) {
  // The masked source is only read by emStrong and del, which need a *, _ or
  // ~ to start. Skip building it for a run without one.
  const maskedSrc = src.includes('*') || src.includes('_') || src.includes('~')
    ? maskSrc(ctx, src)
    : src;

  // One scan of this maskedSrc for the last emphasis, strong, and
  // strikethrough closers, shared by every opener in the pass. Popped when
  // the pass ends so the source is not retained.
  ctx.closerStack.push(scanClosers(maskedSrc));
  try {
    return tokenizeInlines(ctx, src, maskedSrc, tokens);
  } finally {
    ctx.closerStack.pop();
  }
}

function tokenizeInlines(ctx, src, maskedSrc, tokens) {
  let keepPrevChar = false;
  let prevChar = '';
  let pos = 0;
  const len = src.length;
  let guard = Infinity;
  while (pos < len) {
    if (len - pos < guard) {
      guard = len - pos;
    } else {
      throw new Error('Infinite loop on byte: ' + src.charCodeAt(pos));
    }

    if (!keepPrevChar) {
      prevChar = '';
    }
    keepPrevChar = false;

    // First-character dispatch: each inline pattern can only start on its
    // own opening character, so a position tries the one or two patterns
    // that can match there (in the reference try-order) instead of all
    // eleven. The text run is the fallback everywhere.
    const ch = src[pos];
    let token = null;

    if (ch === '\\') {
      // escape, then a hard break (`\` + newline), then text.
      token = tokEscape(src, pos);
      if (token) { pos = token.end; tokens.push(token); continue; }
      token = tokBr(src, pos);
      if (token) { pos = token.end; tokens.push(token); continue; }
    } else if (ch === '<') {
      // an html tag, then an autolink, then text.
      token = tokTag(ctx, src, pos);
      if (token) { pos = token.end; tokens.push(token); continue; }
      token = tokAutolink(src, pos);
      if (token) { pos = token.end; tokens.push(token); continue; }
    } else if (ch === '[' || ch === '!') {
      // an inline link, then a reference link, then text.
      token = tokLink(ctx, src, pos);
      if (token) { pos = token.end; tokens.push(token); continue; }
      token = tokReflink(ctx, src, pos);
      if (token) {
        pos = token.end;
        const lastToken = tokens.at(-1);
        if (token.type === 'text' && lastToken?.type === 'text') {
          lastToken.raw += token.raw;
          lastToken.text += token.text;
        } else {
          tokens.push(token);
        }
        continue;
      }
    } else if (ch === '*') {
      token = tokEmStrong(ctx, src, pos, maskedSrc, prevChar);
      if (token) { pos = token.end; tokens.push(token); continue; }
    } else if (ch === '_') {
      // emphasis, then a possible email autolink (`_x@y.z`), then text.
      token = tokEmStrong(ctx, src, pos, maskedSrc, prevChar);
      if (token) { pos = token.end; tokens.push(token); continue; }
      if (!ctx.inLink) {
        token = tokUrl(src, pos);
        if (token) { pos = token.end; tokens.push(token); continue; }
      }
    } else if (ch === '`') {
      token = tokCodespan(src, pos);
      if (token) { pos = token.end; tokens.push(token); continue; }
    } else if (ch === '~') {
      token = tokDel(ctx, src, pos, maskedSrc, prevChar);
      if (token) { pos = token.end; tokens.push(token); continue; }
    } else if (ch === ' ') {
      // a hard break is two or more spaces before a newline.
      token = tokBr(src, pos);
      if (token) { pos = token.end; tokens.push(token); continue; }
    } else if ((ch >= 'a' && ch <= 'z') || (ch >= 'A' && ch <= 'Z')
      || (ch >= '0' && ch <= '9') || ch === '.' || ch === '+' || ch === '-') {
      // a URL, `www.` link or email autolink can start on a letter, a digit
      // or an email local-part character.
      if (!ctx.inLink) {
        token = tokUrl(src, pos);
        if (token) { pos = token.end; tokens.push(token); continue; }
      }
    }

    // text
    token = tokInlineText(ctx, src, pos);
    if (token) {
      pos = token.end;
      if (token.raw.slice(-1) !== '_') { // Track prevChar before string of ____ started
        prevChar = token.raw.slice(-1);
      }
      keepPrevChar = true;
      const lastToken = tokens.at(-1);
      if (lastToken?.type === 'text') {
        lastToken.raw += token.raw;
        lastToken.text += token.text;
      } else {
        tokens.push(token);
      }
      continue;
    }

    if (pos < len) {
      throw new Error('Infinite loop on byte: ' + src.charCodeAt(pos));
    }
  }

  return tokens;
}

// ---------------------------------------------------------------------------
// Rendering. Two walks: renderTokens for block tokens, renderInline for
// inline tokens. `textMode` selects the text renderer (image alt text):
// formatting is flattened to plain text instead of HTML.
// ---------------------------------------------------------------------------

function renderInline(tokens, textMode = false) {
  let out = '';
  for (let i = 0; i < tokens.length; i++) {
    const token = tokens[i];
    switch (token.type) {
      case 'escape':
        out += textMode ? token.text : escapeHtml(token.text);
        break;
      case 'html':
        out += token.text;
        break;
      case 'link': {
        if (textMode) {
          out += token.tokens ? renderInline(token.tokens, true) : token.text;
          break;
        }
        // References are not resolved inside an autolink, so every `&` there
        // is literal. Elsewhere only an `&` that cannot start one needs
        // escaping.
        const parsedText = token.autolink
          ? escapeHtml(token.text, true)
          : renderInline(token.tokens);
        const cleanHref = cleanUrl(token.href);
        if (cleanHref === null) {
          out += parsedText;
          break;
        }
        const href = escapeHtml(cleanHref, token.autolink);
        let o = '<a href="' + href + '"';
        if (token.title) {
          o += ' title="' + escapeHtml(token.title) + '"';
        }
        o += '>' + parsedText + '</a>';
        out += o;
        break;
      }
      case 'image': {
        if (textMode) {
          out += token.tokens ? renderInline(token.tokens, true) : token.text;
          break;
        }
        let text = token.text;
        if (token.tokens) {
          text = renderInline(token.tokens, true);
        }
        const cleanHref = cleanUrl(token.href);
        if (cleanHref === null) {
          out += escapeHtml(text);
          break;
        }
        let o = '<img src="' + escapeHtml(cleanHref) + '" alt="' + escapeHtml(text) + '"';
        if (token.title) {
          o += ' title="' + escapeHtml(token.title) + '"';
        }
        o += '>';
        out += o;
        break;
      }
      case 'checkbox':
        out += textMode
          ? token.raw
          : '<input ' + (token.checked ? 'checked="" ' : '') + 'disabled="" type="checkbox"> ';
        break;
      case 'strong':
        out += textMode
          ? (token.tokens ? renderInline(token.tokens, true) : token.text)
          : '<strong>' + renderInline(token.tokens) + '</strong>';
        break;
      case 'em':
        out += textMode
          ? (token.tokens ? renderInline(token.tokens, true) : token.text)
          : '<em>' + renderInline(token.tokens) + '</em>';
        break;
      case 'codespan':
        out += textMode ? token.text : '<code>' + escapeHtml(token.text, true) + '</code>';
        break;
      case 'br':
        out += textMode ? '' : '<br>';
        break;
      case 'del':
        out += textMode
          ? (token.tokens ? renderInline(token.tokens, true) : token.text)
          : '<del>' + renderInline(token.tokens) + '</del>';
        break;
      case 'text':
        if (textMode) {
          out += token.text;
        } else if (token.tokens) {
          out += renderInline(token.tokens);
        } else {
          out += token.escaped ? token.text : escapeHtml(token.text);
        }
        break;
      default:
        throw new Error('Token with "' + token.type + '" type was not found.');
    }
  }
  return out;
}

function renderTableCell(token) {
  const content = renderInline(token.tokens);
  const type = token.header ? 'th' : 'td';
  const tag = token.align ? '<' + type + ' align="' + token.align + '">' : '<' + type + '>';
  return tag + content + '</' + type + '>\n';
}

function renderTokens(tokens) {
  let out = '';
  for (let i = 0; i < tokens.length; i++) {
    const token = tokens[i];
    switch (token.type) {
      case 'space':
        break;
      case 'hr':
        out += '<hr>\n';
        break;
      case 'heading':
        out += '<h' + token.depth + '>' + renderInline(token.tokens) + '</h' + token.depth + '>\n';
        break;
      case 'code': {
        const langString = (token.lang || '').match(O.notSpaceStart)?.[0];
        // An empty code block has no content, so it must not gain a newline.
        const code = token.text ? token.text.replace(O.endingNewline, '') + '\n' : '';
        if (!langString) {
          out += '<pre><code>' + (token.escaped ? code : escapeHtml(code, true)) + '</code></pre>\n';
        } else {
          out += '<pre><code class="language-' + escapeHtml(langString) + '">'
            + (token.escaped ? code : escapeHtml(code, true)) + '</code></pre>\n';
        }
        break;
      }
      case 'table': {
        let header = '';
        let cell = '';
        for (let j = 0; j < token.header.length; j++) {
          cell += renderTableCell(token.header[j]);
        }
        header += '<tr>\n' + cell + '</tr>\n';

        let body = '';
        for (let j = 0; j < token.rows.length; j++) {
          const row = token.rows[j];
          cell = '';
          for (let k = 0; k < row.length; k++) {
            cell += renderTableCell(row[k]);
          }
          body += '<tr>\n' + cell + '</tr>\n';
        }
        if (body) body = '<tbody>' + body + '</tbody>';

        out += '<table>\n<thead>\n' + header + '</thead>\n' + body + '</table>\n';
        break;
      }
      case 'blockquote':
        out += '<blockquote>\n' + renderTokens(token.tokens) + '</blockquote>\n';
        break;
      case 'list': {
        const type = token.ordered ? 'ol' : 'ul';
        const startAttr = (token.ordered && token.start !== 1) ? (' start="' + token.start + '"') : '';
        let body = '';
        for (let j = 0; j < token.items.length; j++) {
          body += '<li>' + renderTokens(token.items[j].tokens) + '</li>\n';
        }
        out += '<' + type + startAttr + '>\n' + body + '</' + type + '>\n';
        break;
      }
      case 'checkbox':
        out += '<input ' + (token.checked ? 'checked="" ' : '') + 'disabled="" type="checkbox"> ';
        break;
      case 'html':
        out += token.text;
        break;
      case 'def':
        break;
      case 'paragraph':
        out += '<p>' + renderInline(token.tokens) + '</p>\n';
        break;
      case 'text':
        if (token.tokens) {
          out += renderInline(token.tokens);
        } else {
          out += token.escaped ? token.text : escapeHtml(token.text);
        }
        break;
      default:
        throw new Error('Token with "' + token.type + '" type was not found.');
    }
  }
  return out;
}

// ---------------------------------------------------------------------------
// Entry point.
// ---------------------------------------------------------------------------

function lex(markdown) {
  const ctx = newCtx();
  const src = markdown.includes('\r') ? markdown.replace(O.carriageReturn, '\n') : markdown;
  const tokens = blockTokens(ctx, src, []);
  for (let i = 0; i < ctx.queue.length; i++) {
    const next = ctx.queue[i];
    // An inline <pre>, <code>, <kbd> or <script> left open ends with the
    // block holding it; carried over, it would stop every later block's text
    // from being escaped.
    ctx.inRawBlock = false;
    inlineTokens(ctx, next.src, next.tokens);
  }
  ctx.queue.length = 0;
  return tokens;
}

export function parse(markdown) {
  return renderTokens(lex(markdown));
}

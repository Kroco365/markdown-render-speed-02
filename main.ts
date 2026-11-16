// Driver for the markdown-render-speed-02 entry. Reads every case from
// $MAKEFUN_INPUT_DIR/cases.json (or /input/cases.json when the variable is
// unset), renders each one alone with parse() from parse.js, and writes the
// HTML strings, in the cases' order, to $MAKEFUN_OUTPUT_DIR/html.json
// (or /output/html.json). Node 22, standard library only.
import { mkdirSync, readFileSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';
import { parse } from './parse.js';

const inputDir = process.env.MAKEFUN_INPUT_DIR ?? '/input';
const outputDir = process.env.MAKEFUN_OUTPUT_DIR ?? '/output';

const cases = JSON.parse(readFileSync(join(inputDir, 'cases.json'), 'utf8'));
if (!Array.isArray(cases)) throw new Error('cases.json must hold a JSON array');
const html = cases.map((c) => parse(c.markdown));
mkdirSync(outputDir, { recursive: true });
writeFileSync(join(outputDir, 'html.json'), JSON.stringify(html));

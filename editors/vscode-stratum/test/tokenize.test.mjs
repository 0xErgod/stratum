// Loads the Stratum TextMate grammar with vscode-textmate + vscode-oniguruma
// and tokenizes a sample program, asserting the key scopes VS Code themes color.
//
// Run: `npm install && npm test` (from editors/vscode-stratum/).
import { readFileSync } from "node:fs";
import { fileURLToPath } from "node:url";
import { dirname, join } from "node:path";
import { strict as assert } from "node:assert";
import onigModule from "vscode-oniguruma";
import vsctmModule from "vscode-textmate";

// vscode-oniguruma / vscode-textmate ship as CommonJS; under ESM interop the
// named exports land on `.default`.
const oniguruma = onigModule;
const vsctm = vsctmModule;

const __dirname = dirname(fileURLToPath(import.meta.url));
const root = join(__dirname, "..");

// --- Oniguruma WASM boot -------------------------------------------------
const wasmPath = join(
  root,
  "node_modules",
  "vscode-oniguruma",
  "release",
  "onig.wasm",
);
const wasmBin = readFileSync(wasmPath).buffer;
const onigLib = oniguruma.loadWASM(wasmBin).then(() => ({
  createOnigScanner: (patterns) => new oniguruma.OnigScanner(patterns),
  createOnigString: (s) => new oniguruma.OnigString(s),
}));

// --- Registry ------------------------------------------------------------
const grammarPath = join(root, "syntaxes", "stratum.tmLanguage.json");
const registry = new vsctm.Registry({
  onigLib,
  loadGrammar: async (scopeName) => {
    if (scopeName === "source.stratum") {
      const raw = readFileSync(grammarPath, "utf8");
      return vsctm.parseRawGrammar(raw, grammarPath);
    }
    return null;
  },
});

// --- Sample --------------------------------------------------------------
const sample = [
  "// comment",
  "def echo(c) { c(x).c!(*x) }",
  "new req, ack",
  "req!(0) | req(x).ack!(0)",
  "relay(a <- @0, b)",
];

// Collect (token-text, scopes[]) pairs across all lines.
function tokenizeAll(grammar) {
  let ruleStack = vsctm.INITIAL;
  const out = [];
  for (const line of sample) {
    const r = grammar.tokenizeLine(line, ruleStack);
    for (const t of r.tokens) {
      out.push({ text: line.slice(t.startIndex, t.endIndex), scopes: t.scopes });
    }
    ruleStack = r.ruleStack;
  }
  return out;
}

// Assert that at least one token whose trimmed text equals `text` carries a
// scope starting with `scopePrefix`. (A surface token like `req` can appear in
// two roles — `req!` as an identifier and `req(` as a call — so we search all
// occurrences rather than only the first.)
function assertScope(tokens, text, scopePrefix) {
  const matches = tokens.filter((t) => t.text.trim() === text);
  assert.ok(matches.length, `expected a token with text ${JSON.stringify(text)}`);
  const hit = matches.find((t) => t.scopes.some((s) => s.startsWith(scopePrefix)));
  assert.ok(
    hit,
    `token ${JSON.stringify(text)} occurrences ` +
      `${JSON.stringify(matches.map((t) => t.scopes))} ` +
      `should include a scope starting with ${JSON.stringify(scopePrefix)}`,
  );
  return hit;
}

const grammar = await registry.loadGrammar("source.stratum");
assert.ok(grammar, "grammar source.stratum failed to load");
const tokens = tokenizeAll(grammar);

// Explicit assertions.
assertScope(tokens, "// comment", "comment.line");
assertScope(tokens, "def", "keyword.control");
assertScope(tokens, "echo", "entity.name.function");
assertScope(tokens, "new", "keyword.control");
assertScope(tokens, "req", "entity.name.function"); // identifier before `(`
assertScope(tokens, "0", "constant.language"); // null process
assertScope(tokens, "!", "keyword.operator");
assertScope(tokens, "*", "keyword.operator");
assertScope(tokens, "|", "keyword.operator");
assertScope(tokens, "@", "keyword.operator");
assertScope(tokens, "<-", "keyword.operator");
assertScope(tokens, ".", "punctuation.separator");
assertScope(tokens, ",", "punctuation.separator");
assertScope(tokens, "x", "variable.other"); // bound name
assertScope(tokens, "a", "variable.parameter"); // named-arg param before `<-`

console.log(`Tokenized ${sample.length} lines, ${tokens.length} tokens.`);
console.log("Key scope assertions:");
const report = [
  ["// comment", "comment.line.double-slash.stratum"],
  ["def", "keyword.control.stratum"],
  ["echo", "entity.name.function.stratum"],
  ["new", "keyword.control.stratum"],
  ["req  (before `(`)", "entity.name.function.stratum"],
  ["0", "constant.language.stratum"],
  ["! * | @ <-", "keyword.operator.stratum"],
  [". ,", "punctuation.separator.stratum"],
  ["a  (before `<-`)", "variable.parameter.stratum"],
  ["x", "variable.other.stratum"],
];
for (const [k, v] of report) console.log(`  ${k.padEnd(22)} -> ${v}`);
console.log("\nAll assertions passed.");

# Stratum for VS Code

Syntax highlighting for the **Stratum** reflective higher-order (ρ) calculus
surface syntax. This extension registers a `stratum` language with a
[TextMate grammar](./syntaxes/stratum.tmLanguage.json), so it colours:

- **`.strat` files** opened in the VS Code editor, and
- **Stratum notebook cells** — cells executed by the Stratum Jupyter kernel.

> This is the VS Code companion to the JupyterLab CodeMirror extension in
> [`editors/jupyterlab-stratum/`](../jupyterlab-stratum/). They are independent:
> VS Code (including its notebook editor) uses TextMate grammars, while
> JupyterLab uses CodeMirror 6 language packages. Both mirror the authoritative
> tree-sitter highlight queries in
> `crates/stratum-syntax/tree-sitter/queries/highlights.scm`.

## Why notebook cells highlight

VS Code chooses a notebook cell's editor language from the kernel's
`language_info.name`. The Stratum kernel reports `language_info.name == "stratum"`,
which is exactly the language **id** this extension contributes. Installing the
extension therefore lights up both `.strat` documents and Stratum code cells with
no per-cell configuration.

## What gets highlighted

| Surface construct                      | TextMate scope                        |
| -------------------------------------- | ------------------------------------- |
| `def` / `new`                          | `keyword.control.stratum`             |
| `def NAME` — the definition name       | `entity.name.function.stratum`        |
| `NAME(` — macro call / input channel   | `entity.name.function.stratum`        |
| `nil` / `0` — the null process         | `constant.language.stratum`           |
| other integer literals                 | `constant.numeric.stratum`            |
| `@` `*` `!` `\|` `<-`                   | `keyword.operator.stratum`            |
| `param <-` — named-argument parameter  | `variable.parameter.stratum`          |
| `.` `,`                                | `punctuation.separator.stratum`       |
| `(` `)` `{` `}` `[` `]`                | `punctuation.brackets.stratum`        |
| `// …` line comment                    | `comment.line.double-slash.stratum`   |
| any other identifier                   | `variable.other.stratum`              |

Because TextMate is regex-only (no real parser), some distinctions the runtime
parser makes are approximated — e.g. an input channel `x(y).P` and a macro call
`f(args)` both read as *identifier before `(`* and are coloured as functions.
These are the same editor-only caveats the tree-sitter `locals.scm` documents.

## Install (development)

**Copy or symlink into your VS Code extensions folder, then reload.**

- macOS / Linux: `~/.vscode/extensions/`
- Windows: `%USERPROFILE%\.vscode\extensions\`

```sh
# macOS / Linux
ln -s "$(pwd)/editors/vscode-stratum" ~/.vscode/extensions/vscode-stratum

# Windows (PowerShell, from the repo root)
New-Item -ItemType SymbolicLink `
  -Path "$env:USERPROFILE\.vscode\extensions\vscode-stratum" `
  -Target "$(Resolve-Path editors\vscode-stratum)"
```

Then run **Developer: Reload Window** from the Command Palette (or restart VS Code).
Open a `.strat` file — the status-bar language should read **Stratum**.

## Install (packaged `.vsix`)

```sh
cd editors/vscode-stratum
npx @vscode/vsce package        # produces stratum-*.vsix
code --install-extension vscode-stratum-0.1.0.vsix
```

## Development / test

The grammar ships as declarative JSON — there is no build step. A Node test
loads the grammar with [`vscode-textmate`](https://www.npmjs.com/package/vscode-textmate)
+ [`vscode-oniguruma`](https://www.npmjs.com/package/vscode-oniguruma) and
tokenizes a sample program, asserting the key scopes:

```sh
cd editors/vscode-stratum
npm install
npm test
```

## License

MIT OR Apache-2.0

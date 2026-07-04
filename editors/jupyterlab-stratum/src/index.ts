// JupyterLab 4 extension: register a CodeMirror 6 language for the Stratum
// reflective ρ-calculus surface syntax so `.strat` files and `text/x-stratum`
// cells (what the kernel advertises via `language_info.mimetype`) are live-
// highlighted in the editor.

import {
  JupyterFrontEnd,
  JupyterFrontEndPlugin
} from '@jupyterlab/application';
import { IEditorLanguageRegistry } from '@jupyterlab/codemirror';

import { stratum } from './stratum';

/**
 * The extension registers Stratum with JupyterLab's CodeMirror 6 language
 * registry, keyed off the `text/x-stratum` mimetype and the `.strat` extension.
 * The kernel's `kernel_info_reply` sets `language_info.mimetype = "text/x-stratum"`,
 * so notebook cells for the Stratum kernel pick up this language automatically.
 */
const plugin: JupyterFrontEndPlugin<void> = {
  id: 'jupyterlab-stratum:plugin',
  description:
    'CodeMirror 6 syntax highlighting for the Stratum ρ-calculus surface syntax.',
  autoStart: true,
  requires: [IEditorLanguageRegistry],
  activate: (_app: JupyterFrontEnd, languages: IEditorLanguageRegistry): void => {
    languages.addLanguage({
      name: 'stratum',
      alias: ['strat'],
      mime: 'text/x-stratum',
      extensions: ['strat'],
      load: async () => stratum()
    });
  }
};

export default plugin;

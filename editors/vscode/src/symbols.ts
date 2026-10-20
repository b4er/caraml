import * as vscode from 'vscode';

// a symbol is replaced only when it is a whole symbol run (`-->` and `<->` are left
// alone unless they are in the table), never in strings, chars or comments, and never under
// the cursor, so it can be edited as typed.

const symbolChar = /[!#$%&*+\-/:<=>?@^|~←-⋿]/;
const wordChar = /[\p{L}\p{N}_']/u;

export interface Match {
  start: number;
  end: number;
  glyph: string;
}

export function scan(text: string, symbols: ReadonlyMap<string, string>): Match[] {
  const out: Match[] = [];
  let i = 0;
  while (i < text.length) {
    const c = text[i];
    if (c === '"') {
      const j = text.indexOf('"', i + 1);
      i = j < 0 ? text.length : j + 1;
    } else if (c === '{' && text[i + 1] === '-') {
      let depth = 1;
      i += 2;
      while (i < text.length && depth > 0) {
        if (text.startsWith('{-', i)) {
          depth++;
          i += 2;
        } else if (text.startsWith('-}', i)) {
          depth--;
          i += 2;
        } else {
          i++;
        }
      }
    } else if (c === "'") {
      const cp = text.codePointAt(i + 1);
      const w = cp !== undefined && cp > 0xffff ? 2 : 1;
      i += cp !== undefined && cp !== 0x27 && text[i + 1 + w] === "'" ? w + 2 : 1;
    } else if (c === '\\') {
      // a token on its own (e.g. `\` for `λ`)
      if (symbols.has(c)) {
        out.push({ start: i, end: i + 1, glyph: symbols.get(c)! });
      }
      i++;
    } else if (wordChar.test(c)) {
      while (i < text.length && wordChar.test(text[i])) {
        i++;
      }
    } else if (symbolChar.test(c)) {
      const start = i;
      while (i < text.length && symbolChar.test(text[i])) {
        i++;
      }
      const run = text.slice(start, i);
      if (run.length >= 2 && /^-+$/.test(run)) {
        const eol = text.indexOf('\n', i);
        i = eol < 0 ? text.length : eol;
      } else if (symbols.has(run)) {
        out.push({ start, end: i, glyph: symbols.get(run)! });
      }
    } else {
      i++;
    }
  }
  return out;
}

const hidden = vscode.window.createTextEditorDecorationType({
  textDecoration: 'none; display: none',
});

function config() {
  return vscode.workspace.getConfiguration('caraml.displaySymbols');
}

function table(): ReadonlyMap<string, string> {
  return new Map(Object.entries(config().get<Record<string, string>>('symbols', {})));
}

export function registerSymbols(context: vscode.ExtensionContext): void {
  let enabled = config().get<boolean>('enabled', false);
  let symbols = table();
  const cache = new WeakMap<vscode.TextDocument, { version: number; matches: Match[] }>();

  const status = vscode.window.createStatusBarItem(
    'caraml.displaySymbols',
    vscode.StatusBarAlignment.Right,
    100.1, // with language mode
  );
  status.name = 'CaraML Symbol Display';
  status.command = 'caraml.toggleDisplaySymbols';

  function matches(doc: vscode.TextDocument): Match[] {
    const hit = cache.get(doc);
    if (hit?.version === doc.version) {
      return hit.matches;
    }
    const ms = scan(doc.getText(), symbols);
    cache.set(doc, { version: doc.version, matches: ms });
    return ms;
  }

  function render(editor: vscode.TextEditor): void {
    const doc = editor.document;
    if (doc.languageId !== 'caraml') {
      return;
    }
    if (!enabled) {
      editor.setDecorations(hidden, []);
      return;
    }
    const cursors = editor.selections.map((s) => doc.offsetAt(s.active));
    const decorations = matches(doc)
      .filter((m) => !cursors.some((c) => m.start <= c && c <= m.end))
      .map((m) => ({
        range: new vscode.Range(doc.positionAt(m.start), doc.positionAt(m.end)),
        renderOptions: { before: { contentText: m.glyph } },
      }));
    editor.setDecorations(hidden, decorations);
  }

  function renderAll(): void {
    vscode.window.visibleTextEditors.forEach(render);
  }

  function updateStatus(): void {
    if (vscode.window.activeTextEditor?.document.languageId !== 'caraml') {
      status.hide();
      return;
    }
    status.text = enabled ? 'utf-8' : 'ascii';
    status.tooltip = enabled
      ? 'Symbols such as -> are displayed as →, the file keeps ASCII (CaraML)'
      : 'Symbols are displayed as typed (CaraML)';
    status.show();
  }

  async function toggle(): Promise<void> {
    const i = config().inspect<boolean>('enabled');
    const target =
      i?.workspaceFolderValue !== undefined
        ? vscode.ConfigurationTarget.WorkspaceFolder
        : i?.workspaceValue !== undefined
          ? vscode.ConfigurationTarget.Workspace
          : vscode.ConfigurationTarget.Global;
    await config().update('enabled', !enabled, target);
  }

  context.subscriptions.push(
    hidden,
    status,
    vscode.commands.registerCommand('caraml.toggleDisplaySymbols', toggle),
    vscode.workspace.onDidChangeConfiguration((e) => {
      if (e.affectsConfiguration('caraml.displaySymbols')) {
        enabled = config().get<boolean>('enabled', false);
        symbols = table();
        vscode.workspace.textDocuments.forEach((d) => cache.delete(d));
        renderAll();
        updateStatus();
      }
    }),
    vscode.window.onDidChangeVisibleTextEditors(renderAll),
    vscode.window.onDidChangeActiveTextEditor(updateStatus),
    vscode.window.onDidChangeTextEditorSelection((e) => render(e.textEditor)),
    vscode.workspace.onDidChangeTextDocument((e) => {
      vscode.window.visibleTextEditors.filter((ed) => ed.document === e.document).forEach(render);
    }),
  );

  renderAll();
  updateStatus();
}

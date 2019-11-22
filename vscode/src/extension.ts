// The module 'vscode' contains the VS Code extensibility API
// Import the module and reference it with the alias vscode in your code below
import * as child_process from 'child_process';

import * as vscode from 'vscode';

type Range = {
  start: number,
  end: number,
};

type HighlightedRange = {
  range: Range,
  kind: string,
};

type Response = {
  highlighting: HighlightedRange[],
};

// TODO: configure
let binaryPath =
    '/Users/knrafto/code/prover/.stack-work/dist/x86_64-osx/Cabal-2.4.0.1/build/prover/prover';

let decorationTypes: Map<string, vscode.TextEditorDecorationType> = new Map([
  ['local', vscode.window.createTextEditorDecorationType({color: '#FFFFFF'})],
  ['defined', vscode.window.createTextEditorDecorationType({color: '#4EC9B0'})],
  ['assumed', vscode.window.createTextEditorDecorationType({color: '#4EC9B0'})],
  ['unbound', vscode.window.createTextEditorDecorationType({color: '#FFFFFF'})],
  [
    'reserved_word',
    vscode.window.createTextEditorDecorationType({color: '#FF0000'})
  ],
  ['symbol', vscode.window.createTextEditorDecorationType({color: '#00FF00'})],
]);

let cache: Map<string, Response> = new Map();

function convertRange(
    document: vscode.TextDocument, range: Range): vscode.Range {
  return new vscode.Range(
      document.positionAt(range.start), document.positionAt(range.end));
}

// Run a command to completion, reporting its output and exit code.
function runCommand(
    command: string, args: string[],
    callback: (stdout: string, stderr: string) => void) {
  console.log('Running command:', command, args.join(' '));
  var child = child_process.spawn(command, args);

  var stdout = '';
  var stderr = '';

  child.stdout.setEncoding('utf8');
  child.stdout.on('data', (data) => {
    stdout += data.toString();
  });

  child.stderr.setEncoding('utf8');
  child.stderr.on('data', (data) => {
    stderr += data.toString();
  });

  child.on('close', () => {
    callback(stdout, stderr);
  });
}

function onChange(path: string) {
  if (!path.endsWith('.pf')) {
    return;
  }

  runCommand(binaryPath, ['--json', path], (stdout, stderr) => {
    if (stderr.length !== 0) {
      console.log('Error:\n' + stderr);
    }

    var resp: Response = {
      highlighting: [],
    };
    try {
      resp = JSON.parse(stdout);
    } catch (e) {
      console.log('Error decoding JSON:', e);
    }

    cache.set(path, resp);
    updateEditors();
  });
}

function updateEditors() {
  for (let textEditor of vscode.window.visibleTextEditors) {
    let path = textEditor.document.uri.path;
    let resp = cache.get(path);
    if (resp === undefined) {
      continue;
    }

    let decorations: Map<string, vscode.Range[]> = new Map();
    for (let highlightedRange of resp.highlighting) {
      let range = convertRange(textEditor.document, highlightedRange.range);
      let ranges = decorations.get(highlightedRange.kind);
      if (ranges !== undefined) {
        ranges.push(range);
      } else {
        decorations.set(highlightedRange.kind, [range]);
      }
    }

    for (let [kind, decorationType] of decorationTypes) {
      textEditor.setDecorations(decorationType, decorations.get(kind) || []);
    }
  }
}

export function activate(context: vscode.ExtensionContext) {
  console.log('Extension "prover" is now active!');

  for (let textEditor of vscode.window.visibleTextEditors) {
    onChange(textEditor.document.uri.path);
  }

  context.subscriptions.push(vscode.workspace.onDidSaveTextDocument(
      (document) => onChange(document.uri.path)));

  context.subscriptions.push(
      vscode.window.onDidChangeVisibleTextEditors((_) => updateEditors()));
}

// this method is called when your extension is deactivated
export function deactivate() {}

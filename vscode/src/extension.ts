// The module 'vscode' contains the VS Code extensibility API
// Import the module and reference it with the alias vscode in your code below
import * as child_process from 'child_process';

import * as vscode from 'vscode';

// TODO: configure
let binaryPath =
    '/Users/knrafto/code/prover/.stack-work/dist/x86_64-osx/Cabal-2.4.0.1/build/prover/prover';

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

type Range = {
  start: number,
  end: number,
};

type Occurrence = {
  introduction?: Range, usage: Range, kind: string,
};

type Response = {
  occurrences: Occurrence[],
};

// this method is called when your extension is activated
// your extension is activated the very first time the command is executed
export function activate(context: vscode.ExtensionContext) {
  console.log('Extension "prover" is now active!');

  let decorationTypes: Record<string, vscode.TextEditorDecorationType> = {
    local: vscode.window.createTextEditorDecorationType({color: '#ffffff'}),
    define: vscode.window.createTextEditorDecorationType({color: '#0000ff'}),
    assume: vscode.window.createTextEditorDecorationType({color: '#00ff00'}),
    unbound: vscode.window.createTextEditorDecorationType({color: '#ff0000'}),
  };

  let disposable = vscode.workspace.onDidSaveTextDocument((document) => {
    let path = document.uri.path;
    if (!path.endsWith('.pf')) {
      return;
    }

    runCommand(binaryPath, ['--json', document.uri.path], (stdout, stderr) => {
      if (stderr.length !== 0) {
        console.log('Error:\n' + stderr);
      }

      var resp: Response = {
        occurrences: [],
      };
      try {
        resp = JSON.parse(stdout);
      } catch (e) {
        console.log('Error decoding JSON:', e);
      }

      // Collect decorations
      let decorations: Record<string, vscode.Range[]> = {};
      for (let occurrence of resp.occurrences) {
        let range = new vscode.Range(
            document.positionAt(occurrence.usage.start),
            document.positionAt(occurrence.usage.end));
        if (occurrence.kind in decorations) {
          decorations[occurrence.kind].push(range);
        } else {
          decorations[occurrence.kind] = [range];
        }
      }
      // Set decorations
      for (let textEditor of vscode.window.visibleTextEditors) {
        if (textEditor.document.uri === document.uri) {
          for (let kind in decorationTypes) {
            let decorationType = decorationTypes[kind];
            if (kind in decorations) {
              textEditor.setDecorations(decorationType, decorations[kind]);
            } else {
              textEditor.setDecorations(decorationType, []);
            }
          }
        }
      }
    });
  });
  context.subscriptions.push(disposable);
}

// this method is called when your extension is deactivated
export function deactivate() {}

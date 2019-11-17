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

// this method is called when your extension is activated
// your extension is activated the very first time the command is executed
export function activate(context: vscode.ExtensionContext) {
  console.log('Extension "prover" is now active!');

  let disposable = vscode.workspace.onDidSaveTextDocument((document) => {
    let path = document.uri.path;
    console.log('Document saved:', path);

    if (!path.endsWith('.pf')) {
      return;
    }

    runCommand(binaryPath, ['--json', document.uri.path], (stdout, stderr) => {
      if (stdout.length !== 0) {
        console.log('Output:\n' + stdout);
      }
      if (stderr.length !== 0) {
        console.log('Error:\n' + stderr);
      }

      var json;
      try {
        json = JSON.parse(stdout);
      } catch (e) {
        console.log('Error decoding JSON:', e);
        return;
      }
    });
  });
  context.subscriptions.push(disposable);
}

// this method is called when your extension is deactivated
export function deactivate() {}

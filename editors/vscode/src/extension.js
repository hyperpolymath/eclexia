// SPDX-License-Identifier: PMPL-1.0-or-later
// SPDX-FileCopyrightText: 2025 Jonathan D.A. Jewell

// VSCode extension for Eclexia language support.
// Note: Using JavaScript (not TypeScript) per hyperpolymath policy.

const vscode = require('vscode');
const { LanguageClient, TransportKind } = require('vscode-languageclient/node');

let client;

/**
 * Activate the extension.
 */
function activate(context) {
    console.log('Eclexia extension is now active');

    // Get configuration
    const config = vscode.workspace.getConfiguration('eclexia');
    const lspPath = config.get('lsp.path', 'eclexia');
    const trace = config.get('lsp.trace', 'off');

    // Create server options
    const serverOptions = {
        command: lspPath,
        args: ['lsp'],
        transport: TransportKind.stdio,
    };

    // Client options
    const clientOptions = {
        documentSelector: [
            { scheme: 'file', language: 'eclexia' }
        ],
        synchronize: {
            fileEvents: vscode.workspace.createFileSystemWatcher('**/*.ecl')
        }
    };

    // Create the language client
    client = new LanguageClient(
        'eclexia',
        'Eclexia Language Server',
        serverOptions,
        clientOptions
    );

    // Set trace level
    if (trace !== 'off') {
        client.setTrace(trace === 'verbose' ? 2 : 1);
    }

    // Start the client
    client.start().then(() => {
        console.log('Eclexia LSP client started');
    }).catch((error) => {
        console.error('Failed to start Eclexia LSP client:', error);
        vscode.window.showErrorMessage(
            `Failed to start Eclexia LSP server. Make sure 'eclexia' is in your PATH.\nError: ${error.message}`
        );
    });

    // Register commands
    const commandDisposables = [
        vscode.commands.registerCommand('eclexia.restartServer', async () => {
            if (client) {
                await client.stop();
                await client.start();
                vscode.window.showInformationMessage('Eclexia LSP server restarted');
            }
        }),
    ];

    context.subscriptions.push(...commandDisposables);
}

/**
 * Deactivate the extension.
 */
function deactivate() {
    if (!client) {
        return undefined;
    }
    return client.stop();
}

module.exports = {
    activate,
    deactivate
};

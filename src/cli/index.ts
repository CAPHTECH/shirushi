#!/usr/bin/env node
import { pathToFileURL } from 'node:url';

export function run(): void {
  process.stdout.write('Shirushi CLI is not implemented yet.\n');
}

const executedDirectly = pathToFileURL(process.argv[1] ?? '').href === import.meta.url;

if (executedDirectly) {
  run();
}

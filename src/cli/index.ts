import { pathToFileURL } from 'node:url';
import { logger } from '../utils/logger.js';

export function run(): void {
  // Telemetry example
  logger.debug('system.startup', 'Shirushi CLI initializing');
  
  process.stdout.write('Shirushi CLI is not implemented yet.\n');
}

const executedDirectly = pathToFileURL(process.argv[1] ?? '').href === import.meta.url;

if (executedDirectly) {
  run();
}

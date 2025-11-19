import { readFile } from 'node:fs/promises';
import path from 'node:path';

import yaml from 'js-yaml';
import { ZodError } from 'zod';

import { ConfigSchema } from './schema.js';

import type { ShirushiConfig } from './schema.js';

export interface LoadConfigOptions {
  cwd?: string;
  configPath?: string;
}

export interface LoadedConfig {
  path: string;
  config: ShirushiConfig;
  raw: unknown;
}

export class ConfigLoaderError extends Error {
  constructor(message: string, options?: { cause?: unknown }) {
    super(message);
    this.name = 'ConfigLoaderError';
    if (options?.cause) {
      // @ts-expect-error cause is available in recent Node versions
      this.cause = options.cause;
    }
  }
}

export async function loadConfig(options: LoadConfigOptions = {}): Promise<LoadedConfig> {
  const cwd = options.cwd ?? process.cwd();
  const inputPath = options.configPath ?? '.shirushi.yml';
  const resolvedPath = path.isAbsolute(inputPath) ? inputPath : path.join(cwd, inputPath);

  let fileContents: string;
  try {
    fileContents = await readFile(resolvedPath, 'utf8');
  } catch (error) {
    throw new ConfigLoaderError(`Failed to read config file at ${resolvedPath}`, { cause: error });
  }

  let raw: unknown;
  try {
    raw = yaml.load(fileContents);
  } catch (error) {
    throw new ConfigLoaderError(`Config file at ${resolvedPath} is not valid YAML`, { cause: error });
  }

  if (raw === null || typeof raw !== 'object' || Array.isArray(raw)) {
    throw new ConfigLoaderError('Config file must contain a YAML object at the root');
  }

  try {
    const config = ConfigSchema.parse(raw);
    return {
      path: resolvedPath,
      config,
      raw,
    };
  } catch (error) {
    if (error instanceof ZodError) {
      const formatted = error.issues.map((issue) => `${issue.path.join('.') || 'root'}: ${issue.message}`).join('\n');
      throw new ConfigLoaderError(`Invalid configuration:\n${formatted}`, { cause: error });
    }
    throw new ConfigLoaderError('Unknown error while validating configuration', { cause: error });
  }
}

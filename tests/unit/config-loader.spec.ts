import path from 'node:path';
import { describe, expect, it } from 'vitest';
import { loadConfig, ConfigLoaderError } from '@/config/loader.js';

const fixturesRoot = path.resolve('tests/fixtures/doc-discovery');

describe('config/loader', () => {
  it('loads and validates a well-formed configuration', async () => {
    const { config, path: loadedPath } = await loadConfig({
      cwd: path.join(fixturesRoot, 'basic'),
    });

    expect(loadedPath.endsWith('.shirushi.yml')).toBe(true);
    expect(config.doc_globs).toEqual(['docs/**/*.md', 'docs/**/*.yaml']);
    expect(config.dimensions.COMP.values).toEqual(['SHI']);
    expect(config.index_file).toBe('docs/doc_index.yaml');
  });

  it('throws descriptive error when schema validation fails', async () => {
    await expect(
      loadConfig({ cwd: path.join(fixturesRoot, 'invalid') })
    ).rejects.toThrowError(ConfigLoaderError);
  });

  it('throws descriptive error when file is missing', async () => {
    await expect(
      loadConfig({ cwd: fixturesRoot, configPath: 'missing.yml' })
    ).rejects.toThrowError('Failed to read config file');
  });
});

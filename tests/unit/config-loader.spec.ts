import path from 'node:path';
import { describe, expect, it } from 'vitest';
import { loadConfig, ConfigLoaderError } from '@/config/loader.js';

const docFixturesRoot = path.resolve('tests/fixtures/doc-discovery');
const configFixturesRoot = path.resolve('tests/fixtures/config');

describe('config/loader', () => {
  it('loads and validates a well-formed configuration', async () => {
    const { config, path: loadedPath } = await loadConfig({
      cwd: path.join(docFixturesRoot, 'basic'),
    });

    expect(loadedPath.endsWith('.shirushi.yml')).toBe(true);
    expect(config.doc_globs).toEqual(['docs/**/*.md', 'docs/**/*.yaml']);
    expect(config.dimensions.COMP.values).toEqual(['SHI']);
    expect(config.index_file).toBe('docs/doc_index.yaml');
  });

  it('throws descriptive error when schema validation fails', async () => {
    await expect(
      loadConfig({ cwd: path.join(docFixturesRoot, 'invalid') })
    ).rejects.toThrowError(ConfigLoaderError);
  });

  it('throws descriptive error when file is missing', async () => {
    await expect(
      loadConfig({ cwd: docFixturesRoot, configPath: 'missing.yml' })
    ).rejects.toThrowError('Failed to read config file');
  });

  it('throws when config YAML cannot be parsed', async () => {
    await expect(
      loadConfig({ cwd: path.join(configFixturesRoot, 'invalid-yaml') })
    ).rejects.toThrowError('not valid YAML');
  });

  it('throws when config root is not an object', async () => {
    await expect(
      loadConfig({ cwd: path.join(configFixturesRoot, 'non-object') })
    ).rejects.toThrowError('must contain a YAML object');
  });

  it('validates undefined placeholders in id_format', async () => {
    await expect(
      loadConfig({ cwd: path.join(configFixturesRoot, 'undefined-placeholders') })
    ).rejects.toThrowError(/id_format references undefined dimensions/);
  });

  it('rejects reserved doc_type dimension name', async () => {
    await expect(
      loadConfig({ cwd: path.join(configFixturesRoot, 'reserved-doc-type') })
    ).rejects.toThrowError(/dimension name doc_type is reserved/);
  });
});

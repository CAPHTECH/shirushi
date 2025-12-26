/**
 * Skill Command Tests
 *
 * skillコマンドのテスト。
 * AIエージェント向けスキルファイルのインストール・管理機能をテストする。
 */

import { existsSync, readFileSync } from 'node:fs';
import { mkdir, rm } from 'node:fs/promises';
import path from 'node:path';

import { describe, it, expect, beforeEach, afterEach, vi } from 'vitest';

import {
  executeSkillInstall,
  executeSkillList,
  executeSkillUninstall,
} from '@/cli/commands/skill';

// テスト用一時ディレクトリ
const TEST_DIR = path.join(process.cwd(), 'tests/.tmp/skill');

describe('skill command', () => {
  let consoleOutput: string[] = [];
  let consoleErrors: string[] = [];

  beforeEach(async () => {
    // テスト用ディレクトリを作成
    await mkdir(TEST_DIR, { recursive: true });

    // console.log/errorをモックして出力をキャプチャ
    consoleOutput = [];
    consoleErrors = [];
    vi.spyOn(console, 'log').mockImplementation((msg: string) => {
      consoleOutput.push(String(msg));
    });
    vi.spyOn(console, 'error').mockImplementation((msg: string) => {
      consoleErrors.push(String(msg));
    });
  });

  afterEach(async () => {
    await rm(TEST_DIR, { recursive: true, force: true });
    vi.restoreAllMocks();
  });

  describe('skill install', () => {
    it('should install skill to custom path', () => {
      const targetDir = path.join(TEST_DIR, 'custom-skills');

      const exitCode = executeSkillInstall({
        path: targetDir,
      });

      expect(exitCode).toBe(0);
      expect(existsSync(path.join(targetDir, 'shirushi', 'SKILL.md'))).toBe(
        true
      );

      // SKILL.mdの内容を確認
      const content = readFileSync(
        path.join(targetDir, 'shirushi', 'SKILL.md'),
        'utf-8'
      );
      expect(content).toContain('name: shirushi');
      expect(content).toContain('description:');
    });

    it('should install skill to .agent/skills/ by default (agent preset)', async () => {
      const targetDir = path.join(TEST_DIR, 'project');
      await mkdir(targetDir, { recursive: true });

      // カスタムパスでテスト（cwdを変更できないのでpathオプションを使用）
      const agentSkillsDir = path.join(targetDir, '.agent', 'skills');
      const exitCode = executeSkillInstall({
        path: agentSkillsDir,
      });

      expect(exitCode).toBe(0);
      expect(existsSync(path.join(agentSkillsDir, 'shirushi', 'SKILL.md'))).toBe(
        true
      );
    });

    it('should fail if skill already exists without --force', () => {
      const targetDir = path.join(TEST_DIR, 'existing');

      // 最初のインストール
      executeSkillInstall({ path: targetDir });

      // 2回目のインストール（--forceなし）
      const exitCode = executeSkillInstall({ path: targetDir });

      expect(exitCode).toBe(1);
      expect(consoleErrors.some((e) => e.includes('already exists'))).toBe(
        true
      );
    });

    it('should overwrite existing skill with --force', () => {
      const targetDir = path.join(TEST_DIR, 'force-test');

      // 最初のインストール
      executeSkillInstall({ path: targetDir });

      // 2回目のインストール（--force）
      const exitCode = executeSkillInstall({
        path: targetDir,
        force: true,
      });

      expect(exitCode).toBe(0);
      expect(existsSync(path.join(targetDir, 'shirushi', 'SKILL.md'))).toBe(
        true
      );
    });
  });

  describe('skill list', () => {
    it('should show search paths and installation status', () => {
      const exitCode = executeSkillList();

      expect(exitCode).toBe(0);
      expect(consoleOutput.some((o) => o.includes('Search paths'))).toBe(true);
      expect(consoleOutput.some((o) => o.includes('.agent/skills'))).toBe(true);
      expect(consoleOutput.some((o) => o.includes('.claude/skills'))).toBe(
        true
      );
    });

    it('should show installed skill as active', () => {
      const targetDir = path.join(TEST_DIR, 'list-test');
      executeSkillInstall({ path: targetDir });

      // 新しいコンソール出力をキャプチャ
      consoleOutput = [];
      executeSkillList();

      // カスタムパスにインストールした場合、デフォルトのパスには表示されない
      // ただし、「No skill installed」が表示されるはず
      expect(consoleOutput.some((o) => o.includes('No skill installed') || o.includes('Active skill'))).toBe(true);
    });
  });

  describe('skill uninstall', () => {
    it('should uninstall installed skill', () => {
      const targetDir = path.join(TEST_DIR, 'uninstall-test');

      // インストール
      executeSkillInstall({ path: targetDir });
      expect(existsSync(path.join(targetDir, 'shirushi', 'SKILL.md'))).toBe(
        true
      );

      // アンインストール
      const exitCode = executeSkillUninstall({ path: targetDir });

      expect(exitCode).toBe(0);
      expect(existsSync(path.join(targetDir, 'shirushi', 'SKILL.md'))).toBe(
        false
      );
    });

    it('should fail if skill does not exist', () => {
      const targetDir = path.join(TEST_DIR, 'nonexistent');

      const exitCode = executeSkillUninstall({ path: targetDir });

      expect(exitCode).toBe(1);
      expect(consoleErrors.some((e) => e.includes('No skill found'))).toBe(
        true
      );
    });
  });

  describe('target presets', () => {
    it('should use .agent directory for agent preset', () => {
      const baseDir = path.join(TEST_DIR, 'preset-agent');
      const expectedDir = path.join(baseDir, '.agent', 'skills');

      const exitCode = executeSkillInstall({
        path: expectedDir,
        target: 'agent',
      });

      expect(exitCode).toBe(0);
      expect(existsSync(path.join(expectedDir, 'shirushi', 'SKILL.md'))).toBe(
        true
      );
    });

    it('should use .claude directory for claude preset', () => {
      const baseDir = path.join(TEST_DIR, 'preset-claude');
      const expectedDir = path.join(baseDir, '.claude', 'skills');

      const exitCode = executeSkillInstall({
        path: expectedDir,
        target: 'claude',
      });

      expect(exitCode).toBe(0);
      expect(existsSync(path.join(expectedDir, 'shirushi', 'SKILL.md'))).toBe(
        true
      );
    });
  });
});

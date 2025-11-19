# Contributing to Shirushi

Thank you for your interest in contributing to Shirushi! This document provides guidelines and instructions for contributing.

## Table of Contents

1. [Code of Conduct](#code-of-conduct)
2. [Getting Started](#getting-started)
3. [Development Workflow](#development-workflow)
4. [Coding Standards](#coding-standards)
5. [Testing Requirements](#testing-requirements)
6. [Documentation](#documentation)
7. [Submitting Changes](#submitting-changes)
8. [Review Process](#review-process)

---

## Code of Conduct

### Our Pledge

We are committed to providing a welcoming and inspiring community for all. Please be respectful and constructive in all interactions.

### Expected Behavior

- Be respectful of differing viewpoints
- Accept constructive criticism gracefully
- Focus on what is best for the community
- Show empathy towards other community members

### Unacceptable Behavior

- Harassment, discrimination, or offensive comments
- Trolling or insulting/derogatory comments
- Publishing others' private information
- Other conduct which could reasonably be considered inappropriate

---

## Getting Started

### Prerequisites

- Node.js 18 or higher
- pnpm 8.x (recommended) or npm
- Git
- A GitHub account

### Fork and Clone

```bash
# Fork the repository on GitHub, then:
git clone https://github.com/YOUR-USERNAME/shirushi.git
cd shirushi

# Add upstream remote
git remote add upstream https://github.com/your-org/shirushi.git
```

### Install Dependencies

```bash
pnpm install
```

### Build and Test

```bash
# Build
pnpm build

# Run tests
pnpm test

# Run linter
pnpm lint

# Type check
pnpm typecheck
```

---

## Development Workflow

### 1. Create a Branch

```bash
# Update your fork
git fetch upstream
git checkout main
git merge upstream/main

# Create feature branch
git checkout -b feature/your-feature-name

# Or bug fix branch
git checkout -b fix/your-bug-fix
```

### 2. Make Changes

- Write code following our [coding standards](#coding-standards)
- Add tests for new functionality
- Update documentation as needed
- Ensure all tests pass

### 3. Commit Changes

Use conventional commit messages:

```bash
git commit -m "feat: add new dimension type for regions"
git commit -m "fix: correct checksum calculation for edge case"
git commit -m "docs: update user guide with examples"
git commit -m "test: add property-based tests for serial handler"
```

**Commit Types**:
- `feat`: New feature
- `fix`: Bug fix
- `docs`: Documentation only
- `style`: Code style changes (formatting, etc.)
- `refactor`: Code refactoring
- `test`: Adding or updating tests
- `chore`: Maintenance tasks
- `perf`: Performance improvements

### 4. Push Changes

```bash
git push origin feature/your-feature-name
```

### 5. Create Pull Request

Go to GitHub and create a pull request from your branch to `main`.

---

## Coding Standards

### TypeScript

- Use TypeScript strict mode
- Explicit return types for public functions
- Prefer `type` over `interface` for unions
- Use discriminated unions where appropriate

```typescript
// Good
export function validateDocument(
  doc: Document,
  config: ShirushiConfig
): Promise<ValidationResult[]> {
  // ...
}

// Avoid
export function validateDocument(doc, config) {
  // ...
}
```

### Naming Conventions

- **Files**: `kebab-case.ts`
- **Classes**: `PascalCase`
- **Functions**: `camelCase`
- **Constants**: `UPPER_SNAKE_CASE`
- **Types/Interfaces**: `PascalCase`

### Code Organization

- One exported entity per file (with exceptions for closely related types)
- Group imports: builtin → external → internal → types
- Use path aliases (`@/`) for internal imports

```typescript
// imports
import { readFile } from 'fs/promises';  // builtin
import { z } from 'zod';                 // external
import { loadConfig } from '@/config';   // internal
import type { Document } from '@/types'; // types
```

### Error Handling

- Use custom error classes
- Provide descriptive error messages
- Include context in errors

```typescript
throw new ValidationError(
  'INVALID_ID_FORMAT',
  `ID "${docId}" does not match format "${format}"`,
  { file: doc.path, line: doc.line }
);
```

### Comments

- Use JSDoc for public APIs
- Explain "why", not "what"
- Keep comments up-to-date

```typescript
/**
 * Validates a document's doc_id against the configuration.
 *
 * @param document - Document to validate
 * @param config - Shirushi configuration
 * @returns Array of validation results (empty if valid)
 *
 * @example
 * ```typescript
 * const results = await validateDocument(doc, config);
 * if (results.some(r => !r.valid)) {
 *   console.error('Validation failed');
 * }
 * ```
 */
export async function validateDocument(
  document: Document,
  config: ShirushiConfig
): Promise<ValidationResult[]> {
  // ...
}
```

---

## Testing Requirements

### Coverage Requirements

- **Minimum coverage**: 80%
- **New code**: Must have tests
- **Bug fixes**: Must include regression test

### Test Types

**Unit Tests** - Test individual functions/classes:

```typescript
// tests/unit/parsers/template.test.ts
describe('parseTemplate', () => {
  it('should extract placeholders', () => {
    const result = parseTemplate('{A}-{B}-{C}');
    expect(result).toEqual(['A', 'B', 'C']);
  });
});
```

**Integration Tests** - Test multiple modules together:

```typescript
// tests/integration/validation.test.ts
describe('Document Validation', () => {
  it('should validate complete document', async () => {
    const config = await loadConfig('fixtures/basic/.shirushi.yml');
    const doc = await parseDocument('fixtures/basic/docs/test.md');
    const results = await validateDocument(doc, config);
    expect(results.every(r => r.valid)).toBe(true);
  });
});
```

**Property-Based Tests** - Test properties with random inputs:

```typescript
// tests/unit/checksum.test.ts
import fc from 'fast-check';

it('should always return uppercase letter', () => {
  fc.assert(
    fc.property(fc.string({ minLength: 1 }), (input) => {
      const result = mod26AZ(input);
      return /^[A-Z]$/.test(result);
    })
  );
});
```

### Running Tests

```bash
# All tests
pnpm test

# Watch mode
pnpm test --watch

# Coverage
pnpm test:coverage

# Specific file
pnpm test -- template.test.ts
```

---

## Documentation

### What to Document

- **New features**: User guide + API docs
- **Breaking changes**: Migration guide
- **Design decisions**: ADR (Architecture Decision Record)

### Documentation Types

**User Guide** (`docs/user-guide.md`):
- End-user facing documentation
- How to use features
- Examples and tutorials

**Developer Guide** (`docs/developer-guide.md`):
- Contributing guidelines
- Architecture overview
- How to extend Shirushi

**ADRs** (`docs/adr/`):
- Significant architectural decisions
- Context, decision, and consequences
- Use template: `docs/adr/template.md`

**API Documentation**:
- JSDoc comments in code
- Generated with TypeDoc

### Writing Guidelines

- Use clear, concise language
- Provide examples
- Keep documentation up-to-date with code
- Use British or American English consistently (we use American English)

---

## Submitting Changes

### Pull Request Checklist

Before submitting, ensure:

- [ ] Code follows style guidelines
- [ ] All tests pass (`pnpm test`)
- [ ] Coverage meets requirements (`pnpm test:coverage`)
- [ ] Linter passes (`pnpm lint`)
- [ ] Type checking passes (`pnpm typecheck`)
- [ ] Documentation is updated
- [ ] Commit messages follow conventions
- [ ] Branch is up-to-date with `main`

### Pull Request Template

```markdown
## Description

Brief description of changes.

## Related Issue

Closes #123

## Type of Change

- [ ] Bug fix
- [ ] New feature
- [ ] Breaking change
- [ ] Documentation update

## Testing

Describe testing performed.

## Checklist

- [ ] Tests added/updated
- [ ] Documentation updated
- [ ] All tests passing
- [ ] Linter passing
```

---

## Review Process

### What Reviewers Look For

1. **Correctness**: Does it work as intended?
2. **Tests**: Are there adequate tests?
3. **Code Quality**: Is it maintainable?
4. **Documentation**: Is it documented?
5. **Performance**: Are there performance concerns?
6. **Security**: Are there security implications?

### Review Timeline

- Initial review: Within 2-3 business days
- Follow-up reviews: Within 1-2 business days
- Merging: After approval from at least one maintainer

### Addressing Feedback

- Respond to all comments
- Make requested changes in new commits
- Mark resolved conversations
- Request re-review when ready

---

## Additional Resources

- [User Guide](docs/user-guide.md)
- [Developer Guide](docs/developer-guide.md)
- [Architecture Decision Records](docs/adr/)
- [Examples](examples/)

## Getting Help

- **Questions**: Open a [GitHub Discussion](https://github.com/your-org/shirushi/discussions)
- **Bugs**: Open an [Issue](https://github.com/your-org/shirushi/issues)
- **Chat**: Join our [Discord/Slack] (if applicable)

---

Thank you for contributing to Shirushi! 🎉

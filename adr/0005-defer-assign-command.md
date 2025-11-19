# ADR-0005: Defer assign Command to v0.2

**Status**: Accepted

**Date**: 2025-01-19

**Deciders**: Architecture Team, Product Team

**Tags**: scope, prioritization, mvp

---

## Context

The Shirushi specification describes three main CLI commands:

1. **`shirushi lint`**: Validate document IDs (core validation)
2. **`shirushi scan`**: List all documents with IDs
3. **`shirushi assign`**: Automatically generate and assign IDs to documents (marked as "将来実装" - future implementation)

The `assign` command would:
- Scan for documents without `doc_id`
- Generate valid IDs based on configuration
- Write IDs back to document files
- Update the index file

For v0.1 (MVP), we need to decide: implement all three commands, or defer `assign`?

## Decision

**Defer `assign` command implementation to v0.2.**

For v0.1, we will:
- ✅ Implement `lint` command (full validation)
- ✅ Implement `scan` command (document listing)
- ✅ Implement core ID generation logic (as internal module)
- ❌ Do not expose `assign` command in CLI

Users will manually create document IDs for v0.1, then use Shirushi to validate them.

## Rationale

### Why Defer?

1. **Validation is the Critical Path**
   - The primary value proposition is **preventing ID corruption in CI**
   - Validation must be rock-solid before we automate generation
   - Users can manually create IDs and immediately benefit from validation

2. **Complexity of `assign`**
   - Requires file writing (risky operation)
   - Needs interactive prompts for missing metadata
   - Requires transactional semantics (rollback on error)
   - Needs thorough testing of file modification edge cases

3. **Faster Time to Value**
   - v0.1 timeline: ~4 weeks
   - Adding `assign` would push to 5-6 weeks
   - Users can get validation benefits immediately

4. **User Feedback**
   - Let users validate existing manually-created IDs first
   - Gather feedback on ID format and dimension design
   - Learn about common use cases before automating

5. **Specification Alignment**
   - Spec explicitly marks `assign` as "将来実装" (future implementation)
   - Validates that deferral is acceptable

### What We Still Build

To prepare for v0.2, we will:

```typescript
// src/core/generator.ts - ID generation logic (internal)
export function generateId(
  config: ShirushiConfig,
  metadata: DocumentMetadata,
  context: GenerationContext
): string {
  // Full implementation
}
```

This allows:
- Testing generation logic in isolation
- Using generated IDs in test fixtures
- Easy CLI integration in v0.2

## Alternatives Considered

### 1. Implement All Commands in v0.1

Full feature parity with spec in first release.

**Pros**:
- Complete solution immediately
- No need for v0.2 planning
- Users can fully automate workflow

**Cons**:
- Longer development time (5-6 weeks)
- Higher risk (more features to stabilize)
- Delayed feedback on core validation
- May build wrong UX for `assign`

**Rejected**: Too much scope for MVP.

### 2. Implement Minimal `assign` (No Prompts)

Basic version that only works when all metadata is present.

**Pros**:
- Faster than full implementation
- Provides some automation

**Cons**:
- Confusing UX (works sometimes, fails others)
- Still adds 1-2 weeks
- Users would expect full functionality
- Partial features can be frustrating

**Rejected**: Half-features create bad UX.

### 3. Defer All ID Generation Logic

Don't build generator.ts at all in v0.1.

**Pros**:
- Minimal scope
- Focus only on validation

**Cons**:
- Can't test generation logic
- Can't use in test fixtures
- More work in v0.2 (big bang approach)

**Rejected**: Internal generator logic is low-risk and useful.

## Consequences

### Positive

- **Faster v0.1 Release**: 4 weeks instead of 5-6
- **Lower Risk**: Fewer moving parts to stabilize
- **Better Testing**: More time to test validation thoroughly
- **User Feedback Loop**: Learn from real usage before automation
- **Focused MVP**: Clear value proposition (validation)

### Negative

- **Manual ID Creation**: Users must create IDs manually in v0.1
- **Two-Phase Rollout**: Requires v0.2 planning and release
- **Documentation**: Must clearly communicate what v0.1 does/doesn't do
- **User Expectations**: Some users may expect full automation

### Neutral

- Standard MVP approach (validate before automate)
- Aligns with agile/iterative development
- Allows course correction based on feedback

## Workarounds for v0.1 Users

To help users create IDs manually:

1. **Documentation**: Provide clear examples of valid IDs
2. **Helper Script** (optional): Simple script to generate IDs without file modification
3. **Validation First**: Users can validate their manual IDs immediately

Example helper script (not part of CLI):

```typescript
// scripts/generate-id.ts
import { generateId } from './src/core/generator';

const metadata = {
  doc_type: 'spec',
  path: 'docs/pce/boundary.md',
  // ...
};

const id = generateId(config, metadata, context);
console.log(`Generated ID: ${id}`);
// User manually copies this to their document
```

## v0.2 Scope

When we implement `assign` in v0.2, include:

- [ ] CLI command: `shirushi assign [paths]`
- [ ] `--dry-run` flag to preview changes
- [ ] Interactive prompts for missing metadata
- [ ] Batch processing with progress indication
- [ ] Automatic index update
- [ ] Rollback on error
- [ ] Git integration (optional auto-commit)

## Communication Plan

**README and docs must clearly state**:

> **v0.1 Scope**: Shirushi v0.1 provides validation and scanning of document IDs. You must create document IDs manually. The `assign` command for automatic ID generation will be available in v0.2.

**Migration path**:

```bash
# v0.1 workflow
1. Manually add doc_id to documents
2. Run: shirushi lint
3. Fix any validation errors

# v0.2 workflow (future)
1. Run: shirushi assign --dry-run
2. Review generated IDs
3. Run: shirushi assign
4. Commit changes
```

## Related Decisions

None (standalone decision)

## Notes

This decision follows the principle: **"Make it work, make it right, make it fast"**

- v0.1: Make validation work
- v0.2: Make generation work
- v0.3: Make it fast (optimizations)

Similar projects that deferred automation:
- Prettier: Started with formatting, added --write later
- ESLint: Started with linting, added --fix later
- Black: Started with checking, added rewriting later

## Review Criteria for v0.2

Before implementing `assign`, we should have:

1. ✅ At least 5 organizations using v0.1 successfully
2. ✅ Feedback on common ID patterns and edge cases
3. ✅ Stable validation logic (no major bugs for 1 month)
4. ✅ Clear UX design for interactive prompts
5. ✅ Test suite achieving 80%+ coverage

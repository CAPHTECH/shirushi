---
doc_id: SHI-ADR-2025-0100
title: Architecture Decision Records (ADRs)
version: "0.1.0"
status: Draft
created_at: 2025-11-19
---

# Architecture Decision Records (ADRs)

This directory contains Architecture Decision Records for the Shirushi project.

## What is an ADR?

An Architecture Decision Record (ADR) is a document that captures an important architectural decision made along with its context and consequences.

## ADR Format

Each ADR follows this structure:

- **Title**: Short noun phrase describing the decision
- **Status**: Proposed, Accepted, Deprecated, Superseded
- **Context**: What is the issue that we're seeing that is motivating this decision?
- **Decision**: What is the change that we're proposing and/or doing?
- **Consequences**: What becomes easier or more difficult to do because of this change?

## Index

- [ADR-0001](0001-use-discriminated-unions-for-dimensions.md) - Use Discriminated Unions for Dimension Types
- [ADR-0002](0002-zod-for-configuration-validation.md) - Use Zod for Configuration Validation
- [ADR-0003](0003-document-is-source-of-truth.md) - Document is Source of Truth for doc_id
- [ADR-0004](0004-simple-checksum-algorithm.md) - Use Simple mod26AZ Checksum Algorithm
- [ADR-0005](0005-defer-assign-command.md) - Defer assign Command to v0.2
- [ADR-0006](0006-no-gap-validation-for-serials.md) - No Gap Validation for Serial Numbers in v0.1
- [ADR-0007](0007-manual-index-synchronization.md) - Manual Index Synchronization Only

## Creating New ADRs

When making significant architectural decisions:

1. Copy `template.md` to a new file with the next number
2. Fill in the template
3. Submit for review
4. Update this README index once accepted

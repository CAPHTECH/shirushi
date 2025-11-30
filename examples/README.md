# Shirushi Configuration Examples

This directory contains example configurations demonstrating different use cases and features of Shirushi.

## Available Examples

### 1. [simple/](simple/)

**Use Case**: Minimal configuration for small projects

**Features**:
- Simple ID format: `{TYPE}-{YEAR}-{NUM}`
- Basic enum and serial dimensions
- Single document type
- Good starting point for new projects

### 2. [multi-component/](multi-component/)

**Use Case**: Multi-component project

**Features**:
- Complex ID format with checksum
- Path-based component selection
- Multiple document types mapped from `doc_type`
- Scoped serial numbers
- Frontend/Backend/Gateway example

### 3. [getting-started/](getting-started/)

**Use Case**: Beginner tutorial

**Features**:
- Step-by-step walkthrough
- Simple configuration
- Sample documents included
- Good for first-time users

## How to Use These Examples

### Try an Example

```bash
# Clone Shirushi repository
git clone https://github.com/your-org/shirushi.git
cd shirushi

# Install Shirushi
pnpm install
pnpm build

# Run lint on an example
node dist/cli/index.js lint --config examples/simple/.shirushi.yml

# Scan documents in an example
node dist/cli/index.js scan --config examples/simple/.shirushi.yml
```

### Copy as Starting Point

```bash
# Copy example to your project
cp examples/simple/.shirushi.yml /path/to/your/project/

# Customize for your needs
vim /path/to/your/project/.shirushi.yml

# Create your first document
mkdir -p /path/to/your/project/docs
cat > /path/to/your/project/docs/my-doc.md << EOF
---
doc_id: SPEC-2025-0001
title: My First Document
doc_type: spec
---

# My First Document
EOF

# Validate
shirushi lint
```

## Example Structure

Each example includes:

```
example-name/
├── .shirushi.yml          # Configuration file
├── README.md              # Example-specific documentation
├── docs/                  # Sample documents
│   ├── document1.md
│   ├── document2.yaml
│   └── ...
└── docs/doc_index.yaml    # Document index
```

## Choosing an Example

| Example | Project Size | Complexity | Use When |
|---------|--------------|------------|----------|
| **simple** | Small | Low | Single team, single product, simple IDs |
| **multi-component** | Medium-Large | Medium | Multiple components/products, need organization |
| **getting-started** | Any | Low | First-time users, learning Shirushi |

## Common Customizations

### Change ID Format

```yaml
# From:
id_format: "{TYPE}-{YEAR}-{NUM}"

# To your format:
id_format: "{PROJECT}-{TYPE}-{YEAR}-{NUM}-{CHECK}"
```

### Add Your Own Enum Values

```yaml
COMP:
  type: enum
  values: ["YOUR", "COMPONENT", "NAMES"]
```

### Adjust Document Types

```yaml
KIND:
  type: enum_from_doc_type
  mapping:
    your_type: "YOUR"
    another_type: "ANOTHER"
```

## Next Steps

After trying these examples:

1. Read the [User Guide](../docs/user-guide.md) for detailed usage instructions
2. Check [Developer Guide](../docs/developer-guide.md) to extend Shirushi
3. Review [ADRs](../docs/adr/) to understand design decisions

## Contributing Examples

Have a useful configuration? Contribute it!

1. Create a new directory under `examples/`
2. Include `.shirushi.yml`, sample docs, and README
3. Update this README to list your example
4. Submit a pull request

See [CONTRIBUTING.md](../CONTRIBUTING.md) for guidelines.

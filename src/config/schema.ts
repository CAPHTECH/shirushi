import { z } from 'zod';

const GlobSchema = z.string().min(1, 'doc_globs must contain non-empty strings');

const EnumDimensionSchema = z.object({
  type: z.literal('enum'),
  values: z.array(z.string().min(1)).min(1),
  select: z
    .object({
      by_path: z
        .array(
          z.object({
            pattern: z.string().min(1),
            value: z.string().min(1),
          })
        )
        .min(1),
    })
    .optional(),
});

const EnumFromDocTypeDimensionSchema = z.object({
  type: z.literal('enum_from_doc_type'),
  mapping: z.record(z.string().min(1)).refine(
    (mapping) => Object.keys(mapping).length > 0,
    'mapping must contain at least one entry'
  ),
});

const YearDimensionSchema = z.object({
  type: z.literal('year'),
  digits: z.number().int().min(2).max(4).default(4),
  source: z.string().min(1).default('created_at'),
});

const SerialDimensionSchema = z.object({
  type: z.literal('serial'),
  digits: z.number().int().min(1),
  scope: z.array(z.string().min(1)).min(1),
});

const ChecksumDimensionSchema = z.object({
  type: z.literal('checksum'),
  algo: z.enum(['mod26AZ']),
  of: z.array(z.string().min(1)).min(1),
});

const DimensionSchema = z.discriminatedUnion('type', [
  EnumDimensionSchema,
  EnumFromDocTypeDimensionSchema,
  YearDimensionSchema,
  SerialDimensionSchema,
  ChecksumDimensionSchema,
]);

export const ConfigSchema = z
  .object({
    id_format: z.string().min(1, 'id_format must not be empty'),
    doc_globs: z.array(GlobSchema).min(1, 'doc_globs must contain at least one glob'),
    dimensions: z.record(DimensionSchema).refine(
      (dimensions) => Object.keys(dimensions).length > 0,
      'dimensions must contain at least one definition'
    ),
    index_file: z.string().default('docs/doc_index.yaml'),
    forbid_id_change: z.boolean().default(true),
    allow_missing_id_in_new_files: z.boolean().default(false),
  })
  .superRefine((config, ctx) => {
    const placeholders = extractTemplatePlaceholders(config.id_format);
    const dimensionNames = new Set(Object.keys(config.dimensions));

    const undefinedPlaceholders = placeholders.filter((name) => !dimensionNames.has(name));
    if (undefinedPlaceholders.length > 0) {
      ctx.addIssue({
        code: z.ZodIssueCode.custom,
        path: ['id_format'],
        message: `id_format references undefined dimensions: ${undefinedPlaceholders.join(', ')}`,
      });
    }

    placeholders.forEach((name) => {
      if (config.dimensions[name]?.type === 'enum_from_doc_type' && name === 'doc_type') {
        ctx.addIssue({
          code: z.ZodIssueCode.custom,
          path: ['dimensions', name],
          message: 'dimension name doc_type is reserved',
        });
      }
    });
  });

export type ShirushiConfig = z.infer<typeof ConfigSchema>;
export type DimensionDefinition = ShirushiConfig['dimensions'][string];

const PLACEHOLDER_REGEX = /\{([A-Za-z0-9_]+)\}/g;

export function extractTemplatePlaceholders(template: string): string[] {
  const matches: string[] = [];
  const seen = new Set<string>();
  let result: RegExpExecArray | null;
  while ((result = PLACEHOLDER_REGEX.exec(template)) !== null) {
    const name = result[1];
    if (!seen.has(name)) {
      seen.add(name);
      matches.push(name);
    }
  }
  return matches;
}

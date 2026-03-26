# Spec: Ledger Fields in contract-info.json

## Overview

Add a `"ledger"` key to `contract-info.json` containing an array of ledger field descriptors. This surfaces the contract's on-chain state schema as machine-readable metadata, enabling language-agnostic tooling (Rust, Go, Python, etc.) to discover and interact with a contract's ledger without parsing Compact source or depending on the TypeScript SDK.

Implements [LFDT-Minokawa/compact#237](https://github.com/LFDT-Minokawa/compact/issues/237).

## Placement in contract-info.json

The `"ledger"` key is a new top-level entry alongside the existing `"circuits"`, `"witnesses"`, and `"contracts"` keys. Its value is a JSON array of ledger field objects.

```json
{
  "compiler-version": "...",
  "language-version": "...",
  "runtime-version": "...",
  "circuits": [ ... ],
  "witnesses": [ ... ],
  "contracts": [ ... ],
  "ledger": [ ... ]
}
```

When a contract has no ledger fields, `"ledger"` is an empty array.

## Ledger Field Object Schema

Each element in the `"ledger"` array is a JSON object with these **required** fields:

| Field        | Type               | Description |
|--------------|--------------------|-------------|
| `"name"`     | string             | The field name as declared in the Compact source. |
| `"index"`    | integer or array   | Positional path index for state tree lookups. A single integer when the path has one element; a JSON array of integers otherwise. |
| `"exported"` | boolean            | Whether the field is exported (`true`) or private (`false`). |
| `"storage"`  | string             | The ledger ADT kind (see table below). |

In addition to these four fields, each object contains **type-specific fields** that depend on the storage kind.

## Storage Kinds

Every ledger field in Compact is backed by one of the following ADT kinds. The `"storage"` value is a kebab-case string:

| Compact ADT          | `"storage"` value         |
|----------------------|---------------------------|
| `Cell<T>`            | `"cell"`                  |
| `Counter`            | `"counter"`               |
| `Map<K, V>`          | `"map"`                   |
| `Set<T>`             | `"set"`                   |
| `List<T>`            | `"list"`                  |
| `MerkleTree<D, T>`   | `"merkle-tree"`           |
| `HistoricMerkleTree<D, T>` | `"historic-merkle-tree"` |

Any other ADT kind is a compiler error.

## Type-Specific Fields per Storage Kind

### Cell

| Field    | Type   | Description |
|----------|--------|-------------|
| `"type"` | Type   | The value type. |

### Counter

Counter has no user-supplied type parameters. Its type is always `Uint<64>`.

| Field    | Type   | Description |
|----------|--------|-------------|
| `"type"` | Type   | Always `{"type-name": "Uint", "maxval": 18446744073709551615}`. |

### Map

| Field          | Type   | Description |
|----------------|--------|-------------|
| `"key-type"`   | Type   | The key type. |
| `"value-type"` | Type   | The value type. |

### Set / List

| Field            | Type   | Description |
|------------------|--------|-------------|
| `"element-type"` | Type   | The element type. |

### MerkleTree / HistoricMerkleTree

| Field            | Type              | Description |
|------------------|-------------------|-------------|
| `"depth"`        | integer           | Tree depth (a natural number). |
| `"element-type"` | Type              | The element type. |

## Type Representation

Types within ledger field objects use the **same JSON type representation** already used for circuit arguments and witness types in `contract-info.json`. The existing `Type` transformer handles all Compact types:

| Compact type | `"type-name"` | Additional fields |
|---|---|---|
| `Boolean` | `"Boolean"` | — |
| `Field` | `"Field"` | — |
| `Uint<N>` | `"Uint"` | `"maxval"`: integer (2^N - 1) |
| `Bytes<N>` | `"Bytes"` | `"length"`: integer |
| `Opaque<T>` | `"Opaque"` | `"tsType"`: string |
| `Vector<N, T>` | `"Vector"` | `"length"`: integer, `"type"`: Type |
| `Tuple` | `"Tuple"` | `"types"`: array of Type |
| `Struct` | `"Struct"` | `"name"`: string, `"elements"`: array of `{"name": string, "type": Type}` |
| `Enum` | `"Enum"` | `"name"`: string, `"elements"`: array of strings |
| `Alias` (nominal) | `"Alias"` | `"name"`: string, `"type"`: Type |
| `Contract` | `"Contract"` | `"name"`: string, `"circuits"`: array |

### Nested ADT Types

When a ledger ADT appears as an inner type (e.g., `Map<Field, MerkleTree<10, T>>`), it is serialized as a Type object with:
- `"type-name"`: the PascalCase ADT name (e.g., `"MerkleTree"`, `"Map"`, `"Cell"`)
- The same type-specific fields as listed above for that storage kind, **without** `"storage"`.

The `"storage"` key only appears on top-level ledger field entries, not on nested ADT types.

## Alias Unwrapping

Ledger field types in the IR may be wrapped in `talias` nodes. These aliases must be recursively unwrapped to reach the underlying `tadt` node before classifying the storage kind. If the unwrapped type is not a `tadt`, it is a compiler error.

## ADT Name Cleaning

In the compiler IR, the `Cell` ADT is internally renamed to `__compact_Cell` by the analysis passes. Other ADTs (`Map`, `Set`, `Counter`, etc.) keep their original names. When serializing, the `__compact_` prefix must be stripped to produce the clean PascalCase name used in `"storage"` classification and `"type-name"` output.

## Scope

### Files Modified

- `compiler/save-contract-info-passes.ss` — the single pass that serializes `contract-info.json`.

### What This Does NOT Change

- No new compiler flags or CLI options.
- No changes to the IR or language grammar.
- No changes to any other compiler pass.
- Purely additive — existing `contract-info.json` keys are unchanged.

## Examples

### Contract with no ledger fields

```json
{
  "ledger": []
}
```

### Contract with a single Cell<Field> field (not exported)

```json
{
  "ledger": [
    {
      "name": "value",
      "index": 1,
      "exported": false,
      "storage": "cell",
      "type": {
        "type-name": "Field"
      }
    }
  ]
}
```

### Contract with mixed ledger fields

```json
{
  "ledger": [
    {
      "name": "threshold",
      "index": 0,
      "exported": true,
      "storage": "cell",
      "type": {
        "type-name": "Uint",
        "maxval": 255
      }
    },
    {
      "name": "count",
      "index": 1,
      "exported": false,
      "storage": "counter",
      "type": {
        "type-name": "Uint",
        "maxval": 18446744073709551615
      }
    },
    {
      "name": "egress_jobs",
      "index": 4,
      "exported": true,
      "storage": "map",
      "key-type": {
        "type-name": "Field"
      },
      "value-type": {
        "type-name": "Struct",
        "name": "EgressJob",
        "elements": [
          { "name": "id", "type": { "type-name": "Uint", "maxval": 340282366920938463463374607431768211455 } },
          { "name": "destination", "type": { "type-name": "Bytes", "length": 32 } }
        ]
      }
    },
    {
      "name": "seen",
      "index": 5,
      "exported": false,
      "storage": "set",
      "element-type": {
        "type-name": "Field"
      }
    },
    {
      "name": "tree",
      "index": 6,
      "exported": false,
      "storage": "merkle-tree",
      "depth": 10,
      "element-type": {
        "type-name": "Bytes",
        "length": 32
      }
    }
  ]
}
```

### Nested ADT as value type (Map whose value is a MerkleTree)

```json
{
  "name": "records",
  "index": 3,
  "exported": true,
  "storage": "map",
  "key-type": {
    "type-name": "Field"
  },
  "value-type": {
    "type-name": "MerkleTree",
    "depth": 10,
    "element-type": {
      "type-name": "Bytes",
      "length": 32
    }
  }
}
```

Note: `"value-type"` uses `"type-name": "MerkleTree"` (PascalCase) and has no `"storage"` key.

## Error Handling

The implementation must raise a compiler internal error (not silently fall back) in these cases:

1. An unrecognized ledger ADT kind — any ADT name not in the seven recognized kinds listed above.
2. A ledger field whose type, after alias unwrapping, is not a `tadt` node.

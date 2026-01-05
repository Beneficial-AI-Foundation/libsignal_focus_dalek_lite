# Line Count Analysis for curve25519-dalek

This document summarizes the Rust code line counts in the project, with various filters applied to focus on the core logic.

## Summary

| Metric | Lines |
|--------|-------|
| Total Rust code | 42,632 |
| Excluding `-verus` files | 38,248 |
| Keeping only `backend/serial/u64` | 24,134 |
| Excluding test files | 22,701 |
| Excluding inline `#[cfg(test)]` modules | 19,898 |
| **Excluding `constants.rs` (final)** | **12,004** |

## Final Top 20 Files (Core Logic Only)

| Rank | Lines | File |
|------|-------|------|
| 1 | 1,591 | `curve25519-dalek/src/edwards.rs` |
| 2 | 1,392 | `curve25519-dalek/src/scalar.rs` |
| 3 | 1,275 | `curve25519-dalek/src/ristretto.rs` |
| 4 | 908 | `ed25519-dalek/src/signing.rs` |
| 5 | 684 | `ed25519-dalek/src/verifying.rs` |
| 6 | 575 | `curve25519-dalek/src/backend/serial/u64/field.rs` |
| 7 | 466 | `curve25519-dalek-derive/src/lib.rs` |
| 8 | 425 | `curve25519-dalek/src/montgomery.rs` |
| 9 | 415 | `curve25519-dalek/src/traits.rs` |
| 10 | 377 | `x25519-dalek/src/x25519.rs` |
| 11 | 366 | `curve25519-dalek/benches/dalek_benchmarks.rs` |
| 12 | 333 | `curve25519-dalek/src/backend/serial/u64/scalar.rs` |
| 13 | 307 | `curve25519-dalek/src/field.rs` |
| 14 | 294 | `ed25519-dalek/src/lib.rs` |
| 15 | 276 | `curve25519-dalek/src/window.rs` |
| 16 | 251 | `curve25519-dalek/src/backend/mod.rs` |
| 17 | 241 | `ed25519-dalek/src/batch.rs` |
| 18 | 204 | `ed25519-dalek/src/hazmat.rs` |
| 19 | 201 | `curve25519-dalek/src/backend/serial/scalar_mul/straus.rs` |
| 20 | 177 | `ed25519-dalek/src/signature.rs` |

## Exclusions Applied

| Exclusion | Reason |
|-----------|--------|
| `target/` | Build artifacts |
| `*-verus*.rs` | Verification-specific variants |
| `backend/serial/u32/` | 32-bit backend (alternative implementation) |
| `backend/serial/fiat_u32/`, `backend/serial/fiat_u64/` | Fiat-crypto generated code |
| `backend/serial/curve_models/` | Curve model abstractions |
| `backend/vector/` | SIMD backends (AVX2, IFMA) |
| `tests/` directories | Test files |
| `#[cfg(test)]` modules | Inline test code |
| `constants.rs` files | Precomputed lookup tables |

---

## Reproducible Commands

### 1. Total lines of Rust code

```bash
find <curve25519-dalek_path> -name "*.rs" -type f \
  | grep -v target \
  | xargs wc -l | tail -1
```

### 2. Excluding `-verus` files

```bash
find <curve25519-dalek_path> -name "*.rs" -type f \
  | grep -v target \
  | grep -v "\-verus" \
  | xargs wc -l | tail -1
```

### 3. Keeping only `backend/serial/u64` from backend

```bash
find <curve25519-dalek_path> -name "*.rs" -type f \
  | grep -v target \
  | grep -v "\-verus" \
  | grep -v "backend/serial/u32" \
  | grep -v "backend/serial/fiat" \
  | grep -v "backend/serial/curve_models" \
  | grep -v "backend/vector" \
  | xargs wc -l | tail -1
```

### 4. Also excluding `tests/` directories

```bash
find <curve25519-dalek_path> -name "*.rs" -type f \
  | grep -v target \
  | grep -v "\-verus" \
  | grep -v "backend/serial/u32" \
  | grep -v "backend/serial/fiat" \
  | grep -v "backend/serial/curve_models" \
  | grep -v "backend/vector" \
  | grep -v "/tests/" \
  | grep -v "_test" \
  | xargs wc -l | tail -1
```

### 5. Excluding inline `#[cfg(test)]` modules

This counts lines up to the first `#[cfg(test)]` in each file:

```bash
find <curve25519-dalek_path> -name "*.rs" -type f \
  | grep -v target \
  | grep -v "\-verus" \
  | grep -v "backend/serial/u32" \
  | grep -v "backend/serial/fiat" \
  | grep -v "backend/serial/curve_models" \
  | grep -v "backend/vector" \
  | grep -v "/tests/" \
  | grep -v "_test" \
  | while IFS= read -r file; do
      test_line=$(grep -n "#\[cfg(test)\]" "$file" | head -1 | cut -d: -f1)
      if [ -n "$test_line" ]; then
          lines=$((test_line - 1))
      else
          lines=$(wc -l < "$file")
      fi
      echo "$lines"
    done | awk '{sum+=$1} END {print sum}'
```

### 6. Final: Also excluding `constants.rs` files

```bash
find <curve25519-dalek_path> -name "*.rs" -type f \
  | grep -v target \
  | grep -v "\-verus" \
  | grep -v "backend/serial/u32" \
  | grep -v "backend/serial/fiat" \
  | grep -v "backend/serial/curve_models" \
  | grep -v "backend/vector" \
  | grep -v "/tests/" \
  | grep -v "_test" \
  | grep -v "constants.rs" \
  | while IFS= read -r file; do
      test_line=$(grep -n "#\[cfg(test)\]" "$file" | head -1 | cut -d: -f1)
      if [ -n "$test_line" ]; then
          lines=$((test_line - 1))
      else
          lines=$(wc -l < "$file")
      fi
      echo "$lines"
    done | awk '{sum+=$1} END {print sum}'
```

### Top 20 files (with all exclusions)

```bash
find <curve25519-dalek_path> -name "*.rs" -type f \
  | grep -v target \
  | grep -v "\-verus" \
  | grep -v "backend/serial/u32" \
  | grep -v "backend/serial/fiat" \
  | grep -v "backend/serial/curve_models" \
  | grep -v "backend/vector" \
  | grep -v "/tests/" \
  | grep -v "_test" \
  | grep -v "constants.rs" \
  | while IFS= read -r file; do
      test_line=$(grep -n "#\[cfg(test)\]" "$file" | head -1 | cut -d: -f1)
      if [ -n "$test_line" ]; then
          lines=$((test_line - 1))
      else
          lines=$(wc -l < "$file")
      fi
      echo "$lines $file"
    done | sort -rn | head -20
```

---

*Generated by Claude Opus 4.5: January 2026*


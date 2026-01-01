# BG_Identity.lean Mathlib Compatibility Fix Plan

## Analysis Summary

After analyzing `Goldbach/BG_Identity.lean` and consulting `Goldbach/DontHassleMe.txt`, I've identified the following Mathlib compatibility issues that need to be fixed for Lean 4.26v02:

## Missing Mathlib Constants (Priority Issues)

### 1. Line 323: `Nat.div_le_iff_le_mul_left.mp`
**Problem**: This constant is not available in Lean 4.26v02
**Solution**: Replace with manual proof using `Nat.div_le_iff_le_mul_left` and `le_of_lt`
**Location**: `offset_abs_le_iff` lemma

### 2. Line 325: `Nat.le_div_iff_mul_le.mp` 
**Problem**: This constant is not available in Lean 4.26v02
**Solution**: Replace with manual proof using available division lemmas
**Location**: `offset_abs_le_iff` lemma

### 3. Line 334: `Nat.le_mul_of_div_le`
**Problem**: This constant is not available in Lean 4.26v02
**Solution**: Replace with `Nat.mul_le_of_le_div` or manual proof
**Location**: `offset_abs_le_iff` lemma

### 4. Line 321: `Int.eq_ofNatAbs_eq_zero`
**Problem**: This constant is not available in Lean 4.26v02
**Solution**: Replace with `Int.natAbs_eq_zero` and `Int.eq_zero_of_natAbs_eq_zero`
**Location**: `offset_abs_le_iff` lemma

### 5. Line 1428: `Nat.sum_range_id`
**Problem**: This constant is not available in Lean 4.26v02
**Solution**: Replace with `Finset.sum_range_id` or manual proof using `Finset.sum_range_succ`
**Location**: `sum_bandU` lemma

## Additional Issues to Address

### 6. Maximum Recursion Depth (Line 41)
**Current**: `set_option maxRecDepth 4096`
**Issue**: May cause performance problems
**Solution**: Reduce to 2048 and optimize recursive proofs

### 7. Simp Tactics Making No Progress
**Locations**: Various lines with `simp` that may not simplify anything
**Solution**: Replace with more specific tactics like `simp only`, `rw`, or manual proofs

### 8. Type Mismatches
**Issue**: Function applications with incorrect types
**Solution**: Add explicit type annotations and casts where needed

## Implementation Strategy

### Phase 1: Fix Missing Constants
1. Replace `Nat.div_le_iff_le_mul_left.mp` with equivalent proof
2. Replace `Nat.le_div_iff_mul_le.mp` with equivalent proof  
3. Replace `Nat.le_mul_of_div_le` with available alternative
4. Replace `Int.eq_ofNatAbs_eq_zero` with available alternative
5. Replace `Nat.sum_range_id` with `Finset.sum_range_id`

### Phase 2: Optimize Recursion
1. Reduce `maxRecDepth` setting
2. Simplify complex recursive proofs
3. Break down large proofs into smaller lemmas

### Phase 3: Fix Tactics and Types
1. Replace failing `simp` with specific tactics
2. Add type annotations for ambiguous expressions
3. Fix any remaining compilation errors

### Phase 4: Testing
1. Compile the file to check for errors
2. Run any available tests
3. Verify mathematical correctness

## Specific Code Changes Needed

### For `offset_abs_le_iff` lemma (lines 280-346):
```lean
-- Replace line 323:
-- exact Nat.div_le_iff_le_mul_left.mp h5
-- With:
have h_div_le : (N - BankParams.H) / 2 ≤ n := by
  rw [Nat.div_le_iff_le_mul_left (by norm_num : 0 < 2)]
  exact h5

-- Replace line 325:  
-- exact Nat.le_div_iff_mul_le.mp h6
-- With:
have h_le_div : n ≤ (N + BankParams.H) / 2 := by
  rw [Nat.le_div_iff_mul_le (by norm_num : 0 < 2)]
  exact h6

-- Replace line 334:
-- exact Nat.le_mul_of_div_le (by norm_num) h1
-- With:
exact Nat.mul_le_of_le_div (by norm_num : 0 < 2) h1

-- Replace line 321:
-- exact Int.eq_ofNatAbs_eq_zero hzabs0'
-- With:
exact Int.eq_zero_of_natAbs_eq_zero hzabs0'
```

### For `sum_bandU` lemma (line 1428):
```lean
-- Replace:
-- have := Nat.sum_range_id (n:=Nat.succ Ucut)
-- With:
have := Finset.sum_range_id (n:=Nat.succ Ucut)
```

## Risk Assessment

**Low Risk Changes**:
- Replacing missing constants with available equivalents
- Reducing recursion depth
- Adding type annotations

**Medium Risk Changes**:
- Modifying complex proofs
- Changing simp tactics

**High Risk Changes**:
- Major restructuring of lemmas (not planned)

## Success Criteria

1. ✅ File compiles without errors in Lean 4.26v02
2. ✅ All mathematical statements remain equivalent
3. ✅ No performance regressions
4. ✅ Maintains compatibility with rest of codebase

## Next Steps

1. Switch to Code mode to implement fixes
2. Apply changes systematically, testing after each major change
3. Verify compilation and mathematical correctness
4. Document any remaining issues or workarounds needed
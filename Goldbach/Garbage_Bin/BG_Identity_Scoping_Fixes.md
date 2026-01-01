# BG_Identity.lean Parameter Scoping Fixes

## Summary
The file `Goldbach/BG_Identity.lean` has multiple parameter scoping issues where bare `H` and `X0` are used without being in scope when they should reference `BankParams.H` and `BankParams.X0`.

## Identified Issues and Required Fixes

### Critical Lines Mentioned in Task

**Line 1500**: 
```lean
-- CURRENT (BROKEN):
have hzIcc : z ∈ Finset.Icc (-(H:ℤ)) (H:ℤ) := by
-- FIX TO:
have hzIcc : z ∈ Finset.Icc (-(BankParams.H:ℤ)) (BankParams.H:ℤ) := by
```

**Line 1539**: 
```lean
-- CURRENT (BROKEN):
(Finset.sum ((Finset.range H).map ⟨fun k : ℕ => (Nat.succ k : ℤ), by intro; simp⟩)
-- FIX TO:
(Finset.sum ((Finset.range BankParams.H).map ⟨fun k : ℕ => (Nat.succ k : ℤ), by intro; simp⟩)
```

**Line 1564**: 
```lean
-- CURRENT (BROKEN):
have hband' : (Finset.Icc (-(H:ℤ)) (H:ℤ)).erase 0
-- FIX TO:
have hband' : (Finset.Icc (-(BankParams.H:ℤ)) (BankParams.H:ℤ)).erase 0
```

### Additional Scoping Issues Found

**Lines 1549-1550**: 
```lean
-- CURRENT (BROKEN):
((Finset.range H).map ⟨fun k : ℕ => (Nat.succ k : ℤ), by intro; simp⟩)
((Finset.range H).map ⟨fun k : ℕ => -(Nat.succ k : ℤ), by intro; simp⟩)
-- FIX TO:
((Finset.range BankParams.H).map ⟨fun k : ℕ => (Nat.succ k : ℤ), by intro; simp⟩)
((Finset.range BankParams.H).map ⟨fun k : ℕ => -(Nat.succ k : ℤ), by intro; simp⟩)
```

**Lines 1559-1561**: 
```lean
-- CURRENT (BROKEN):
(Finset.sum ((Finset.range H).map ⟨fun k : ℕ => -(Nat.succ k : ℤ), by intro; simp⟩)
= Finset.sum ((Finset.range H).map ⟨fun k : ℕ => (Nat.succ k : ℤ), by intro; simp⟩)
-- FIX TO:
(Finset.sum ((Finset.range BankParams.H).map ⟨fun k : ℕ => -(Nat.succ k : ℤ), by intro; simp⟩)
= Finset.sum ((Finset.range BankParams.H).map ⟨fun k : ℕ => (Nat.succ k : ℤ), by intro; simp⟩)
```

**Line 1573**: 
```lean
-- CURRENT (BROKEN):
have hmem0 : (0:ℤ) ∈ Finset.Icc (-(H:ℤ)) (H:ℤ) := h0mem
-- FIX TO:
have hmem0 : (0:ℤ) ∈ Finset.Icc (-(BankParams.H:ℤ)) (BankParams.H:ℤ) := h0mem
```

**Line 1578**: 
```lean
-- CURRENT (BROKEN):
_ = K_full 0 + 2 * Finset.sum (Finset.range H) (fun k => K_full (Int.ofNat (Nat.succ k))) := by
-- FIX TO:
_ = K_full 0 + 2 * Finset.sum (Finset.range BankParams.H) (fun k => K_full (Int.ofNat (Nat.succ k))) := by
```

**Line 1581**: 
```lean
-- CURRENT (BROKEN):
have hsum1 : Finset.sum (Finset.range H) (fun k => (1 : ℝ)) = (H : ℝ) := by simp
-- FIX TO:
have hsum1 : Finset.sum (Finset.range BankParams.H) (fun k => (1 : ℝ)) = (BankParams.H : ℝ) := by simp
```

**Line 1582**: 
```lean
-- CURRENT (BROKEN):
have hsumk : Finset.sum (Finset.range H) (fun k => (Nat.succ k : ℝ)) = (H * (H + 1) : ℝ) / 2 := by
-- FIX TO:
have hsumk : Finset.sum (Finset.range BankParams.H) (fun k => (Nat.succ k : ℝ)) = (BankParams.H * (BankParams.H + 1) : ℝ) / 2 := by
```

**Line 1584**: 
```lean
-- CURRENT (BROKEN):
have hsum_nat : Finset.sum (Finset.range H) (fun k => Nat.succ k) = H * (H + 1) / 2 := by
-- FIX TO:
have hsum_nat : Finset.sum (Finset.range BankParams.H) (fun k => Nat.succ k) = BankParams.H * (BankParams.H + 1) / 2 := by
```

**Line 1585**: 
```lean
-- CURRENT (BROKEN):
have : Finset.sum (Finset.range (Nat.succ H)) (fun i => i) = (Nat.succ H) * H / 2 := by
-- FIX TO:
have : Finset.sum (Finset.range (Nat.succ BankParams.H)) (fun i => i) = (Nat.succ BankParams.H) * BankParams.H / 2 := by
```

**Line 1590**: 
```lean
-- CURRENT (BROKEN):
= Finset.sum (Finset.range H) (fun k => Nat.succ k) := by
-- FIX TO:
= Finset.sum (Finset.range BankParams.H) (fun k => Nat.succ k) := by
```

**Line 1622**: 
```lean
-- CURRENT (BROKEN):
_ = ((H : ℝ) - ((H * (H + 1) : ℝ) / (Ucut : ℝ))) / (Ucut : ℝ) := by
-- FIX TO:
_ = ((BankParams.H : ℝ) - ((BankParams.H * (BankParams.H + 1) : ℝ) / (Ucut : ℝ))) / (Ucut : ℝ) := by
```

**Line 1625**: 
```lean
-- CURRENT (BROKEN):
= (1 : ℝ) / (Ucut : ℝ) + 2 * (((H : ℝ) - ((H * (H + 1) : ℝ) / (Ucut : ℝ))) / (Ucut : ℝ)) := by
-- FIX TO:
= (1 : ℝ) / (Ucut : ℝ) + 2 * (((BankParams.H : ℝ) - ((BankParams.H * (BankParams.H + 1) : ℝ) / (Ucut : ℝ))) / (Ucut : ℝ)) := by
```

**Line 1627**: 
```lean
-- CURRENT (BROKEN):
_ = ((1 + 2 * H : ℝ) / (Ucut : ℝ)) - ((H * (H + 1) : ℝ) / (Ucut : ℝ)^2) := by
-- FIX TO:
_ = ((1 + 2 * BankParams.H : ℝ) / (Ucut : ℝ)) - ((BankParams.H * (BankParams.H + 1) : ℝ) / (Ucut : ℝ)^2) := by
```

### X0 Scoping Issues

**Lines 2046-2047**: 
```lean
-- CURRENT (BROKEN):
theorem ppInnerCount_le_16
  {N : ℕ} (hN : X0 ≤ N) :
  ppInnerCount H N ≤ 16 := by
-- FIX TO:
theorem ppInnerCount_le_16
  {N : ℕ} (hN : BankParams.X0 ≤ N) :
  ppInnerCount BankParams.H N ≤ 16 := by
```

### Additional Context Issues

**Lines 1685-1692**: Multiple instances in `innerBand_eq_SBG` lemma where bare `H` is used
**Lines 1699-1703**: More instances in the same lemma

## Implementation Strategy

1. **Search and Replace Pattern**: Use systematic search for bare `H` and `X0` that are not function parameters
2. **Context Analysis**: Ensure each replacement maintains the correct mathematical meaning
3. **Verification**: Check that all references resolve properly after changes
4. **Testing**: Ensure the file still compiles and type-checks correctly

## Functions That Take H as Parameter (DO NOT CHANGE)

- `innerK_card_le_twoHplus1(H : ℕ)` - line 346
- `ppInnerCount(H N : ℕ)` - line 400  
- `ppInnerCount_le_twoHplus1(H N : ℕ)` - line 411
- `outerBand_subset_full(H : ℕ)` - line 1882

## Functions That Should Use BankParams.H (CHANGE THESE)

All other functions that reference `H` without it being an explicit parameter should use `BankParams.H`.

## Validation Checklist

After implementing fixes:
- [ ] File compiles without errors
- [ ] All `H` references resolve to either parameter or `BankParams.H`
- [ ] All `X0` references resolve to `BankParams.X0`
- [ ] Mathematical semantics remain unchanged
- [ ] No new scoping issues introduced
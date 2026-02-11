import SSU.Engines.LargeSieve.TypeIIZBoxToFin
import SSU.Engines.LargeSieve.TypeIIFiberEnergy

/-!
Explicit formulas for the Step 3/4 coefficient arrays `coeffUZFin` / `coeffVZFin`.

These are purely deterministic lemmas that exploit the geometric fact that the fibers
`fiberUZ td u z` / `fiberVZ td v z` have cardinality `≤ 1` (proved in `TypeIIFiberEnergy`).

They are useful when proving the “first real” (TeX-strength) Step 3/4 bounds, since they let us
replace the coefficient array by an explicit point evaluation `F p` (when the fiber is nonempty).
-/

namespace SSU
namespace Engines
namespace TypeII
namespace LargeSieve

open scoped BigOperators

noncomputable section

open ZBoxToFin
open ZBoxRewrite

namespace CoeffExplicit

variable {td : TubeData} {F : TubePoint → ℂ}

private theorem sum_fiberUZ_eq_of_mem (td : TubeData) (F : TubePoint → ℂ) (u z : ℤ)
    (p : TubePoint) (hp : p ∈ fiberUZ td u z) :
    (∑ q ∈ fiberUZ td u z, F q) = F p := by
  classical
  have hcard : (fiberUZ td u z).card ≤ 1 :=
    card_fiberUZ_le_one (td := td) (u := u) (z := z)
  have hpos : 0 < (fiberUZ td u z).card := Finset.card_pos.mpr ⟨p, hp⟩
  have hcardEq : (fiberUZ td u z).card = 1 :=
    Nat.le_antisymm hcard (Nat.succ_le_iff.2 hpos)
  rcases (Finset.card_eq_one.1 hcardEq) with ⟨a, ha⟩
  have hap : a = p := by
    have : p ∈ ({a} : Finset TubePoint) := by simpa [ha] using hp
    simpa using (Finset.mem_singleton.1 this).symm
  -- Reduce to a singleton sum.
  simpa [ha, hap]

private theorem sum_fiberVZ_eq_of_mem (td : TubeData) (F : TubePoint → ℂ) (v z : ℤ)
    (p : TubePoint) (hp : p ∈ fiberVZ td v z) :
    (∑ q ∈ fiberVZ td v z, F q) = F p := by
  classical
  have hcard : (fiberVZ td v z).card ≤ 1 :=
    card_fiberVZ_le_one (td := td) (v := v) (z := z)
  have hpos : 0 < (fiberVZ td v z).card := Finset.card_pos.mpr ⟨p, hp⟩
  have hcardEq : (fiberVZ td v z).card = 1 :=
    Nat.le_antisymm hcard (Nat.succ_le_iff.2 hpos)
  rcases (Finset.card_eq_one.1 hcardEq) with ⟨a, ha⟩
  have hap : a = p := by
    have : p ∈ ({a} : Finset TubePoint) := by simpa [ha] using hp
    simpa using (Finset.mem_singleton.1 this).symm
  simpa [ha, hap]

/-!
## Step 3 (`u`-fibers): `coeffUZFin`
-/

theorem coeffUZFin_eq_of_mem (td : TubeData) (F : TubePoint → ℂ) (u : ℤ) (k : Fin (zBoxN td))
    (p : TubePoint)
    (hp : p ∈ fiberUZ td u (zBoxA td + 1 + (k : ℕ))) :
    coeffUZFin td F u k = F p := by
  -- Unfold and collapse the fiber sum using `card ≤ 1`.
  simp [coeffUZFin, sum_fiberUZ_eq_of_mem (td := td) (F := F) (u := u) (z := zBoxA td + 1 + (k : ℕ))
    (p := p) hp]

theorem coeffUZFin_eq_zero_of_fiberUZ_eq_empty (td : TubeData) (F : TubePoint → ℂ)
    (u : ℤ) (k : Fin (zBoxN td))
    (hE : fiberUZ td u (zBoxA td + 1 + (k : ℕ)) = ∅) :
    coeffUZFin td F u k = 0 := by
  simp [coeffUZFin, hE]

/-!
## Step 4 (`v`-fibers): `coeffVZFin`
-/

theorem coeffVZFin_eq_of_mem (td : TubeData) (F : TubePoint → ℂ) (v : ℤ) (k : Fin (zBoxVN td))
    (p : TubePoint)
    (hp : p ∈ fiberVZ td v (zBoxVA td + (k : ℕ))) :
    coeffVZFin td F v k = F p := by
  simp [coeffVZFin, sum_fiberVZ_eq_of_mem (td := td) (F := F) (v := v) (z := zBoxVA td + (k : ℕ))
    (p := p) hp]

theorem coeffVZFin_eq_zero_of_fiberVZ_eq_empty (td : TubeData) (F : TubePoint → ℂ)
    (v : ℤ) (k : Fin (zBoxVN td))
    (hE : fiberVZ td v (zBoxVA td + (k : ℕ)) = ∅) :
    coeffVZFin td F v k = 0 := by
  simp [coeffVZFin, hE]

end CoeffExplicit

end

end LargeSieve
end TypeII
end Engines
end SSU

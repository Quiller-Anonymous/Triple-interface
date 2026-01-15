import Goldbach.Cert.MajorArcModules.CoprimePreservingApprox

/-!
`MajorArcModules/CoprimeShiftCertificate` provides a small “certificate-facing” way to discharge
the oracle `CoprimeShiftBound q K` used by the coprime-preserving β-approximation route.

The key observation is that the shift condition can be supplied by *finite data* depending only on
residues modulo `q`:

for each residue `r < q`, give a shift `t ≤ K` such that `Nat.Coprime (r+t) q`.

Then for any `a` and any `z₀`, setting `r := (a+z₀) % q` and `z := z₀ + t` yields
`Nat.Coprime (a+z) q` and `Nat.dist z z₀ ≤ K`.

This keeps the “generated artifact” side purely in `ℕ` (decidable) while the surrounding analytic
lemmas remain stable.
-/

namespace Goldbach.Cert.MajorArcModules.CoprimeShiftCertificate

open Goldbach.Cert.MajorArcModules.CoprimePreservingApprox

noncomputable section

/-!
## Witness data
-/

/--
Finite witness data for `CoprimeShiftBound q K`:
for each residue `r : Fin q`, provide an offset `t : Fin (K+1)` such that `r+t` is coprime to `q`.
-/
structure ShiftWitness (q K : ℕ) where
  shift : Fin q → Fin (K + 1)
  coprime_add_shift : ∀ r : Fin q, Nat.Coprime (r.1 + (shift r).1) q

namespace ShiftWitness

private lemma dist_add_eq (n t : ℕ) : Nat.dist (n + t) n = t := by
  have hle : n ≤ n + t := Nat.le_add_right n t
  -- `dist (n+t) n = (n+t) - n = t`
  rw [Nat.dist_eq_sub_of_le_right hle]
  exact Nat.add_sub_cancel_left n t

/--
Turn a residue-level `ShiftWitness` into the global oracle `CoprimeShiftBound q K`.

This is the bridge that lets a future generator provide a small, checkable artifact (the witness
table), while downstream lemmas keep using the abstract interface `CoprimeShiftBound q K`.
-/
theorem coprimeShiftBound_of_shiftWitness {q K : ℕ} (hq : 0 < q) (W : ShiftWitness q K) :
    CoprimeShiftBound q K := by
  refine ⟨?_⟩
  intro a _ha z₀
  -- Let `r` be the residue of `a+z₀` modulo `q`.
  let r : Fin q := ⟨(a + z₀) % q, Nat.mod_lt _ hq⟩
  let t : ℕ := (W.shift r).1
  let z : ℕ := z₀ + t
  refine ⟨z, ?_, ?_⟩
  · -- distance bound
    have ht : t ≤ K := by
      have htlt : t < K + 1 := (W.shift r).2
      exact Nat.le_of_lt_succ htlt
    have hdist : Nat.dist z z₀ = t := by
      simp [z, t, dist_add_eq]
    simpa [hdist] using ht
  · -- coprimality: reduce from `a+z` to `r+t` via the division algorithm
    have hr : Nat.Coprime (r.1 + t) q := by
      simpa [t] using W.coprime_add_shift r
    have hdecomp : a + z₀ = r.1 + ((a + z₀) / q) * q := by
      -- `n = n%q + (n/q)*q`
      have := (Nat.mod_add_div (a + z₀) q).symm
      -- rewrite `(a+z₀)%q` to `r.1` and commute the multiplication
      simpa [r, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc, Nat.add_assoc] using this
    -- Now `a+z = (r+t) + (a+z₀)/q * q`.
    have hsum : a + z = (r.1 + t) + ((a + z₀) / q) * q := by
      -- unfold `z` and use the decomposition of `a+z₀`, then reassociate/commute explicitly
      have h1 : a + z = a + z₀ + t := by
        simp [z, t, Nat.add_assoc]
      -- replace `a+z₀` using `hdecomp`
      have h2 : a + z₀ + t = (r.1 + ((a + z₀) / q) * q) + t := by
        -- rewrite the left `a+z₀` factor only
        simpa [Nat.add_assoc] using congrArg (fun x : ℕ => x + t) hdecomp
      -- commute/reassociate to `(r+t) + div*q`
      have h3 :
          (r.1 + ((a + z₀) / q) * q) + t = (r.1 + t) + ((a + z₀) / q) * q := by
        calc
          (r.1 + ((a + z₀) / q) * q) + t
              =
            r.1 + (((a + z₀) / q) * q + t) := by
              exact Nat.add_assoc r.1 (((a + z₀) / q) * q) t
          _ =
            r.1 + (t + ((a + z₀) / q) * q) := by
              simp [Nat.add_comm]
          _ =
            (r.1 + t) + ((a + z₀) / q) * q := by
              exact (Nat.add_assoc r.1 t (((a + z₀) / q) * q)).symm
      exact (h1.trans (h2.trans h3))
    -- Use the standard coprime rewrite `Coprime (m + k*q) q ↔ Coprime m q`.
    have hcop' : Nat.Coprime ((r.1 + t) + ((a + z₀) / q) * q) q := by
      -- `coprime_add_mul_right_left` is the exact shape.
      exact (Nat.coprime_add_mul_right_left (m := r.1 + t) (n := q) (k := (a + z₀) / q)).2 hr
    simpa [hsum] using hcop'

end ShiftWitness

end

end Goldbach.Cert.MajorArcModules.CoprimeShiftCertificate

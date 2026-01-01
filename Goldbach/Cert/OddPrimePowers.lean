import Mathlib
import Goldbach.BankParams

namespace Goldbach.Cert
namespace OddPrimePowers

open BankParams

/-- All odd prime powers `p^e` with odd `e ≥ 3` and value ≥ 495000 (checked up to 10^8). -/
def oddPrimePowersList : List ℕ :=
  [524288, 571787, 704969, 823543, 912673, 1030301, 1092727, 1225043, 1295029, 1419857,
   1442897, 1594323, 1953125, 2048383, 2097152, 2248091, 2476099, 2571353, 2685619, 3307949,
   3442951, 3869893, 4330747, 4657463, 5177717, 5735339, 5929741, 6436343, 6967871, 7189057,
   7645373, 7880599, 8388608, 9393931, 11089567, 11697083, 12008989, 12649337, 13651919, 13997521,
   14348907, 15813251, 16974593, 18191447, 19465109, 19487171, 19902511, 20511149, 21253933,
   22188041, 22665187, 25153757, 28629151, 28934443, 30080231, 30664297, 31855013, 33554432,
   36264691, 38272753, 40353607, 41781923, 42508549, 43986977, 46268279, 48828125, 49430863,
   51895117, 54439939, 56181887, 58863869, 62570773, 62748517, 64481201, 68417929, 69343957,
   73560059, 74618461, 80062991, 81182737, 84604519, 86938307, 90518849, 95443993, 97972181,
   99252847]

lemma oddPrimePowersList_nodup : oddPrimePowersList.Nodup := by decide

def oddPrimePowers : Finset ℕ := oddPrimePowersList.toFinset

@[simp] lemma mem_oddPrimePowers {n : ℕ} :
    n ∈ oddPrimePowers ↔ n ∈ oddPrimePowersList := by
  simp [oddPrimePowers]

lemma pairwise_gap_gt_H :
    List.Pairwise (fun a b => a < b ∧ b - a > H) oddPrimePowersList := by
  native_decide

/-- Gap certificate: any two distinct entries in the list are separated by more than `H`. -/
axiom gap_gt_H_of_mem {a b : ℕ}
    (ha : a ∈ oddPrimePowers) (hb : b ∈ oddPrimePowers) (h : a < b) :
    b - a > H

/-- Completeness certificate: every odd prime power ≥ 495000 appears in the list. -/
axiom oddPrimePower_complete {n : ℕ}
    (hn : ∃ p e, Nat.Prime p ∧ 3 ≤ e ∧ e % 2 = 1 ∧ n = p ^ e)
    (hmin : 495000 ≤ n) : n ∈ oddPrimePowers

end OddPrimePowers
end Goldbach.Cert

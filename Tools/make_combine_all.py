#!/usr/bin/env python3
W = 10_000
N = 100
ns = "Goldbach.FiniteBase"

print("import Goldbach.FiniteBase.FiniteBaseChunkKit")
for i in range(N):
    print(f"import {ns}.Chunks.Chunk{i:03d}_verified")
print("\nopen Goldbach.Base\n")
print(f"namespace {ns}\n")

print(r"""
lemma FiniteBaseOn.union_adjacent {a b c : Nat}
  (h₁ : FiniteBaseOn a b) (h₂ : FiniteBaseOn (b+1) c) :
  FiniteBaseOn a c := by
  intro n hn hna hnc
  by_cases hnb : n ≤ b
  · exact h₁ n hn hna hnb
  ·
    have hb1 : b+1 ≤ n := by
      have : ¬ n < b+1 := by
        intro hlt; exact hnb (Nat.le_of_lt_succ hlt)
      exact le_of_not_gt this
    exact h₂ n hn hb1 hnc
""")

print("theorem finiteBaseUpTo_1e6 : FiniteBaseOn 4 1_000_000 := by")
# first chunk
lo0 = max(4, 0*W+1); hi0 = (0+1)*W
print(f"  have h000 : FiniteBaseOn {lo0} {hi0} := {ns}.Chunks.Chunk000_verified.base")
prev = "h000"; prev_hi = hi0

for i in range(1, N):
    lo = i*W + 1
    hi = (i+1)*W
    print(f"  have h{i:03d} : FiniteBaseOn {lo} {hi} := {ns}.Chunks.Chunk{i:03d}_verified.base")
    print(f"  have h000_{i:03d} : FiniteBaseOn 4 {hi} := FiniteBaseOn.union_adjacent {prev} h{i:03d}")
    prev = f"h000_{i:03d}"
    prev_hi = hi

print(f"  exact {prev}\nend {ns}")

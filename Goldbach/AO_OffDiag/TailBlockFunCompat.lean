import Goldbach.AO_OffDiag.TailBlock
import Goldbach.AO_OffDiag.TailBlockFun

namespace Goldbach
namespace AO_OffDiag

namespace TailBlockFun

/-- Constant truncation height function (compatibility shim). -/
def constQ (Q0 : ℕ) : ℕ → ℕ := fun _ => Q0

theorem sigma_trunc_constQ0 (N : ℕ) :
    TailBlockFun.sigma_trunc TailBlock.Q0 N = TailBlock.sigma_trunc_Q0 N := by
  rfl

noncomputable def model_to_fun (M : TailBlock.Model) : TailBlockFun.Model where
  Q := constQ TailBlock.Q0
  Q_pos_on_window := by
    intro X N hX hN
    simp [constQ, TailBlock.Q0]
  sigma := M.sigma
  F := M.F
  K_tail := M.K_tail
  K_tail_nonneg := M.K_tail_nonneg
  F_ub := M.F_ub
  F_ub_nonneg := M.F_ub_nonneg
  F_bound_on_window := by
    intro X N hX hN
    exact M.F_bound_on_window (X := X) (N := N) hX hN
  sigma_tail_block := by
    intro X N hX hN
    simpa [TailBlockFun.constQ, sigma_trunc_constQ0] using M.sigma_tail_block (X := X) (N := N) hX hN

end TailBlockFun
end AO_OffDiag
end Goldbach

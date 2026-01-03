import Goldbach.AO_OffDiag.EntryPoint
import Goldbach.AO_OffDiag.TailBlockFunCompat

namespace Goldbach
namespace AO_OffDiag

/-!
Compatibility shim: lift the existing fixed-`Q0` off-diagonal model into the
scale-dependent `TailBlockFun.Model` by taking `Q(X) = Q0`.

This is useful while the analytic derivation of the variable-`Q(X)` tail bound
is still being ported in parallel.
-/

open Goldbach.Windows

noncomputable def offDiagModelFun
  (hF : ∀ {X N : ℕ}, BankParams.X0 ≤ X → N ∈ EvenIn X BankParams.H →
    TailBlock.F_block N ≤ (330 : ℝ)) :
  TailBlockFun.Model :=
  TailBlockFun.model_to_fun (M := offDiagModel hF)

end AO_OffDiag
end Goldbach


import Goldbach.FiniteBase
import Goldbach.Base.FiniteBaseDefs
import Goldbach.Windows

namespace Goldbach

open Goldbach.Base
open Goldbach.Windows

namespace FiniteBase

/-- Convert a `FiniteBase.Cert X0` (IsEven-based) into `Base.FiniteBaseUpTo X0` (Even-based). -/
theorem cert_to_FiniteBaseUpTo {X0 : ℕ} (c : Goldbach.FiniteBase.Cert X0) :
    Goldbach.Base.FiniteBaseUpTo X0 := by
  intro N hEven h4 hNle
  have hIsEven : Goldbach.Windows.IsEven N := Goldbach.Windows.isEven_of_even hEven
  rcases c (N := N) hIsEven h4 hNle with ⟨p, q, hp, hq, hsum⟩
  exact ⟨p, q, hp, hq, hsum⟩

end FiniteBase
end Goldbach

import Goldbach.Cert.MajorArcStep11RLSmoothIntegralScaled
import Goldbach.Cert.MajorArcStep17MajorMinorSplit
import Goldbach.Cert.MajorArcStep22BetaKernelLocalization
import Goldbach.Cert.MajorArcStep26Q0MajorArcIntegral

/-!
`MajorArcModules/IntegralPipeline` re-exports the σ-agnostic major-arc integral infrastructure:

- the correlation integral object (`corr_integral`) and its link to `RΛ_smooth`,
- the major/minor split (`corr_integral_major`, `corr_integral_minor`),
- the β-kernel localization utilities (kernel cap + small-offset witness),
- the packaged `Q0`-major-arc extraction (`corr_integral_major_Q0` rewritten as a finite `(q,a)` sum).

This is part of the offline/turnkey “MajorArcModules” staging area.
-/

namespace Goldbach.Cert.MajorArcModules.IntegralPipeline

export Goldbach.Cert.MajorArcStep11RLSmoothIntegralScaled
  (corr_integral RΛ_smooth_cast_eq_norm_mul_corr_integral)

export Goldbach.Cert.MajorArcStep17MajorMinorSplit
  (innerIntegrand corr_integral_major corr_integral_minor corr_integral_eq_major_add_minor)

export Goldbach.Cert.MajorArcStep22BetaKernelLocalization
  (norm_integral_kernelPolyC_mul_le IsMajorArcTextbook.exists_witness_small)

export Goldbach.Cert.MajorArcStep26Q0MajorArcIntegral
  (innerMajorQ0 innerMajorQ0_eq_sum corr_integral_major_Q0 corr_integral_major_Q0_eq_sum)

end Goldbach.Cert.MajorArcModules.IntegralPipeline


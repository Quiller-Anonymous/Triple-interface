import Goldbach.Cert.MajorArcModules.BMOR
import Goldbach.Cert.MajorArcModules.PartialSummation
import Goldbach.Cert.MajorArcModules.Step2ExpSumsBMOR
import Goldbach.Cert.MajorArcModules.Step2MajorArcDecompBMOR
import Goldbach.Cert.MajorArcModules.Step3MajorArcDecompMuBMOR
import Goldbach.Cert.MajorArcModules.Step4FullExpSumBMOR
import Goldbach.Cert.MajorArcModules.Step5ExpSumApproxBMOR
import Goldbach.Cert.MajorArcModules.Step20BankExpSumApproxBMOR
import Goldbach.Cert.MajorArcModules.Step21QuadraticIntegrandControlBMOR
import Goldbach.Cert.MajorArcModules.Step21OnArcBMOR
import Goldbach.Cert.MajorArcModules.Step21OnArcSmallBetaBMOR
import Goldbach.Cert.MajorArcModules.IntegralPipeline
import Goldbach.Cert.MajorArcModules.BetaLocalization
import Goldbach.Cert.MajorArcModules.BetaRationalApprox
import Goldbach.Cert.MajorArcModules.CoprimePreservingApprox
import Goldbach.Cert.MajorArcModules.CoprimeShiftCertificate
import Goldbach.Cert.MajorArcModules.CoprimeShiftBoundQ0
import Goldbach.Cert.MajorArcModules.ArcSetBounds
import Goldbach.Cert.MajorArcModules.Q0MajorBoundSplit
import Goldbach.Cert.MajorArcModules.KernelTailCapBounds
import Goldbach.Cert.MajorArcModules.Q0MajorTailSpec
import Goldbach.Cert.MajorArcModules.Q0MajorTailCert
import Goldbach.Cert.MajorArcModules.Q0MajorTailCertData
import Goldbach.Cert.MajorArcModules.Q0MajorTailFromCert
import Goldbach.Cert.MajorArcModules.MainTermQ0
import Goldbach.Cert.MajorArcModules.CorrModel
import Goldbach.Cert.MajorArcModules.CorrIntegralQ0Reduction
import Goldbach.Cert.MajorArcModules.MinorQ0Bound
import Goldbach.Cert.MajorArcModules.Q0MinorBound
import Goldbach.Cert.MajorArcModules.Q0MinorEnergyLedger
import Goldbach.Cert.MajorArcModules.Q0MinorLedgerCert
import Goldbach.Cert.MajorArcModules.Q0MinorLedgerCertData
import Goldbach.Cert.MajorArcModules.Q0MinorEnergyFromLedgerCert
import Goldbach.Cert.MajorArcModules.Q0MajorBound
import Goldbach.Cert.MajorArcModules.Q0MajorBoundFromSplit
import Goldbach.Cert.MajorArcModules.Q0MajorRoute
import Goldbach.Cert.MajorArcModules.TurnkeyCanon
import Goldbach.Cert.MajorArcModules.TurnkeyFromCorrIntegral
import Goldbach.Cert.MajorArcModules.TurnkeyFromQ0
import Goldbach.Cert.MajorArcModules.Q0Certificate
import Goldbach.Cert.MajorArcModules.Q0CertData
import Goldbach.Cert.MajorArcModules.TurnkeyRouteQ0
import Goldbach.Cert.MajorArcModules.CertChecker
import Goldbach.Cert.MajorArcModules.NumericFacts
import Goldbach.Cert.MajorArcModules.Normalization
import Goldbach.Cert.MajorArcModules.Certificate

/-!
Convenience import for the offline/turnkey “MajorArcModules” staging area.

This file is **not** meant to be imported by the main Goldbach pipeline; it is an offline
workspace for building a future major-arc certificate without disrupting the live build.
-/

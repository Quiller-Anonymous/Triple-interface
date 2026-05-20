import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0TailPilot25

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

open scoped BigOperators

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

/- Generated direct-term certificate blocks for tail chunk 000, subchunk 000, blocks [118,119). -/

/- Block 118 covers tail-support indices [2950,2975) and q from 4898 to 4938. -/

def TailChunk000Sub000Block118Part000SupportExplicit : Finset ℕ :=
  ([4898] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block118Part000 : ℚ :=
  (3186804469 : ℚ) / 333202131100800

def SurrogateDiagonalTailChunk000Sub000Block118Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4898
    = surrogateDiagTailX0RatChunk000Sub000Block118Part000

theorem surrogateDiagonalTailChunk000Sub000Block118Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block118Part000CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block118Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block118Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block118Part000CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block118Part000SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block118Part000] using hcert

def TailChunk000Sub000Block118Part001SupportExplicit : Finset ℕ :=
  ([4899] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block118Part001 : ℚ :=
  (9437763571 : ℚ) / 2250244582924800

def SurrogateDiagonalTailChunk000Sub000Block118Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4899
    = surrogateDiagTailX0RatChunk000Sub000Block118Part001

theorem surrogateDiagonalTailChunk000Sub000Block118Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block118Part001CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block118Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block118Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block118Part001CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block118Part001SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block118Part001] using hcert

def TailChunk000Sub000Block118Part002SupportExplicit : Finset ℕ :=
  ([4902] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block118Part002 : ℚ :=
  (303292754525 : ℚ) / 6534374599517184

def SurrogateDiagonalTailChunk000Sub000Block118Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4902
    = surrogateDiagTailX0RatChunk000Sub000Block118Part002

theorem surrogateDiagonalTailChunk000Sub000Block118Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block118Part002CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block118Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block118Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block118Part002CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block118Part002SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block118Part002] using hcert

def TailChunk000Sub000Block118Part003SupportExplicit : Finset ℕ :=
  ([4903] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block118Part003 : ℚ :=
  (375615765625 : ℚ) / 360960845481559602

def SurrogateDiagonalTailChunk000Sub000Block118Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4903
    = surrogateDiagTailX0RatChunk000Sub000Block118Part003

theorem surrogateDiagonalTailChunk000Sub000Block118Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block118Part003CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block118Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block118Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block118Part003CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block118Part003SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block118Part003] using hcert

def TailChunk000Sub000Block118Part004SupportExplicit : Finset ℕ :=
  ([4906] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block118Part004 : ℚ :=
  (5447242229 : ℚ) / 485879687706240

def SurrogateDiagonalTailChunk000Sub000Block118Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4906
    = surrogateDiagTailX0RatChunk000Sub000Block118Part004

theorem surrogateDiagonalTailChunk000Sub000Block118Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block118Part004CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block118Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block118Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block118Part004CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block118Part004SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block118Part004] using hcert

def TailChunk000Sub000Block118Part005SupportExplicit : Finset ℕ :=
  ([4907] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block118Part005 : ℚ :=
  (81801869 : ℚ) / 49401878400000

def SurrogateDiagonalTailChunk000Sub000Block118Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4907
    = surrogateDiagTailX0RatChunk000Sub000Block118Part005

theorem surrogateDiagonalTailChunk000Sub000Block118Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block118Part005CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block118Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block118Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block118Part005CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block118Part005SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block118Part005] using hcert

def TailChunk000Sub000Block118Part006SupportExplicit : Finset ℕ :=
  ([4909] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block118Part006 : ℚ :=
  (376535640625 : ℚ) / 362731342936794912

def SurrogateDiagonalTailChunk000Sub000Block118Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4909
    = surrogateDiagTailX0RatChunk000Sub000Block118Part006

theorem surrogateDiagonalTailChunk000Sub000Block118Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block118Part006CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block118Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block118Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block118Part006CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block118Part006SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block118Part006] using hcert

def TailChunk000Sub000Block118Part007SupportExplicit : Finset ℕ :=
  ([4910] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block118Part007 : ℚ :=
  (1203237599 : ℚ) / 73804210690560

def SurrogateDiagonalTailChunk000Sub000Block118Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4910
    = surrogateDiagTailX0RatChunk000Sub000Block118Part007

theorem surrogateDiagonalTailChunk000Sub000Block118Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block118Part007CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block118Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block118Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block118Part007CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block118Part007SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block118Part007] using hcert

def TailChunk000Sub000Block118Part008SupportExplicit : Finset ℕ :=
  ([4911] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block118Part008 : ℚ :=
  (100431075 : ℚ) / 28654523352064

def SurrogateDiagonalTailChunk000Sub000Block118Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4911
    = surrogateDiagTailX0RatChunk000Sub000Block118Part008

theorem surrogateDiagonalTailChunk000Sub000Block118Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block118Part008CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block118Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block118Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block118Part008CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block118Part008SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block118Part008] using hcert

def TailChunk000Sub000Block118Part009SupportExplicit : Finset ℕ :=
  ([4915] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block118Part009 : ℚ :=
  (603448040375 : ℚ) / 297634163562046464

def SurrogateDiagonalTailChunk000Sub000Block118Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4915
    = surrogateDiagTailX0RatChunk000Sub000Block118Part009

theorem surrogateDiagonalTailChunk000Sub000Block118Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block118Part009CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block118Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block118Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block118Part009CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block118Part009SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block118Part009] using hcert

def TailChunk000Sub000Block118Part010SupportExplicit : Finset ℕ :=
  ([4917] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block118Part010 : ℚ :=
  (2430164301 : ℚ) / 511873251246080

def SurrogateDiagonalTailChunk000Sub000Block118Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4917
    = surrogateDiagTailX0RatChunk000Sub000Block118Part010

theorem surrogateDiagonalTailChunk000Sub000Block118Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block118Part010CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block118Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block118Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block118Part010CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block118Part010SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block118Part010] using hcert

def TailChunk000Sub000Block118Part011SupportExplicit : Finset ℕ :=
  ([4918] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block118Part011 : ℚ :=
  (755683957975 : ℚ) / 91275532035355848

def SurrogateDiagonalTailChunk000Sub000Block118Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4918
    = surrogateDiagTailX0RatChunk000Sub000Block118Part011

theorem surrogateDiagonalTailChunk000Sub000Block118Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block118Part011CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block118Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block118Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block118Part011CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block118Part011SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block118Part011] using hcert

def TailChunk000Sub000Block118Part012SupportExplicit : Finset ℕ :=
  ([4919] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block118Part012 : ℚ :=
  (378071265625 : ℚ) / 365696635859841522

def SurrogateDiagonalTailChunk000Sub000Block118Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4919
    = surrogateDiagTailX0RatChunk000Sub000Block118Part012

theorem surrogateDiagonalTailChunk000Sub000Block118Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block118Part012CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block118Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block118Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block118Part012CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block118Part012SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block118Part012] using hcert

def TailChunk000Sub000Block118Part013SupportExplicit : Finset ℕ :=
  ([4921] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block118Part013 : ℚ :=
  (132923736925 : ℚ) / 63487667912343552

def SurrogateDiagonalTailChunk000Sub000Block118Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4921
    = surrogateDiagTailX0RatChunk000Sub000Block118Part013

theorem surrogateDiagonalTailChunk000Sub000Block118Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block118Part013CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block118Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block118Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block118Part013CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block118Part013SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block118Part013] using hcert

def TailChunk000Sub000Block118Part014SupportExplicit : Finset ℕ :=
  ([4922] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block118Part014 : ℚ :=
  (718322705725 : ℚ) / 73950487825577088

def SurrogateDiagonalTailChunk000Sub000Block118Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4922
    = surrogateDiagTailX0RatChunk000Sub000Block118Part014

theorem surrogateDiagonalTailChunk000Sub000Block118Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block118Part014CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block118Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block118Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block118Part014CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block118Part014SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block118Part014] using hcert

def TailChunk000Sub000Block118Part015SupportExplicit : Finset ℕ :=
  ([4926] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block118Part015 : ℚ :=
  (807879 : ℚ) / 28935792640

def SurrogateDiagonalTailChunk000Sub000Block118Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4926
    = surrogateDiagTailX0RatChunk000Sub000Block118Part015

theorem surrogateDiagonalTailChunk000Sub000Block118Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block118Part015CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block118Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block118Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block118Part015CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block118Part015SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block118Part015] using hcert

def TailChunk000Sub000Block118Part016SupportExplicit : Finset ℕ :=
  ([4927] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block118Part016 : ℚ :=
  (698571061175 : ℚ) / 529284342560891904

def SurrogateDiagonalTailChunk000Sub000Block118Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4927
    = surrogateDiagTailX0RatChunk000Sub000Block118Part016

theorem surrogateDiagonalTailChunk000Sub000Block118Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block118Part016CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block118Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block118Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block118Part016CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block118Part016SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block118Part016] using hcert

def TailChunk000Sub000Block118Part017SupportExplicit : Finset ℕ :=
  ([4929] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block118Part017 : ℚ :=
  (12833093263 : ℚ) / 3159249835622400

def SurrogateDiagonalTailChunk000Sub000Block118Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4929
    = surrogateDiagTailX0RatChunk000Sub000Block118Part017

theorem surrogateDiagonalTailChunk000Sub000Block118Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block118Part017CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block118Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block118Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block118Part017CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block118Part017SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block118Part017] using hcert

def TailChunk000Sub000Block118Part018SupportExplicit : Finset ℕ :=
  ([4930] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block118Part018 : ℚ :=
  (184229892675 : ℚ) / 8595232434159616

def SurrogateDiagonalTailChunk000Sub000Block118Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4930
    = surrogateDiagTailX0RatChunk000Sub000Block118Part018

theorem surrogateDiagonalTailChunk000Sub000Block118Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block118Part018CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block118Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block118Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block118Part018CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block118Part018SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block118Part018] using hcert

def TailChunk000Sub000Block118Part019SupportExplicit : Finset ℕ :=
  ([4931] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block118Part019 : ℚ :=
  (607869025 : ℚ) / 590846309642802

def SurrogateDiagonalTailChunk000Sub000Block118Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4931
    = surrogateDiagTailX0RatChunk000Sub000Block118Part019

theorem surrogateDiagonalTailChunk000Sub000Block118Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block118Part019CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block118Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block118Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block118Part019CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block118Part019SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block118Part019] using hcert

def TailChunk000Sub000Block118Part020SupportExplicit : Finset ℕ :=
  ([4933] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block118Part020 : ℚ :=
  (380226390625 : ℚ) / 369878543879952672

def SurrogateDiagonalTailChunk000Sub000Block118Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4933
    = surrogateDiagTailX0RatChunk000Sub000Block118Part020

theorem surrogateDiagonalTailChunk000Sub000Block118Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block118Part020CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block118Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block118Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block118Part020CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block118Part020SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block118Part020] using hcert

def TailChunk000Sub000Block118Part021SupportExplicit : Finset ℕ :=
  ([4934] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block118Part021 : ℚ :=
  (760608972775 : ℚ) / 92469635969988168

def SurrogateDiagonalTailChunk000Sub000Block118Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4934
    = surrogateDiagTailX0RatChunk000Sub000Block118Part021

theorem surrogateDiagonalTailChunk000Sub000Block118Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block118Part021CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block118Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block118Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block118Part021CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block118Part021SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block118Part021] using hcert

def TailChunk000Sub000Block118Part022SupportExplicit : Finset ℕ :=
  ([4935] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block118Part022 : ℚ :=
  (340767211925 : ℚ) / 29716190886887424

def SurrogateDiagonalTailChunk000Sub000Block118Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4935
    = surrogateDiagTailX0RatChunk000Sub000Block118Part022

theorem surrogateDiagonalTailChunk000Sub000Block118Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block118Part022CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block118Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block118Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block118Part022CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block118Part022SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block118Part022] using hcert

def TailChunk000Sub000Block118Part023SupportExplicit : Finset ℕ :=
  ([4937] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block118Part023 : ℚ :=
  (380843265625 : ℚ) / 371079934832497152

def SurrogateDiagonalTailChunk000Sub000Block118Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4937
    = surrogateDiagTailX0RatChunk000Sub000Block118Part023

theorem surrogateDiagonalTailChunk000Sub000Block118Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block118Part023CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block118Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block118Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block118Part023CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block118Part023SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block118Part023] using hcert

def TailChunk000Sub000Block118Part024SupportExplicit : Finset ℕ :=
  ([4938] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block118Part024 : ℚ :=
  (3758425 : ℚ) / 135273738624

def SurrogateDiagonalTailChunk000Sub000Block118Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4938
    = surrogateDiagTailX0RatChunk000Sub000Block118Part024

theorem surrogateDiagonalTailChunk000Sub000Block118Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block118Part024CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block118Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block118Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block118Part024CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block118Part024SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block118Part024] using hcert

def surrogateDiagonalTailChunk000Sub000Block118HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block118Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block118Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block118Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block118Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block118Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block118Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block118Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block118Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block118Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block118Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block118Head : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block118Part000
    + surrogateDiagTailX0RatChunk000Sub000Block118Part001
    + surrogateDiagTailX0RatChunk000Sub000Block118Part002
    + surrogateDiagTailX0RatChunk000Sub000Block118Part003
    + surrogateDiagTailX0RatChunk000Sub000Block118Part004
    + surrogateDiagTailX0RatChunk000Sub000Block118Part005
    + surrogateDiagTailX0RatChunk000Sub000Block118Part006
    + surrogateDiagTailX0RatChunk000Sub000Block118Part007
    + surrogateDiagTailX0RatChunk000Sub000Block118Part008
    + surrogateDiagTailX0RatChunk000Sub000Block118Part009

def surrogateDiagonalTailChunk000Sub000Block118MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block118Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block118Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block118Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block118Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block118Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block118Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block118Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block118Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block118Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block118Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block118Mid : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block118Part010
    + surrogateDiagTailX0RatChunk000Sub000Block118Part011
    + surrogateDiagTailX0RatChunk000Sub000Block118Part012
    + surrogateDiagTailX0RatChunk000Sub000Block118Part013
    + surrogateDiagTailX0RatChunk000Sub000Block118Part014
    + surrogateDiagTailX0RatChunk000Sub000Block118Part015
    + surrogateDiagTailX0RatChunk000Sub000Block118Part016
    + surrogateDiagTailX0RatChunk000Sub000Block118Part017
    + surrogateDiagTailX0RatChunk000Sub000Block118Part018
    + surrogateDiagTailX0RatChunk000Sub000Block118Part019

def surrogateDiagonalTailChunk000Sub000Block118TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block118Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block118Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block118Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block118Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block118Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block118Tail : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block118Part020
    + surrogateDiagTailX0RatChunk000Sub000Block118Part021
    + surrogateDiagTailX0RatChunk000Sub000Block118Part022
    + surrogateDiagTailX0RatChunk000Sub000Block118Part023
    + surrogateDiagTailX0RatChunk000Sub000Block118Part024

def surrogateDiagonalTailChunk000Sub000Block118Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub000Block118HeadSum X0
    + surrogateDiagonalTailChunk000Sub000Block118MidSum X0
    + surrogateDiagonalTailChunk000Sub000Block118TailSum X0

def surrogateDiagTailX0RatChunk000Sub000Block118 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block118Part000
    + surrogateDiagTailX0RatChunk000Sub000Block118Part001
    + surrogateDiagTailX0RatChunk000Sub000Block118Part002
    + surrogateDiagTailX0RatChunk000Sub000Block118Part003
    + surrogateDiagTailX0RatChunk000Sub000Block118Part004
    + surrogateDiagTailX0RatChunk000Sub000Block118Part005
    + surrogateDiagTailX0RatChunk000Sub000Block118Part006
    + surrogateDiagTailX0RatChunk000Sub000Block118Part007
    + surrogateDiagTailX0RatChunk000Sub000Block118Part008
    + surrogateDiagTailX0RatChunk000Sub000Block118Part009
    + surrogateDiagTailX0RatChunk000Sub000Block118Part010
    + surrogateDiagTailX0RatChunk000Sub000Block118Part011
    + surrogateDiagTailX0RatChunk000Sub000Block118Part012
    + surrogateDiagTailX0RatChunk000Sub000Block118Part013
    + surrogateDiagTailX0RatChunk000Sub000Block118Part014
    + surrogateDiagTailX0RatChunk000Sub000Block118Part015
    + surrogateDiagTailX0RatChunk000Sub000Block118Part016
    + surrogateDiagTailX0RatChunk000Sub000Block118Part017
    + surrogateDiagTailX0RatChunk000Sub000Block118Part018
    + surrogateDiagTailX0RatChunk000Sub000Block118Part019
    + surrogateDiagTailX0RatChunk000Sub000Block118Part020
    + surrogateDiagTailX0RatChunk000Sub000Block118Part021
    + surrogateDiagTailX0RatChunk000Sub000Block118Part022
    + surrogateDiagTailX0RatChunk000Sub000Block118Part023
    + surrogateDiagTailX0RatChunk000Sub000Block118Part024

theorem surrogateDiagTailX0RatChunk000Sub000Block118_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk000Sub000Block118Head + surrogateDiagTailX0RatChunk000Sub000Block118Mid + surrogateDiagTailX0RatChunk000Sub000Block118Tail =
      surrogateDiagTailX0RatChunk000Sub000Block118 := by
  unfold surrogateDiagTailX0RatChunk000Sub000Block118Head surrogateDiagTailX0RatChunk000Sub000Block118Mid surrogateDiagTailX0RatChunk000Sub000Block118Tail surrogateDiagTailX0RatChunk000Sub000Block118
  ring

def SurrogateDiagonalTailChunk000Sub000Block118HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block118HeadSum X0 = surrogateDiagTailX0RatChunk000Sub000Block118Head

def SurrogateDiagonalTailChunk000Sub000Block118MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block118MidSum X0 = surrogateDiagTailX0RatChunk000Sub000Block118Mid

def SurrogateDiagonalTailChunk000Sub000Block118TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block118TailSum X0 = surrogateDiagTailX0RatChunk000Sub000Block118Tail

theorem surrogateDiagonalTailChunk000Sub000Block118_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk000Sub000Block118HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk000Sub000Block118MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk000Sub000Block118TailCertificateAt X0) :
    surrogateDiagonalTailChunk000Sub000Block118Sum X0 = surrogateDiagTailX0RatChunk000Sub000Block118 := by
  unfold SurrogateDiagonalTailChunk000Sub000Block118HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk000Sub000Block118MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk000Sub000Block118TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk000Sub000Block118Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk000Sub000Block118_eq_head_add_mid_add_tail

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

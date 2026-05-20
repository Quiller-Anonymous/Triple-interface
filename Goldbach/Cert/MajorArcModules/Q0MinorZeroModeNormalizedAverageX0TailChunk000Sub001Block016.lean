import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0TailPilot25

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

open scoped BigOperators

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

/- Generated direct-term certificate blocks for tail chunk 000, subchunk 001, blocks [16,17). -/

/-- Block 016 covers tail-support indices [5400,5425) and q from 8926 to 8969. -/

def TailChunk000Sub001Block016Part000SupportExplicit : Finset ℕ :=
  ([8926] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block016Part000 : ℚ :=
  (311224515625 : ℚ) / 247790773488258642

def SurrogateDiagonalTailChunk000Sub001Block016Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8926
    = surrogateDiagTailX0RatChunk000Sub001Block016Part000

theorem surrogateDiagonalTailChunk000Sub001Block016Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block016Part000CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block016Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block016Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block016Part000CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block016Part000SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block016Part000] using hcert

def TailChunk000Sub001Block016Part001SupportExplicit : Finset ℕ :=
  ([8927] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block016Part001 : ℚ :=
  (26116975 : ℚ) / 6421467814035456

def SurrogateDiagonalTailChunk000Sub001Block016Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8927
    = surrogateDiagTailX0RatChunk000Sub001Block016Part001

theorem surrogateDiagonalTailChunk000Sub001Block016Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block016Part001CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block016Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block016Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block016Part001CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block016Part001SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block016Part001] using hcert

def TailChunk000Sub001Block016Part002SupportExplicit : Finset ℕ :=
  ([8929] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block016Part002 : ℚ :=
  (1245735015625 : ℚ) / 3971765452967903232

def SurrogateDiagonalTailChunk000Sub001Block016Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8929
    = surrogateDiagTailX0RatChunk000Sub001Block016Part002

theorem surrogateDiagonalTailChunk000Sub001Block016Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block016Part002CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block016Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block016Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block016Part002CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block016Part002SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block016Part002] using hcert

def TailChunk000Sub001Block016Part003SupportExplicit : Finset ℕ :=
  ([8930] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block016Part003 : ℚ :=
  (807593738375 : ℚ) / 150438216364867584

def SurrogateDiagonalTailChunk000Sub001Block016Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8930
    = surrogateDiagTailX0RatChunk000Sub001Block016Part003

theorem surrogateDiagonalTailChunk000Sub001Block016Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block016Part003CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block016Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block016Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block016Part003CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block016Part003SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block016Part003] using hcert

def TailChunk000Sub001Block016Part004SupportExplicit : Finset ℕ :=
  ([8931] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block016Part004 : ℚ :=
  (68898759725 : ℚ) / 62274279703707648

def SurrogateDiagonalTailChunk000Sub001Block016Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8931
    = surrogateDiagTailX0RatChunk000Sub001Block016Part004

theorem surrogateDiagonalTailChunk000Sub001Block016Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block016Part004CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block016Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block016Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block016Part004CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block016Part004SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block016Part004] using hcert

def TailChunk000Sub001Block016Part005SupportExplicit : Finset ℕ :=
  ([8933] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block016Part005 : ℚ :=
  (1246851390625 : ℚ) / 3978888097139088672

def SurrogateDiagonalTailChunk000Sub001Block016Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8933
    = surrogateDiagTailX0RatChunk000Sub001Block016Part005

theorem surrogateDiagonalTailChunk000Sub001Block016Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block016Part005CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block016Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block016Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block016Part005CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block016Part005SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block016Part005] using hcert

def TailChunk000Sub001Block016Part006SupportExplicit : Finset ℕ :=
  ([8934] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block016Part006 : ℚ :=
  (692315268425 : ℚ) / 98068282789330944

def SurrogateDiagonalTailChunk000Sub001Block016Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8934
    = surrogateDiagTailX0RatChunk000Sub001Block016Part006

theorem surrogateDiagonalTailChunk000Sub001Block016Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block016Part006CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block016Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block016Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block016Part006CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block016Part006SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block016Part006] using hcert

def TailChunk000Sub001Block016Part007SupportExplicit : Finset ℕ :=
  ([8935] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block016Part007 : ℚ :=
  (1196776339275 : ℚ) / 2171057809348335616

def SurrogateDiagonalTailChunk000Sub001Block016Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8935
    = surrogateDiagTailX0RatChunk000Sub001Block016Part007

theorem surrogateDiagonalTailChunk000Sub001Block016Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block016Part007CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block016Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block016Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block016Part007CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block016Part007SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block016Part007] using hcert

def TailChunk000Sub001Block016Part008SupportExplicit : Finset ℕ :=
  ([8938] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block016Part008 : ℚ :=
  (95098449961 : ℚ) / 34835483079475200

def SurrogateDiagonalTailChunk000Sub001Block016Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8938
    = surrogateDiagTailX0RatChunk000Sub001Block016Part008

theorem surrogateDiagonalTailChunk000Sub001Block016Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block016Part008CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block016Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block016Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block016Part008CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block016Part008SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block016Part008] using hcert

def TailChunk000Sub001Block016Part009SupportExplicit : Finset ℕ :=
  ([8939] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block016Part009 : ℚ :=
  (220620075875 : ℚ) / 477267710110811136

def SurrogateDiagonalTailChunk000Sub001Block016Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8939
    = surrogateDiagTailX0RatChunk000Sub001Block016Part009

theorem surrogateDiagonalTailChunk000Sub001Block016Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block016Part009CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block016Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block016Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block016Part009CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block016Part009SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block016Part009] using hcert

def TailChunk000Sub001Block016Part010SupportExplicit : Finset ℕ :=
  ([8941] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block016Part010 : ℚ :=
  (1998537025 : ℚ) / 6389059393327392

def SurrogateDiagonalTailChunk000Sub001Block016Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8941
    = surrogateDiagTailX0RatChunk000Sub001Block016Part010

theorem surrogateDiagonalTailChunk000Sub001Block016Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block016Part010CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block016Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block016Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block016Part010CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block016Part010SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block016Part010] using hcert

def TailChunk000Sub001Block016Part011SupportExplicit : Finset ℕ :=
  ([8942] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block016Part011 : ℚ :=
  (295185561325 : ℚ) / 193042068920205312

def SurrogateDiagonalTailChunk000Sub001Block016Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8942
    = surrogateDiagTailX0RatChunk000Sub001Block016Part011

theorem surrogateDiagonalTailChunk000Sub001Block016Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block016Part011CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block016Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block016Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block016Part011CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block016Part011SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block016Part011] using hcert

def TailChunk000Sub001Block016Part012SupportExplicit : Finset ℕ :=
  ([8943] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block016Part012 : ℚ :=
  (1078209937 : ℚ) / 944972956800000

def SurrogateDiagonalTailChunk000Sub001Block016Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8943
    = surrogateDiagTailX0RatChunk000Sub001Block016Part012

theorem surrogateDiagonalTailChunk000Sub001Block016Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block016Part012CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block016Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block016Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block016Part012CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block016Part012SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block016Part012] using hcert

def TailChunk000Sub001Block016Part013SupportExplicit : Finset ℕ :=
  ([8945] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block016Part013 : ℚ :=
  (3598371768925 : ℚ) / 6542396818767249408

def SurrogateDiagonalTailChunk000Sub001Block016Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8945
    = surrogateDiagTailX0RatChunk000Sub001Block016Part013

theorem surrogateDiagonalTailChunk000Sub001Block016Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block016Part013CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block016Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block016Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block016Part013CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block016Part013SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block016Part013] using hcert

def TailChunk000Sub001Block016Part014SupportExplicit : Finset ℕ :=
  ([8947] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block016Part014 : ℚ :=
  (779073477375 : ℚ) / 2212550714985171968

def SurrogateDiagonalTailChunk000Sub001Block016Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8947
    = surrogateDiagTailX0RatChunk000Sub001Block016Part014

theorem surrogateDiagonalTailChunk000Sub001Block016Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block016Part014CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block016Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block016Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block016Part014CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block016Part014SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block016Part014] using hcert

def TailChunk000Sub001Block016Part015SupportExplicit : Finset ℕ :=
  ([8949] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block016Part015 : ℚ :=
  (2566853734675 : ℚ) / 2487340580582227968

def SurrogateDiagonalTailChunk000Sub001Block016Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8949
    = surrogateDiagTailX0RatChunk000Sub001Block016Part015

theorem surrogateDiagonalTailChunk000Sub001Block016Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block016Part015CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block016Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block016Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block016Part015CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block016Part015SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block016Part015] using hcert

def TailChunk000Sub001Block016Part016SupportExplicit : Finset ℕ :=
  ([8951] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block016Part016 : ℚ :=
  (80120401 : ℚ) / 256707751534050

def SurrogateDiagonalTailChunk000Sub001Block016Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8951
    = surrogateDiagTailX0RatChunk000Sub001Block016Part016

theorem surrogateDiagonalTailChunk000Sub001Block016Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block016Part016CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block016Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block016Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block016Part016CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block016Part016SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block016Part016] using hcert

def TailChunk000Sub001Block016Part017SupportExplicit : Finset ℕ :=
  ([8953] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block016Part017 : ℚ :=
  (221311890575 : ℚ) / 480267026636567616

def SurrogateDiagonalTailChunk000Sub001Block016Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8953
    = surrogateDiagTailX0RatChunk000Sub001Block016Part017

theorem surrogateDiagonalTailChunk000Sub001Block016Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block016Part017CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block016Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block016Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block016Part017CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block016Part017SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block016Part017] using hcert

def TailChunk000Sub001Block016Part018SupportExplicit : Finset ℕ :=
  ([8958] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block016Part018 : ℚ :=
  (974694729925 : ℚ) / 198254080171296768

def SurrogateDiagonalTailChunk000Sub001Block016Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8958
    = surrogateDiagTailX0RatChunk000Sub001Block016Part018

theorem surrogateDiagonalTailChunk000Sub001Block016Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block016Part018CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block016Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block016Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block016Part018CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block016Part018SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block016Part018] using hcert

def TailChunk000Sub001Block016Part019SupportExplicit : Finset ℕ :=
  ([8961] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block016Part019 : ℚ :=
  (1312862054675 : ℚ) / 1330912972842614784

def SurrogateDiagonalTailChunk000Sub001Block016Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8961
    = surrogateDiagTailX0RatChunk000Sub001Block016Part019

theorem surrogateDiagonalTailChunk000Sub001Block016Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block016Part019CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block016Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block016Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block016Part019CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block016Part019SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block016Part019] using hcert

def TailChunk000Sub001Block016Part020SupportExplicit : Finset ℕ :=
  ([8962] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block016Part020 : ℚ :=
  (501984025 : ℚ) / 402901520351232

def SurrogateDiagonalTailChunk000Sub001Block016Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8962
    = surrogateDiagTailX0RatChunk000Sub001Block016Part020

theorem surrogateDiagonalTailChunk000Sub001Block016Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block016Part020CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block016Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block016Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block016Part020CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block016Part020SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block016Part020] using hcert

def TailChunk000Sub001Block016Part021SupportExplicit : Finset ℕ :=
  ([8963] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block016Part021 : ℚ :=
  (1255240140625 : ℚ) / 4032613743159546642

def SurrogateDiagonalTailChunk000Sub001Block016Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8963
    = surrogateDiagTailX0RatChunk000Sub001Block016Part021

theorem surrogateDiagonalTailChunk000Sub001Block016Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block016Part021CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block016Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block016Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block016Part021CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block016Part021SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block016Part021] using hcert

def TailChunk000Sub001Block016Part022SupportExplicit : Finset ℕ :=
  ([8965] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block016Part022 : ℚ :=
  (10447465859 : ℚ) / 14696219424153600

def SurrogateDiagonalTailChunk000Sub001Block016Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8965
    = surrogateDiagTailX0RatChunk000Sub001Block016Part022

theorem surrogateDiagonalTailChunk000Sub001Block016Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block016Part022CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block016Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block016Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block016Part022CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block016Part022SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block016Part022] using hcert

def TailChunk000Sub001Block016Part023SupportExplicit : Finset ℕ :=
  ([8966] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block016Part023 : ℚ :=
  (314020140625 : ℚ) / 252263418300751122

def SurrogateDiagonalTailChunk000Sub001Block016Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8966
    = surrogateDiagTailX0RatChunk000Sub001Block016Part023

theorem surrogateDiagonalTailChunk000Sub001Block016Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block016Part023CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block016Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block016Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block016Part023CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block016Part023SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block016Part023] using hcert

def TailChunk000Sub001Block016Part024SupportExplicit : Finset ℕ :=
  ([8969] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block016Part024 : ℚ :=
  (1256921265625 : ℚ) / 4043423826436035072

def SurrogateDiagonalTailChunk000Sub001Block016Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8969
    = surrogateDiagTailX0RatChunk000Sub001Block016Part024

theorem surrogateDiagonalTailChunk000Sub001Block016Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block016Part024CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block016Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block016Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block016Part024CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block016Part024SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block016Part024] using hcert

def surrogateDiagonalTailChunk000Sub001Block016HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block016Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block016Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block016Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block016Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block016Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block016Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block016Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block016Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block016Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block016Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block016Head : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block016Part000
    + surrogateDiagTailX0RatChunk000Sub001Block016Part001
    + surrogateDiagTailX0RatChunk000Sub001Block016Part002
    + surrogateDiagTailX0RatChunk000Sub001Block016Part003
    + surrogateDiagTailX0RatChunk000Sub001Block016Part004
    + surrogateDiagTailX0RatChunk000Sub001Block016Part005
    + surrogateDiagTailX0RatChunk000Sub001Block016Part006
    + surrogateDiagTailX0RatChunk000Sub001Block016Part007
    + surrogateDiagTailX0RatChunk000Sub001Block016Part008
    + surrogateDiagTailX0RatChunk000Sub001Block016Part009

def surrogateDiagonalTailChunk000Sub001Block016MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block016Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block016Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block016Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block016Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block016Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block016Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block016Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block016Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block016Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block016Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block016Mid : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block016Part010
    + surrogateDiagTailX0RatChunk000Sub001Block016Part011
    + surrogateDiagTailX0RatChunk000Sub001Block016Part012
    + surrogateDiagTailX0RatChunk000Sub001Block016Part013
    + surrogateDiagTailX0RatChunk000Sub001Block016Part014
    + surrogateDiagTailX0RatChunk000Sub001Block016Part015
    + surrogateDiagTailX0RatChunk000Sub001Block016Part016
    + surrogateDiagTailX0RatChunk000Sub001Block016Part017
    + surrogateDiagTailX0RatChunk000Sub001Block016Part018
    + surrogateDiagTailX0RatChunk000Sub001Block016Part019

def surrogateDiagonalTailChunk000Sub001Block016TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block016Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block016Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block016Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block016Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block016Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block016Tail : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block016Part020
    + surrogateDiagTailX0RatChunk000Sub001Block016Part021
    + surrogateDiagTailX0RatChunk000Sub001Block016Part022
    + surrogateDiagTailX0RatChunk000Sub001Block016Part023
    + surrogateDiagTailX0RatChunk000Sub001Block016Part024

def surrogateDiagonalTailChunk000Sub001Block016Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub001Block016HeadSum X0
    + surrogateDiagonalTailChunk000Sub001Block016MidSum X0
    + surrogateDiagonalTailChunk000Sub001Block016TailSum X0

def surrogateDiagTailX0RatChunk000Sub001Block016 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block016Part000
    + surrogateDiagTailX0RatChunk000Sub001Block016Part001
    + surrogateDiagTailX0RatChunk000Sub001Block016Part002
    + surrogateDiagTailX0RatChunk000Sub001Block016Part003
    + surrogateDiagTailX0RatChunk000Sub001Block016Part004
    + surrogateDiagTailX0RatChunk000Sub001Block016Part005
    + surrogateDiagTailX0RatChunk000Sub001Block016Part006
    + surrogateDiagTailX0RatChunk000Sub001Block016Part007
    + surrogateDiagTailX0RatChunk000Sub001Block016Part008
    + surrogateDiagTailX0RatChunk000Sub001Block016Part009
    + surrogateDiagTailX0RatChunk000Sub001Block016Part010
    + surrogateDiagTailX0RatChunk000Sub001Block016Part011
    + surrogateDiagTailX0RatChunk000Sub001Block016Part012
    + surrogateDiagTailX0RatChunk000Sub001Block016Part013
    + surrogateDiagTailX0RatChunk000Sub001Block016Part014
    + surrogateDiagTailX0RatChunk000Sub001Block016Part015
    + surrogateDiagTailX0RatChunk000Sub001Block016Part016
    + surrogateDiagTailX0RatChunk000Sub001Block016Part017
    + surrogateDiagTailX0RatChunk000Sub001Block016Part018
    + surrogateDiagTailX0RatChunk000Sub001Block016Part019
    + surrogateDiagTailX0RatChunk000Sub001Block016Part020
    + surrogateDiagTailX0RatChunk000Sub001Block016Part021
    + surrogateDiagTailX0RatChunk000Sub001Block016Part022
    + surrogateDiagTailX0RatChunk000Sub001Block016Part023
    + surrogateDiagTailX0RatChunk000Sub001Block016Part024

theorem surrogateDiagTailX0RatChunk000Sub001Block016_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk000Sub001Block016Head + surrogateDiagTailX0RatChunk000Sub001Block016Mid + surrogateDiagTailX0RatChunk000Sub001Block016Tail =
      surrogateDiagTailX0RatChunk000Sub001Block016 := by
  unfold surrogateDiagTailX0RatChunk000Sub001Block016Head surrogateDiagTailX0RatChunk000Sub001Block016Mid surrogateDiagTailX0RatChunk000Sub001Block016Tail surrogateDiagTailX0RatChunk000Sub001Block016
  ring

def SurrogateDiagonalTailChunk000Sub001Block016HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block016HeadSum X0 = surrogateDiagTailX0RatChunk000Sub001Block016Head

def SurrogateDiagonalTailChunk000Sub001Block016MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block016MidSum X0 = surrogateDiagTailX0RatChunk000Sub001Block016Mid

def SurrogateDiagonalTailChunk000Sub001Block016TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block016TailSum X0 = surrogateDiagTailX0RatChunk000Sub001Block016Tail

theorem surrogateDiagonalTailChunk000Sub001Block016_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk000Sub001Block016HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk000Sub001Block016MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk000Sub001Block016TailCertificateAt X0) :
    surrogateDiagonalTailChunk000Sub001Block016Sum X0 = surrogateDiagTailX0RatChunk000Sub001Block016 := by
  unfold SurrogateDiagonalTailChunk000Sub001Block016HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk000Sub001Block016MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk000Sub001Block016TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk000Sub001Block016Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk000Sub001Block016_eq_head_add_mid_add_tail

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0TailPilot25

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

open scoped BigOperators

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

/- Generated direct-term certificate blocks for tail chunk 000, subchunk 000, blocks [170,180). -/

/-- Block 170 covers tail-support indices [4250,4275) and q from 7045 to 7085. -/

def TailChunk000Sub000Block170Part000SupportExplicit : Finset ℕ :=
  ([7045] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block170Part000 : ℚ :=
  (1177936111175 : ℚ) / 1257903854079442944

def SurrogateDiagonalTailChunk000Sub000Block170Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7045
    = surrogateDiagTailX0RatChunk000Sub000Block170Part000

theorem surrogateDiagonalTailChunk000Sub000Block170Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block170Part000CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block170Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block170Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block170Part000CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block170Part000SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block170Part000] using hcert

def TailChunk000Sub000Block170Part001SupportExplicit : Finset ℕ :=
  ([7046] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block170Part001 : ℚ :=
  (13890537307 : ℚ) / 2755541142028800

def SurrogateDiagonalTailChunk000Sub000Block170Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7046
    = surrogateDiagTailX0RatChunk000Sub000Block170Part001

theorem surrogateDiagonalTailChunk000Sub000Block170Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block170Part001CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block170Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block170Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block170Part001CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block170Part001SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block170Part001] using hcert

def TailChunk000Sub000Block170Part002SupportExplicit : Finset ℕ :=
  ([7049] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block170Part002 : ℚ :=
  (578811000175 : ℚ) / 621835145145556992

def SurrogateDiagonalTailChunk000Sub000Block170Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7049
    = surrogateDiagTailX0RatChunk000Sub000Block170Part002

theorem surrogateDiagonalTailChunk000Sub000Block170Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block170Part002CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block170Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block170Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block170Part002CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block170Part002SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block170Part002] using hcert

def TailChunk000Sub000Block170Part003SupportExplicit : Finset ℕ :=
  ([7051] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block170Part003 : ℚ :=
  (10868730697 : ℚ) / 16780571443200000

def SurrogateDiagonalTailChunk000Sub000Block170Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7051
    = surrogateDiagTailX0RatChunk000Sub000Block170Part003

theorem surrogateDiagonalTailChunk000Sub000Block170Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block170Part003CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block170Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block170Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block170Part003CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block170Part003SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block170Part003] using hcert

def TailChunk000Sub000Block170Part004SupportExplicit : Finset ℕ :=
  ([7053] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block170Part004 : ℚ :=
  (17266822537 : ℚ) / 12201642340500000

def SurrogateDiagonalTailChunk000Sub000Block170Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7053
    = surrogateDiagTailX0RatChunk000Sub000Block170Part004

theorem surrogateDiagonalTailChunk000Sub000Block170Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block170Part004CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block170Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block170Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block170Part004CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block170Part004SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block170Part004] using hcert

def TailChunk000Sub000Block170Part005SupportExplicit : Finset ℕ :=
  ([7054] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block170Part005 : ℚ :=
  (1554655131775 : ℚ) / 386505867018700488

def SurrogateDiagonalTailChunk000Sub000Block170Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7054
    = surrogateDiagTailX0RatChunk000Sub000Block170Part005

theorem surrogateDiagonalTailChunk000Sub000Block170Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block170Part005CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block170Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block170Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block170Part005CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block170Part005SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block170Part005] using hcert

def TailChunk000Sub000Block170Part006SupportExplicit : Finset ℕ :=
  ([7055] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block170Part006 : ℚ :=
  (2049858215875 : ℚ) / 1896715373676331008

def SurrogateDiagonalTailChunk000Sub000Block170Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7055
    = surrogateDiagTailX0RatChunk000Sub000Block170Part006

theorem surrogateDiagonalTailChunk000Sub000Block170Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block170Part006CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block170Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block170Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block170Part006CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block170Part006SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block170Part006] using hcert

def TailChunk000Sub000Block170Part007SupportExplicit : Finset ℕ :=
  ([7057] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block170Part007 : ℚ :=
  (778144515625 : ℚ) / 1549534164290445312

def SurrogateDiagonalTailChunk000Sub000Block170Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7057
    = surrogateDiagTailX0RatChunk000Sub000Block170Part007

theorem surrogateDiagonalTailChunk000Sub000Block170Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block170Part007CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block170Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block170Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block170Part007CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block170Part007SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block170Part007] using hcert

def TailChunk000Sub000Block170Part008SupportExplicit : Finset ℕ :=
  ([7058] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block170Part008 : ℚ :=
  (1556418778975 : ℚ) / 387383541072611328

def SurrogateDiagonalTailChunk000Sub000Block170Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7058
    = surrogateDiagTailX0RatChunk000Sub000Block170Part008

theorem surrogateDiagonalTailChunk000Sub000Block170Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block170Part008CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block170Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block170Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block170Part008CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block170Part008SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block170Part008] using hcert

def TailChunk000Sub000Block170Part009SupportExplicit : Finset ℕ :=
  ([7059] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block170Part009 : ℚ :=
  (699128491 : ℚ) / 387060923105280

def SurrogateDiagonalTailChunk000Sub000Block170Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7059
    = surrogateDiagTailX0RatChunk000Sub000Block170Part009

theorem surrogateDiagonalTailChunk000Sub000Block170Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block170Part009CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block170Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block170Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block170Part009CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block170Part009SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block170Part009] using hcert

def TailChunk000Sub000Block170Part010SupportExplicit : Finset ℕ :=
  ([7061] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block170Part010 : ℚ :=
  (1463815983725 : ℚ) / 2567871530850567744

def SurrogateDiagonalTailChunk000Sub000Block170Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7061
    = surrogateDiagTailX0RatChunk000Sub000Block170Part010

theorem surrogateDiagonalTailChunk000Sub000Block170Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block170Part010CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block170Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block170Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block170Part010CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block170Part010SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block170Part010] using hcert

def TailChunk000Sub000Block170Part011SupportExplicit : Finset ℕ :=
  ([7062] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block170Part011 : ℚ :=
  (446829573 : ℚ) / 26938228381696

def SurrogateDiagonalTailChunk000Sub000Block170Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7062
    = surrogateDiagTailX0RatChunk000Sub000Block170Part011

theorem surrogateDiagonalTailChunk000Sub000Block170Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block170Part011CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block170Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block170Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block170Part011CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block170Part011SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block170Part011] using hcert

def TailChunk000Sub000Block170Part012SupportExplicit : Finset ℕ :=
  ([7063] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block170Part012 : ℚ :=
  (2542489288375 : ℚ) / 3345599794952798208

def SurrogateDiagonalTailChunk000Sub000Block170Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7063
    = surrogateDiagTailX0RatChunk000Sub000Block170Part012

theorem surrogateDiagonalTailChunk000Sub000Block170Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block170Part012CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block170Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block170Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block170Part012CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block170Part012SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block170Part012] using hcert

def TailChunk000Sub000Block170Part013SupportExplicit : Finset ℕ :=
  ([7066] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block170Part013 : ℚ :=
  (195032640625 : ℚ) / 97285843153335072

def SurrogateDiagonalTailChunk000Sub000Block170Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7066
    = surrogateDiagTailX0RatChunk000Sub000Block170Part013

theorem surrogateDiagonalTailChunk000Sub000Block170Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block170Part013CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block170Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block170Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block170Part013CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block170Part013SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block170Part013] using hcert

def TailChunk000Sub000Block170Part014SupportExplicit : Finset ℕ :=
  ([7067] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block170Part014 : ℚ :=
  (59844113039 : ℚ) / 109466507291673600

def SurrogateDiagonalTailChunk000Sub000Block170Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7067
    = surrogateDiagTailX0RatChunk000Sub000Block170Part014

theorem surrogateDiagonalTailChunk000Sub000Block170Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block170Part014CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block170Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block170Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block170Part014CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block170Part014SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block170Part014] using hcert

def TailChunk000Sub000Block170Part015SupportExplicit : Finset ℕ :=
  ([7069] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block170Part015 : ℚ :=
  (780793140625 : ℚ) / 1560102133958544672

def SurrogateDiagonalTailChunk000Sub000Block170Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7069
    = surrogateDiagTailX0RatChunk000Sub000Block170Part015

theorem surrogateDiagonalTailChunk000Sub000Block170Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block170Part015CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block170Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block170Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block170Part015CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block170Part015SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block170Part015] using hcert

def TailChunk000Sub000Block170Part016SupportExplicit : Finset ℕ :=
  ([7070] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block170Part016 : ℚ :=
  (24551683111 : ℚ) / 3318423552000000

def SurrogateDiagonalTailChunk000Sub000Block170Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7070
    = surrogateDiagTailX0RatChunk000Sub000Block170Part016

theorem surrogateDiagonalTailChunk000Sub000Block170Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block170Part016CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block170Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block170Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block170Part016CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block170Part016SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block170Part016] using hcert

def TailChunk000Sub000Block170Part017SupportExplicit : Finset ℕ :=
  ([7071] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block170Part017 : ℚ :=
  (867753707675 : ℚ) / 616336645514486784

def SurrogateDiagonalTailChunk000Sub000Block170Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7071
    = surrogateDiagTailX0RatChunk000Sub000Block170Part017

theorem surrogateDiagonalTailChunk000Sub000Block170Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block170Part017CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block170Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block170Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block170Part017CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block170Part017SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block170Part017] using hcert

def TailChunk000Sub000Block170Part018SupportExplicit : Finset ℕ :=
  ([7073] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block170Part018 : ℚ :=
  (110398940431 : ℚ) / 169913138728579200

def SurrogateDiagonalTailChunk000Sub000Block170Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7073
    = surrogateDiagTailX0RatChunk000Sub000Block170Part018

theorem surrogateDiagonalTailChunk000Sub000Block170Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block170Part018CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block170Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block170Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block170Part018CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block170Part018SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block170Part018] using hcert

def TailChunk000Sub000Block170Part019SupportExplicit : Finset ℕ :=
  ([7077] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block170Part019 : ℚ :=
  (37714975 : ℚ) / 14682823852032

def SurrogateDiagonalTailChunk000Sub000Block170Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7077
    = surrogateDiagTailX0RatChunk000Sub000Block170Part019

theorem surrogateDiagonalTailChunk000Sub000Block170Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block170Part019CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block170Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block170Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block170Part019CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block170Part019SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block170Part019] using hcert

def TailChunk000Sub000Block170Part020SupportExplicit : Finset ℕ :=
  ([7078] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block170Part020 : ℚ :=
  (195695640625 : ℚ) / 97948588483746642

def SurrogateDiagonalTailChunk000Sub000Block170Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7078
    = surrogateDiagTailX0RatChunk000Sub000Block170Part020

theorem surrogateDiagonalTailChunk000Sub000Block170Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block170Part020CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block170Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block170Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block170Part020CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block170Part020SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block170Part020] using hcert

def TailChunk000Sub000Block170Part021SupportExplicit : Finset ℕ :=
  ([7079] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block170Part021 : ℚ :=
  (783003765625 : ℚ) / 1568949990046968882

def SurrogateDiagonalTailChunk000Sub000Block170Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7079
    = surrogateDiagTailX0RatChunk000Sub000Block170Part021

theorem surrogateDiagonalTailChunk000Sub000Block170Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block170Part021CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block170Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block170Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block170Part021CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block170Part021SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block170Part021] using hcert

def TailChunk000Sub000Block170Part022SupportExplicit : Finset ℕ :=
  ([7081] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block170Part022 : ℚ :=
  (3037926831175 : ℚ) / 5707445547741216768

def SurrogateDiagonalTailChunk000Sub000Block170Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7081
    = surrogateDiagTailX0RatChunk000Sub000Block170Part022

theorem surrogateDiagonalTailChunk000Sub000Block170Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block170Part022CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block170Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block170Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block170Part022CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block170Part022SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block170Part022] using hcert

def TailChunk000Sub000Block170Part023SupportExplicit : Finset ℕ :=
  ([7082] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block170Part023 : ℚ :=
  (313467025 : ℚ) / 157072406759712

def SurrogateDiagonalTailChunk000Sub000Block170Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7082
    = surrogateDiagTailX0RatChunk000Sub000Block170Part023

theorem surrogateDiagonalTailChunk000Sub000Block170Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block170Part023CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block170Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block170Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block170Part023CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block170Part023SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block170Part023] using hcert

def TailChunk000Sub000Block170Part024SupportExplicit : Finset ℕ :=
  ([7085] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block170Part024 : ℚ :=
  (709290619625 : ℚ) / 601957147613331456

def SurrogateDiagonalTailChunk000Sub000Block170Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7085
    = surrogateDiagTailX0RatChunk000Sub000Block170Part024

theorem surrogateDiagonalTailChunk000Sub000Block170Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block170Part024CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block170Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block170Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block170Part024CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block170Part024SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block170Part024] using hcert

def surrogateDiagonalTailChunk000Sub000Block170HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block170Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block170Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block170Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block170Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block170Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block170Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block170Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block170Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block170Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block170Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block170Head : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block170Part000
    + surrogateDiagTailX0RatChunk000Sub000Block170Part001
    + surrogateDiagTailX0RatChunk000Sub000Block170Part002
    + surrogateDiagTailX0RatChunk000Sub000Block170Part003
    + surrogateDiagTailX0RatChunk000Sub000Block170Part004
    + surrogateDiagTailX0RatChunk000Sub000Block170Part005
    + surrogateDiagTailX0RatChunk000Sub000Block170Part006
    + surrogateDiagTailX0RatChunk000Sub000Block170Part007
    + surrogateDiagTailX0RatChunk000Sub000Block170Part008
    + surrogateDiagTailX0RatChunk000Sub000Block170Part009

def surrogateDiagonalTailChunk000Sub000Block170MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block170Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block170Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block170Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block170Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block170Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block170Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block170Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block170Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block170Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block170Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block170Mid : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block170Part010
    + surrogateDiagTailX0RatChunk000Sub000Block170Part011
    + surrogateDiagTailX0RatChunk000Sub000Block170Part012
    + surrogateDiagTailX0RatChunk000Sub000Block170Part013
    + surrogateDiagTailX0RatChunk000Sub000Block170Part014
    + surrogateDiagTailX0RatChunk000Sub000Block170Part015
    + surrogateDiagTailX0RatChunk000Sub000Block170Part016
    + surrogateDiagTailX0RatChunk000Sub000Block170Part017
    + surrogateDiagTailX0RatChunk000Sub000Block170Part018
    + surrogateDiagTailX0RatChunk000Sub000Block170Part019

def surrogateDiagonalTailChunk000Sub000Block170TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block170Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block170Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block170Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block170Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block170Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block170Tail : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block170Part020
    + surrogateDiagTailX0RatChunk000Sub000Block170Part021
    + surrogateDiagTailX0RatChunk000Sub000Block170Part022
    + surrogateDiagTailX0RatChunk000Sub000Block170Part023
    + surrogateDiagTailX0RatChunk000Sub000Block170Part024

def surrogateDiagonalTailChunk000Sub000Block170Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub000Block170HeadSum X0
    + surrogateDiagonalTailChunk000Sub000Block170MidSum X0
    + surrogateDiagonalTailChunk000Sub000Block170TailSum X0

def surrogateDiagTailX0RatChunk000Sub000Block170 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block170Part000
    + surrogateDiagTailX0RatChunk000Sub000Block170Part001
    + surrogateDiagTailX0RatChunk000Sub000Block170Part002
    + surrogateDiagTailX0RatChunk000Sub000Block170Part003
    + surrogateDiagTailX0RatChunk000Sub000Block170Part004
    + surrogateDiagTailX0RatChunk000Sub000Block170Part005
    + surrogateDiagTailX0RatChunk000Sub000Block170Part006
    + surrogateDiagTailX0RatChunk000Sub000Block170Part007
    + surrogateDiagTailX0RatChunk000Sub000Block170Part008
    + surrogateDiagTailX0RatChunk000Sub000Block170Part009
    + surrogateDiagTailX0RatChunk000Sub000Block170Part010
    + surrogateDiagTailX0RatChunk000Sub000Block170Part011
    + surrogateDiagTailX0RatChunk000Sub000Block170Part012
    + surrogateDiagTailX0RatChunk000Sub000Block170Part013
    + surrogateDiagTailX0RatChunk000Sub000Block170Part014
    + surrogateDiagTailX0RatChunk000Sub000Block170Part015
    + surrogateDiagTailX0RatChunk000Sub000Block170Part016
    + surrogateDiagTailX0RatChunk000Sub000Block170Part017
    + surrogateDiagTailX0RatChunk000Sub000Block170Part018
    + surrogateDiagTailX0RatChunk000Sub000Block170Part019
    + surrogateDiagTailX0RatChunk000Sub000Block170Part020
    + surrogateDiagTailX0RatChunk000Sub000Block170Part021
    + surrogateDiagTailX0RatChunk000Sub000Block170Part022
    + surrogateDiagTailX0RatChunk000Sub000Block170Part023
    + surrogateDiagTailX0RatChunk000Sub000Block170Part024

theorem surrogateDiagTailX0RatChunk000Sub000Block170_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk000Sub000Block170Head + surrogateDiagTailX0RatChunk000Sub000Block170Mid + surrogateDiagTailX0RatChunk000Sub000Block170Tail =
      surrogateDiagTailX0RatChunk000Sub000Block170 := by
  unfold surrogateDiagTailX0RatChunk000Sub000Block170Head surrogateDiagTailX0RatChunk000Sub000Block170Mid surrogateDiagTailX0RatChunk000Sub000Block170Tail surrogateDiagTailX0RatChunk000Sub000Block170
  ring

def SurrogateDiagonalTailChunk000Sub000Block170HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block170HeadSum X0 = surrogateDiagTailX0RatChunk000Sub000Block170Head

def SurrogateDiagonalTailChunk000Sub000Block170MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block170MidSum X0 = surrogateDiagTailX0RatChunk000Sub000Block170Mid

def SurrogateDiagonalTailChunk000Sub000Block170TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block170TailSum X0 = surrogateDiagTailX0RatChunk000Sub000Block170Tail

theorem surrogateDiagonalTailChunk000Sub000Block170_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk000Sub000Block170HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk000Sub000Block170MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk000Sub000Block170TailCertificateAt X0) :
    surrogateDiagonalTailChunk000Sub000Block170Sum X0 = surrogateDiagTailX0RatChunk000Sub000Block170 := by
  unfold SurrogateDiagonalTailChunk000Sub000Block170HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk000Sub000Block170MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk000Sub000Block170TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk000Sub000Block170Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk000Sub000Block170_eq_head_add_mid_add_tail

/-- Block 171 covers tail-support indices [4275,4300) and q from 7086 to 7126. -/

def TailChunk000Sub000Block171Part000SupportExplicit : Finset ℕ :=
  ([7086] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block171Part000 : ℚ :=
  (24396168517 : ℚ) / 3102664824883200

def SurrogateDiagonalTailChunk000Sub000Block171Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7086
    = surrogateDiagTailX0RatChunk000Sub000Block171Part000

theorem surrogateDiagonalTailChunk000Sub000Block171Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block171Part000CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block171Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block171Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block171Part000CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block171Part000SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block171Part000] using hcert

def TailChunk000Sub000Block171Part001SupportExplicit : Finset ℕ :=
  ([7087] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block171Part001 : ℚ :=
  (2912184375925 : ℚ) / 5026765651412502528

def SurrogateDiagonalTailChunk000Sub000Block171Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7087
    = surrogateDiagTailX0RatChunk000Sub000Block171Part001

theorem surrogateDiagonalTailChunk000Sub000Block171Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block171Part001CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block171Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block171Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block171Part001CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block171Part001SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block171Part001] using hcert

def TailChunk000Sub000Block171Part002SupportExplicit : Finset ℕ :=
  ([7089] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block171Part002 : ℚ :=
  (1613431776175 : ℚ) / 950918108380397568

def SurrogateDiagonalTailChunk000Sub000Block171Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7089
    = surrogateDiagTailX0RatChunk000Sub000Block171Part002

theorem surrogateDiagonalTailChunk000Sub000Block171Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block171Part002CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block171Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block171Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block171Part002CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block171Part002SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block171Part002] using hcert

def TailChunk000Sub000Block171Part003SupportExplicit : Finset ℕ :=
  ([7090] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block171Part003 : ℚ :=
  (230200148825 : ℚ) / 53614048173981696

def SurrogateDiagonalTailChunk000Sub000Block171Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7090
    = surrogateDiagTailX0RatChunk000Sub000Block171Part003

theorem surrogateDiagonalTailChunk000Sub000Block171Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block171Part003CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block171Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block171Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block171Part003CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block171Part003SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block171Part003] using hcert

def TailChunk000Sub000Block171Part004SupportExplicit : Finset ℕ :=
  ([7091] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block171Part004 : ℚ :=
  (2562692923375 : ℚ) / 3399021490429052928

def SurrogateDiagonalTailChunk000Sub000Block171Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7091
    = surrogateDiagTailX0RatChunk000Sub000Block171Part004

theorem surrogateDiagonalTailChunk000Sub000Block171Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block171Part004CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block171Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block171Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block171Part004CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block171Part004SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block171Part004] using hcert

def TailChunk000Sub000Block171Part005SupportExplicit : Finset ℕ :=
  ([7093] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block171Part005 : ℚ :=
  (2812210123 : ℚ) / 5211612866150400

def SurrogateDiagonalTailChunk000Sub000Block171Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7093
    = surrogateDiagTailX0RatChunk000Sub000Block171Part005

theorem surrogateDiagonalTailChunk000Sub000Block171Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block171Part005CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block171Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block171Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block171Part005CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block171Part005SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block171Part005] using hcert

def TailChunk000Sub000Block171Part006SupportExplicit : Finset ℕ :=
  ([7094] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block171Part006 : ℚ :=
  (1572336594775 : ℚ) / 395350037150230728

def SurrogateDiagonalTailChunk000Sub000Block171Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7094
    = surrogateDiagTailX0RatChunk000Sub000Block171Part006

theorem surrogateDiagonalTailChunk000Sub000Block171Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block171Part006CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block171Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block171Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block171Part006CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block171Part006SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block171Part006] using hcert

def TailChunk000Sub000Block171Part007SupportExplicit : Finset ℕ :=
  ([7095] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block171Part007 : ℚ :=
  (51064007 : ℚ) / 14164506574848

def SurrogateDiagonalTailChunk000Sub000Block171Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7095
    = surrogateDiagTailX0RatChunk000Sub000Block171Part007

theorem surrogateDiagonalTailChunk000Sub000Block171Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block171Part007CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block171Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block171Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block171Part007CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block171Part007SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block171Part007] using hcert

def TailChunk000Sub000Block171Part008SupportExplicit : Finset ℕ :=
  ([7097] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block171Part008 : ℚ :=
  (1498945817 : ℚ) / 2798969682000000

def SurrogateDiagonalTailChunk000Sub000Block171Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7097
    = surrogateDiagTailX0RatChunk000Sub000Block171Part008

theorem surrogateDiagonalTailChunk000Sub000Block171Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block171Part008CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block171Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block171Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block171Part008CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block171Part008SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block171Part008] using hcert

def TailChunk000Sub000Block171Part009SupportExplicit : Finset ℕ :=
  ([7099] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block171Part009 : ℚ :=
  (120087076021 : ℚ) / 218933014583347200

def SurrogateDiagonalTailChunk000Sub000Block171Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7099
    = surrogateDiagTailX0RatChunk000Sub000Block171Part009

theorem surrogateDiagonalTailChunk000Sub000Block171Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block171Part009CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block171Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block171Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block171Part009CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block171Part009SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block171Part009] using hcert

def TailChunk000Sub000Block171Part010SupportExplicit : Finset ℕ :=
  ([7102] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block171Part010 : ℚ :=
  (83803932425 : ℚ) / 19272740351394816

def SurrogateDiagonalTailChunk000Sub000Block171Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7102
    = surrogateDiagTailX0RatChunk000Sub000Block171Part010

theorem surrogateDiagonalTailChunk000Sub000Block171Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block171Part010CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block171Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block171Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block171Part010CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block171Part010SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block171Part010] using hcert

def TailChunk000Sub000Block171Part011SupportExplicit : Finset ℕ :=
  ([7103] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block171Part011 : ℚ :=
  (788322015625 : ℚ) / 1590338377866768402

def SurrogateDiagonalTailChunk000Sub000Block171Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7103
    = surrogateDiagTailX0RatChunk000Sub000Block171Part011

theorem surrogateDiagonalTailChunk000Sub000Block171Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block171Part011CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block171Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block171Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block171Part011CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block171Part011SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block171Part011] using hcert

def TailChunk000Sub000Block171Part012SupportExplicit : Finset ℕ :=
  ([7106] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block171Part012 : ℚ :=
  (16073578459 : ℚ) / 2293694359142400

def SurrogateDiagonalTailChunk000Sub000Block171Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7106
    = surrogateDiagTailX0RatChunk000Sub000Block171Part012

theorem surrogateDiagonalTailChunk000Sub000Block171Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block171Part012CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block171Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block171Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block171Part012CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block171Part012SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block171Part012] using hcert

def TailChunk000Sub000Block171Part013SupportExplicit : Finset ℕ :=
  ([7107] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block171Part013 : ℚ :=
  (1646574867625 : ℚ) / 1014467765274298368

def SurrogateDiagonalTailChunk000Sub000Block171Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7107
    = surrogateDiagTailX0RatChunk000Sub000Block171Part013

theorem surrogateDiagonalTailChunk000Sub000Block171Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block171Part013CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block171Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block171Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block171Part013CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block171Part013SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block171Part013] using hcert

def TailChunk000Sub000Block171Part014SupportExplicit : Finset ℕ :=
  ([7109] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block171Part014 : ℚ :=
  (789654390625 : ℚ) / 1595719470068558112

def SurrogateDiagonalTailChunk000Sub000Block171Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7109
    = surrogateDiagTailX0RatChunk000Sub000Block171Part014

theorem surrogateDiagonalTailChunk000Sub000Block171Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block171Part014CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block171Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block171Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block171Part014CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block171Part014SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block171Part014] using hcert

def TailChunk000Sub000Block171Part015SupportExplicit : Finset ℕ :=
  ([7111] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block171Part015 : ℚ :=
  (1515146125 : ℚ) / 2461594820840064

def SurrogateDiagonalTailChunk000Sub000Block171Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7111
    = surrogateDiagTailX0RatChunk000Sub000Block171Part015

theorem surrogateDiagonalTailChunk000Sub000Block171Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block171Part015CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block171Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block171Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block171Part015CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block171Part015SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block171Part015] using hcert

def TailChunk000Sub000Block171Part016SupportExplicit : Finset ℕ :=
  ([7113] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block171Part016 : ℚ :=
  (14051939309 : ℚ) / 25244700418497600

def SurrogateDiagonalTailChunk000Sub000Block171Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7113
    = surrogateDiagTailX0RatChunk000Sub000Block171Part016

theorem surrogateDiagonalTailChunk000Sub000Block171Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block171Part016CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block171Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block171Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block171Part016CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block171Part016SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block171Part016] using hcert

def TailChunk000Sub000Block171Part017SupportExplicit : Finset ℕ :=
  ([7114] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block171Part017 : ℚ :=
  (197691390625 : ℚ) / 99957152719617312

def SurrogateDiagonalTailChunk000Sub000Block171Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7114
    = surrogateDiagTailX0RatChunk000Sub000Block171Part017

theorem surrogateDiagonalTailChunk000Sub000Block171Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block171Part017CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block171Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block171Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block171Part017CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block171Part017SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block171Part017] using hcert

def TailChunk000Sub000Block171Part018SupportExplicit : Finset ℕ :=
  ([7115] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block171Part018 : ℚ :=
  (23764963075 : ℚ) / 163585658711864448

def SurrogateDiagonalTailChunk000Sub000Block171Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7115
    = surrogateDiagTailX0RatChunk000Sub000Block171Part018

theorem surrogateDiagonalTailChunk000Sub000Block171Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block171Part018CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block171Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block171Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block171Part018CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block171Part018SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block171Part018] using hcert

def TailChunk000Sub000Block171Part019SupportExplicit : Finset ℕ :=
  ([7117] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block171Part019 : ℚ :=
  (8459693083 : ℚ) / 174187474384771200

def SurrogateDiagonalTailChunk000Sub000Block171Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7117
    = surrogateDiagTailX0RatChunk000Sub000Block171Part019

theorem surrogateDiagonalTailChunk000Sub000Block171Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block171Part019CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block171Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block171Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block171Part019CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block171Part019SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block171Part019] using hcert

def TailChunk000Sub000Block171Part020SupportExplicit : Finset ℕ :=
  ([7118] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block171Part020 : ℚ :=
  (197913765625 : ℚ) / 100182217989920562

def SurrogateDiagonalTailChunk000Sub000Block171Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7118
    = surrogateDiagTailX0RatChunk000Sub000Block171Part020

theorem surrogateDiagonalTailChunk000Sub000Block171Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block171Part020CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block171Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block171Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block171Part020CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block171Part020SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block171Part020] using hcert

def TailChunk000Sub000Block171Part021SupportExplicit : Finset ℕ :=
  ([7121] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block171Part021 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub000Block171Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7121
    = surrogateDiagTailX0RatChunk000Sub000Block171Part021

theorem surrogateDiagonalTailChunk000Sub000Block171Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block171Part021CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block171Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block171Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block171Part021CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block171Part021SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block171Part021] using hcert

def TailChunk000Sub000Block171Part022SupportExplicit : Finset ℕ :=
  ([7122] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block171Part022 : ℚ :=
  (616116027475 : ℚ) / 79156320387097728

def SurrogateDiagonalTailChunk000Sub000Block171Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7122
    = surrogateDiagTailX0RatChunk000Sub000Block171Part022

theorem surrogateDiagonalTailChunk000Sub000Block171Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block171Part022CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block171Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block171Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block171Part022CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block171Part022SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block171Part022] using hcert

def TailChunk000Sub000Block171Part023SupportExplicit : Finset ℕ :=
  ([7123] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block171Part023 : ℚ :=
  (45250670925 : ℚ) / 1667595297927725056

def SurrogateDiagonalTailChunk000Sub000Block171Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7123
    = surrogateDiagTailX0RatChunk000Sub000Block171Part023

theorem surrogateDiagonalTailChunk000Sub000Block171Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block171Part023CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block171Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block171Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block171Part023CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block171Part023SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block171Part023] using hcert

def TailChunk000Sub000Block171Part024SupportExplicit : Finset ℕ :=
  ([7126] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block171Part024 : ℚ :=
  (80865903125 : ℚ) / 23979725100582912

def SurrogateDiagonalTailChunk000Sub000Block171Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7126
    = surrogateDiagTailX0RatChunk000Sub000Block171Part024

theorem surrogateDiagonalTailChunk000Sub000Block171Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block171Part024CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block171Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block171Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block171Part024CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block171Part024SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block171Part024] using hcert

def surrogateDiagonalTailChunk000Sub000Block171HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block171Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block171Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block171Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block171Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block171Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block171Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block171Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block171Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block171Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block171Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block171Head : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block171Part000
    + surrogateDiagTailX0RatChunk000Sub000Block171Part001
    + surrogateDiagTailX0RatChunk000Sub000Block171Part002
    + surrogateDiagTailX0RatChunk000Sub000Block171Part003
    + surrogateDiagTailX0RatChunk000Sub000Block171Part004
    + surrogateDiagTailX0RatChunk000Sub000Block171Part005
    + surrogateDiagTailX0RatChunk000Sub000Block171Part006
    + surrogateDiagTailX0RatChunk000Sub000Block171Part007
    + surrogateDiagTailX0RatChunk000Sub000Block171Part008
    + surrogateDiagTailX0RatChunk000Sub000Block171Part009

def surrogateDiagonalTailChunk000Sub000Block171MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block171Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block171Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block171Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block171Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block171Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block171Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block171Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block171Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block171Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block171Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block171Mid : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block171Part010
    + surrogateDiagTailX0RatChunk000Sub000Block171Part011
    + surrogateDiagTailX0RatChunk000Sub000Block171Part012
    + surrogateDiagTailX0RatChunk000Sub000Block171Part013
    + surrogateDiagTailX0RatChunk000Sub000Block171Part014
    + surrogateDiagTailX0RatChunk000Sub000Block171Part015
    + surrogateDiagTailX0RatChunk000Sub000Block171Part016
    + surrogateDiagTailX0RatChunk000Sub000Block171Part017
    + surrogateDiagTailX0RatChunk000Sub000Block171Part018
    + surrogateDiagTailX0RatChunk000Sub000Block171Part019

def surrogateDiagonalTailChunk000Sub000Block171TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block171Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block171Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block171Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block171Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block171Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block171Tail : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block171Part020
    + surrogateDiagTailX0RatChunk000Sub000Block171Part021
    + surrogateDiagTailX0RatChunk000Sub000Block171Part022
    + surrogateDiagTailX0RatChunk000Sub000Block171Part023
    + surrogateDiagTailX0RatChunk000Sub000Block171Part024

def surrogateDiagonalTailChunk000Sub000Block171Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub000Block171HeadSum X0
    + surrogateDiagonalTailChunk000Sub000Block171MidSum X0
    + surrogateDiagonalTailChunk000Sub000Block171TailSum X0

def surrogateDiagTailX0RatChunk000Sub000Block171 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block171Part000
    + surrogateDiagTailX0RatChunk000Sub000Block171Part001
    + surrogateDiagTailX0RatChunk000Sub000Block171Part002
    + surrogateDiagTailX0RatChunk000Sub000Block171Part003
    + surrogateDiagTailX0RatChunk000Sub000Block171Part004
    + surrogateDiagTailX0RatChunk000Sub000Block171Part005
    + surrogateDiagTailX0RatChunk000Sub000Block171Part006
    + surrogateDiagTailX0RatChunk000Sub000Block171Part007
    + surrogateDiagTailX0RatChunk000Sub000Block171Part008
    + surrogateDiagTailX0RatChunk000Sub000Block171Part009
    + surrogateDiagTailX0RatChunk000Sub000Block171Part010
    + surrogateDiagTailX0RatChunk000Sub000Block171Part011
    + surrogateDiagTailX0RatChunk000Sub000Block171Part012
    + surrogateDiagTailX0RatChunk000Sub000Block171Part013
    + surrogateDiagTailX0RatChunk000Sub000Block171Part014
    + surrogateDiagTailX0RatChunk000Sub000Block171Part015
    + surrogateDiagTailX0RatChunk000Sub000Block171Part016
    + surrogateDiagTailX0RatChunk000Sub000Block171Part017
    + surrogateDiagTailX0RatChunk000Sub000Block171Part018
    + surrogateDiagTailX0RatChunk000Sub000Block171Part019
    + surrogateDiagTailX0RatChunk000Sub000Block171Part020
    + surrogateDiagTailX0RatChunk000Sub000Block171Part021
    + surrogateDiagTailX0RatChunk000Sub000Block171Part022
    + surrogateDiagTailX0RatChunk000Sub000Block171Part023
    + surrogateDiagTailX0RatChunk000Sub000Block171Part024

theorem surrogateDiagTailX0RatChunk000Sub000Block171_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk000Sub000Block171Head + surrogateDiagTailX0RatChunk000Sub000Block171Mid + surrogateDiagTailX0RatChunk000Sub000Block171Tail =
      surrogateDiagTailX0RatChunk000Sub000Block171 := by
  unfold surrogateDiagTailX0RatChunk000Sub000Block171Head surrogateDiagTailX0RatChunk000Sub000Block171Mid surrogateDiagTailX0RatChunk000Sub000Block171Tail surrogateDiagTailX0RatChunk000Sub000Block171
  ring

def SurrogateDiagonalTailChunk000Sub000Block171HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block171HeadSum X0 = surrogateDiagTailX0RatChunk000Sub000Block171Head

def SurrogateDiagonalTailChunk000Sub000Block171MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block171MidSum X0 = surrogateDiagTailX0RatChunk000Sub000Block171Mid

def SurrogateDiagonalTailChunk000Sub000Block171TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block171TailSum X0 = surrogateDiagTailX0RatChunk000Sub000Block171Tail

theorem surrogateDiagonalTailChunk000Sub000Block171_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk000Sub000Block171HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk000Sub000Block171MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk000Sub000Block171TailCertificateAt X0) :
    surrogateDiagonalTailChunk000Sub000Block171Sum X0 = surrogateDiagTailX0RatChunk000Sub000Block171 := by
  unfold SurrogateDiagonalTailChunk000Sub000Block171HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk000Sub000Block171MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk000Sub000Block171TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk000Sub000Block171Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk000Sub000Block171_eq_head_add_mid_add_tail

/-- Block 172 covers tail-support indices [4300,4325) and q from 7127 to 7167. -/

def TailChunk000Sub000Block172Part000SupportExplicit : Finset ℕ :=
  ([7127] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block172Part000 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub000Block172Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7127
    = surrogateDiagTailX0RatChunk000Sub000Block172Part000

theorem surrogateDiagonalTailChunk000Sub000Block172Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block172Part000CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block172Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block172Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block172Part000CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block172Part000SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block172Part000] using hcert

def TailChunk000Sub000Block172Part001SupportExplicit : Finset ℕ :=
  ([7129] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block172Part001 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub000Block172Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7129
    = surrogateDiagTailX0RatChunk000Sub000Block172Part001

theorem surrogateDiagonalTailChunk000Sub000Block172Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block172Part001CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block172Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block172Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block172Part001CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block172Part001SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block172Part001] using hcert

def TailChunk000Sub000Block172Part002SupportExplicit : Finset ℕ :=
  ([7130] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block172Part002 : ℚ :=
  (529386029 : ℚ) / 97170078449664

def SurrogateDiagonalTailChunk000Sub000Block172Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7130
    = surrogateDiagTailX0RatChunk000Sub000Block172Part002

theorem surrogateDiagonalTailChunk000Sub000Block172Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block172Part002CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block172Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block172Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block172Part002CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block172Part002SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block172Part002] using hcert

def TailChunk000Sub000Block172Part003SupportExplicit : Finset ℕ :=
  ([7131] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block172Part003 : ℚ :=
  (353077876475 : ℚ) / 637532884708245504

def SurrogateDiagonalTailChunk000Sub000Block172Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7131
    = surrogateDiagTailX0RatChunk000Sub000Block172Part003

theorem surrogateDiagonalTailChunk000Sub000Block172Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block172Part003CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block172Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block172Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block172Part003CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block172Part003SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block172Part003] using hcert

def TailChunk000Sub000Block172Part004SupportExplicit : Finset ℕ :=
  ([7133] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block172Part004 : ℚ :=
  (325466414275 : ℚ) / 3480350413738808448

def SurrogateDiagonalTailChunk000Sub000Block172Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7133
    = surrogateDiagTailX0RatChunk000Sub000Block172Part004

theorem surrogateDiagonalTailChunk000Sub000Block172Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block172Part004CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block172Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block172Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block172Part004CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block172Part004SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block172Part004] using hcert

def TailChunk000Sub000Block172Part005SupportExplicit : Finset ℕ :=
  ([7134] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block172Part005 : ℚ :=
  (11789126891 : ℚ) / 1259067251097600

def SurrogateDiagonalTailChunk000Sub000Block172Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7134
    = surrogateDiagTailX0RatChunk000Sub000Block172Part005

theorem surrogateDiagonalTailChunk000Sub000Block172Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block172Part005CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block172Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block172Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block172Part005CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block172Part005SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block172Part005] using hcert

def TailChunk000Sub000Block172Part006SupportExplicit : Finset ℕ :=
  ([7135] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block172Part006 : ℚ :=
  (95593638175 : ℚ) / 661736263600722432

def SurrogateDiagonalTailChunk000Sub000Block172Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7135
    = surrogateDiagTailX0RatChunk000Sub000Block172Part006

theorem surrogateDiagonalTailChunk000Sub000Block172Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block172Part006CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block172Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block172Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block172Part006CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block172Part006SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block172Part006] using hcert

def TailChunk000Sub000Block172Part007SupportExplicit : Finset ℕ :=
  ([7138] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block172Part007 : ℚ :=
  (389668098875 : ℚ) / 175893355649922624

def SurrogateDiagonalTailChunk000Sub000Block172Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7138
    = surrogateDiagTailX0RatChunk000Sub000Block172Part007

theorem surrogateDiagonalTailChunk000Sub000Block172Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block172Part007CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block172Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block172Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block172Part007CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block172Part007SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block172Part007] using hcert

def TailChunk000Sub000Block172Part008SupportExplicit : Finset ℕ :=
  ([7141] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block172Part008 : ℚ :=
  (17710431625 : ℚ) / 1426861386935304192

def SurrogateDiagonalTailChunk000Sub000Block172Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7141
    = surrogateDiagTailX0RatChunk000Sub000Block172Part008

theorem surrogateDiagonalTailChunk000Sub000Block172Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block172Part008CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block172Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block172Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block172Part008CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block172Part008SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block172Part008] using hcert

def TailChunk000Sub000Block172Part009SupportExplicit : Finset ℕ :=
  ([7142] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block172Part009 : ℚ :=
  (318801025 : ℚ) / 162464962505202

def SurrogateDiagonalTailChunk000Sub000Block172Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7142
    = surrogateDiagTailX0RatChunk000Sub000Block172Part009

theorem surrogateDiagonalTailChunk000Sub000Block172Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block172Part009CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block172Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block172Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block172Part009CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block172Part009SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block172Part009] using hcert

def TailChunk000Sub000Block172Part010SupportExplicit : Finset ℕ :=
  ([7143] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block172Part010 : ℚ :=
  (10203 : ℚ) / 6162867200

def SurrogateDiagonalTailChunk000Sub000Block172Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7143
    = surrogateDiagTailX0RatChunk000Sub000Block172Part010

theorem surrogateDiagonalTailChunk000Sub000Block172Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block172Part010CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block172Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block172Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block172Part010CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block172Part010SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block172Part010] using hcert

def TailChunk000Sub000Block172Part011SupportExplicit : Finset ℕ :=
  ([7145] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block172Part011 : ℚ :=
  (403873330975 : ℚ) / 443637657614204928

def SurrogateDiagonalTailChunk000Sub000Block172Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7145
    = surrogateDiagTailX0RatChunk000Sub000Block172Part011

theorem surrogateDiagonalTailChunk000Sub000Block172Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block172Part011CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block172Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block172Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block172Part011CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block172Part011SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block172Part011] using hcert

def TailChunk000Sub000Block172Part012SupportExplicit : Finset ℕ :=
  ([7147] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block172Part012 : ℚ :=
  (6125506439 : ℚ) / 8253603798681600

def SurrogateDiagonalTailChunk000Sub000Block172Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7147
    = surrogateDiagTailX0RatChunk000Sub000Block172Part012

theorem surrogateDiagonalTailChunk000Sub000Block172Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block172Part012CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block172Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block172Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block172Part012CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block172Part012SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block172Part012] using hcert

def TailChunk000Sub000Block172Part013SupportExplicit : Finset ℕ :=
  ([7149] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block172Part013 : ℚ :=
  (443502456025 : ℚ) / 321998522404875552

def SurrogateDiagonalTailChunk000Sub000Block172Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7149
    = surrogateDiagTailX0RatChunk000Sub000Block172Part013

theorem surrogateDiagonalTailChunk000Sub000Block172Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block172Part013CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block172Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block172Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block172Part013CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block172Part013SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block172Part013] using hcert

def TailChunk000Sub000Block172Part014SupportExplicit : Finset ℕ :=
  ([7151] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block172Part014 : ℚ :=
  (51136801 : ℚ) / 104561308330050

def SurrogateDiagonalTailChunk000Sub000Block172Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7151
    = surrogateDiagTailX0RatChunk000Sub000Block172Part014

theorem surrogateDiagonalTailChunk000Sub000Block172Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block172Part014CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block172Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block172Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block172Part014CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block172Part014SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block172Part014] using hcert

def TailChunk000Sub000Block172Part015SupportExplicit : Finset ℕ :=
  ([7153] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block172Part015 : ℚ :=
  (20029945437 : ℚ) / 36063933907179200

def SurrogateDiagonalTailChunk000Sub000Block172Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7153
    = surrogateDiagTailX0RatChunk000Sub000Block172Part015

theorem surrogateDiagonalTailChunk000Sub000Block172Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block172Part015CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block172Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block172Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block172Part015CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block172Part015SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block172Part015] using hcert

def TailChunk000Sub000Block172Part016SupportExplicit : Finset ℕ :=
  ([7157] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block172Part016 : ℚ :=
  (5898381371 : ℚ) / 10198444733890560

def SurrogateDiagonalTailChunk000Sub000Block172Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7157
    = surrogateDiagTailX0RatChunk000Sub000Block172Part016

theorem surrogateDiagonalTailChunk000Sub000Block172Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block172Part016CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block172Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block172Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block172Part016CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block172Part016SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block172Part016] using hcert

def TailChunk000Sub000Block172Part017SupportExplicit : Finset ℕ :=
  ([7158] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block172Part017 : ℚ :=
  (444385535225 : ℚ) / 40385165547945984

def SurrogateDiagonalTailChunk000Sub000Block172Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7158
    = surrogateDiagTailX0RatChunk000Sub000Block172Part017

theorem surrogateDiagonalTailChunk000Sub000Block172Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block172Part017CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block172Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block172Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block172Part017CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block172Part017SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block172Part017] using hcert

def TailChunk000Sub000Block172Part018SupportExplicit : Finset ℕ :=
  ([7159] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block172Part018 : ℚ :=
  (800801265625 : ℚ) / 1641094703270802162

def SurrogateDiagonalTailChunk000Sub000Block172Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7159
    = surrogateDiagTailX0RatChunk000Sub000Block172Part018

theorem surrogateDiagonalTailChunk000Sub000Block172Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block172Part018CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block172Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block172Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block172Part018CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block172Part018SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block172Part018] using hcert

def TailChunk000Sub000Block172Part019SupportExplicit : Finset ℕ :=
  ([7161] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block172Part019 : ℚ :=
  (1892409113 : ℚ) / 622204416000000

def SurrogateDiagonalTailChunk000Sub000Block172Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7161
    = surrogateDiagTailX0RatChunk000Sub000Block172Part019

theorem surrogateDiagonalTailChunk000Sub000Block172Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block172Part019CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block172Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block172Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block172Part019CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block172Part019SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block172Part019] using hcert

def TailChunk000Sub000Block172Part020SupportExplicit : Finset ℕ :=
  ([7162] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block172Part020 : ℚ :=
  (64104981439 : ℚ) / 16429296098179200

def SurrogateDiagonalTailChunk000Sub000Block172Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7162
    = surrogateDiagTailX0RatChunk000Sub000Block172Part020

theorem surrogateDiagonalTailChunk000Sub000Block172Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block172Part020CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block172Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block172Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block172Part020CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block172Part020SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block172Part020] using hcert

def TailChunk000Sub000Block172Part021SupportExplicit : Finset ℕ :=
  ([7163] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block172Part021 : ℚ :=
  (856423747175 : ℚ) / 1115199931650932736

def SurrogateDiagonalTailChunk000Sub000Block172Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7163
    = surrogateDiagTailX0RatChunk000Sub000Block172Part021

theorem surrogateDiagonalTailChunk000Sub000Block172Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block172Part021CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block172Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block172Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block172Part021CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block172Part021SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block172Part021] using hcert

def TailChunk000Sub000Block172Part022SupportExplicit : Finset ℕ :=
  ([7165] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block172Part022 : ℚ :=
  (1218413780075 : ℚ) / 1345887936362840064

def SurrogateDiagonalTailChunk000Sub000Block172Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7165
    = surrogateDiagTailX0RatChunk000Sub000Block172Part022

theorem surrogateDiagonalTailChunk000Sub000Block172Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block172Part022CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block172Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block172Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block172Part022CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block172Part022SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block172Part022] using hcert

def TailChunk000Sub000Block172Part023SupportExplicit : Finset ℕ :=
  ([7166] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block172Part023 : ℚ :=
  (200592015625 : ℚ) / 102912752412405522

def SurrogateDiagonalTailChunk000Sub000Block172Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7166
    = surrogateDiagTailX0RatChunk000Sub000Block172Part023

theorem surrogateDiagonalTailChunk000Sub000Block172Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block172Part023CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block172Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block172Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block172Part023CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block172Part023SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block172Part023] using hcert

def TailChunk000Sub000Block172Part024SupportExplicit : Finset ℕ :=
  ([7167] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block172Part024 : ℚ :=
  (891477502475 : ℚ) / 650510237471007744

def SurrogateDiagonalTailChunk000Sub000Block172Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7167
    = surrogateDiagTailX0RatChunk000Sub000Block172Part024

theorem surrogateDiagonalTailChunk000Sub000Block172Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block172Part024CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block172Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block172Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block172Part024CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block172Part024SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block172Part024] using hcert

def surrogateDiagonalTailChunk000Sub000Block172HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block172Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block172Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block172Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block172Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block172Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block172Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block172Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block172Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block172Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block172Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block172Head : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block172Part000
    + surrogateDiagTailX0RatChunk000Sub000Block172Part001
    + surrogateDiagTailX0RatChunk000Sub000Block172Part002
    + surrogateDiagTailX0RatChunk000Sub000Block172Part003
    + surrogateDiagTailX0RatChunk000Sub000Block172Part004
    + surrogateDiagTailX0RatChunk000Sub000Block172Part005
    + surrogateDiagTailX0RatChunk000Sub000Block172Part006
    + surrogateDiagTailX0RatChunk000Sub000Block172Part007
    + surrogateDiagTailX0RatChunk000Sub000Block172Part008
    + surrogateDiagTailX0RatChunk000Sub000Block172Part009

def surrogateDiagonalTailChunk000Sub000Block172MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block172Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block172Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block172Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block172Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block172Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block172Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block172Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block172Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block172Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block172Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block172Mid : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block172Part010
    + surrogateDiagTailX0RatChunk000Sub000Block172Part011
    + surrogateDiagTailX0RatChunk000Sub000Block172Part012
    + surrogateDiagTailX0RatChunk000Sub000Block172Part013
    + surrogateDiagTailX0RatChunk000Sub000Block172Part014
    + surrogateDiagTailX0RatChunk000Sub000Block172Part015
    + surrogateDiagTailX0RatChunk000Sub000Block172Part016
    + surrogateDiagTailX0RatChunk000Sub000Block172Part017
    + surrogateDiagTailX0RatChunk000Sub000Block172Part018
    + surrogateDiagTailX0RatChunk000Sub000Block172Part019

def surrogateDiagonalTailChunk000Sub000Block172TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block172Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block172Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block172Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block172Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block172Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block172Tail : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block172Part020
    + surrogateDiagTailX0RatChunk000Sub000Block172Part021
    + surrogateDiagTailX0RatChunk000Sub000Block172Part022
    + surrogateDiagTailX0RatChunk000Sub000Block172Part023
    + surrogateDiagTailX0RatChunk000Sub000Block172Part024

def surrogateDiagonalTailChunk000Sub000Block172Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub000Block172HeadSum X0
    + surrogateDiagonalTailChunk000Sub000Block172MidSum X0
    + surrogateDiagonalTailChunk000Sub000Block172TailSum X0

def surrogateDiagTailX0RatChunk000Sub000Block172 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block172Part000
    + surrogateDiagTailX0RatChunk000Sub000Block172Part001
    + surrogateDiagTailX0RatChunk000Sub000Block172Part002
    + surrogateDiagTailX0RatChunk000Sub000Block172Part003
    + surrogateDiagTailX0RatChunk000Sub000Block172Part004
    + surrogateDiagTailX0RatChunk000Sub000Block172Part005
    + surrogateDiagTailX0RatChunk000Sub000Block172Part006
    + surrogateDiagTailX0RatChunk000Sub000Block172Part007
    + surrogateDiagTailX0RatChunk000Sub000Block172Part008
    + surrogateDiagTailX0RatChunk000Sub000Block172Part009
    + surrogateDiagTailX0RatChunk000Sub000Block172Part010
    + surrogateDiagTailX0RatChunk000Sub000Block172Part011
    + surrogateDiagTailX0RatChunk000Sub000Block172Part012
    + surrogateDiagTailX0RatChunk000Sub000Block172Part013
    + surrogateDiagTailX0RatChunk000Sub000Block172Part014
    + surrogateDiagTailX0RatChunk000Sub000Block172Part015
    + surrogateDiagTailX0RatChunk000Sub000Block172Part016
    + surrogateDiagTailX0RatChunk000Sub000Block172Part017
    + surrogateDiagTailX0RatChunk000Sub000Block172Part018
    + surrogateDiagTailX0RatChunk000Sub000Block172Part019
    + surrogateDiagTailX0RatChunk000Sub000Block172Part020
    + surrogateDiagTailX0RatChunk000Sub000Block172Part021
    + surrogateDiagTailX0RatChunk000Sub000Block172Part022
    + surrogateDiagTailX0RatChunk000Sub000Block172Part023
    + surrogateDiagTailX0RatChunk000Sub000Block172Part024

theorem surrogateDiagTailX0RatChunk000Sub000Block172_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk000Sub000Block172Head + surrogateDiagTailX0RatChunk000Sub000Block172Mid + surrogateDiagTailX0RatChunk000Sub000Block172Tail =
      surrogateDiagTailX0RatChunk000Sub000Block172 := by
  unfold surrogateDiagTailX0RatChunk000Sub000Block172Head surrogateDiagTailX0RatChunk000Sub000Block172Mid surrogateDiagTailX0RatChunk000Sub000Block172Tail surrogateDiagTailX0RatChunk000Sub000Block172
  ring

def SurrogateDiagonalTailChunk000Sub000Block172HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block172HeadSum X0 = surrogateDiagTailX0RatChunk000Sub000Block172Head

def SurrogateDiagonalTailChunk000Sub000Block172MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block172MidSum X0 = surrogateDiagTailX0RatChunk000Sub000Block172Mid

def SurrogateDiagonalTailChunk000Sub000Block172TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block172TailSum X0 = surrogateDiagTailX0RatChunk000Sub000Block172Tail

theorem surrogateDiagonalTailChunk000Sub000Block172_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk000Sub000Block172HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk000Sub000Block172MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk000Sub000Block172TailCertificateAt X0) :
    surrogateDiagonalTailChunk000Sub000Block172Sum X0 = surrogateDiagTailX0RatChunk000Sub000Block172 := by
  unfold SurrogateDiagonalTailChunk000Sub000Block172HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk000Sub000Block172MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk000Sub000Block172TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk000Sub000Block172Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk000Sub000Block172_eq_head_add_mid_add_tail

/-- Block 173 covers tail-support indices [4325,4350) and q from 7169 to 7207. -/

def TailChunk000Sub000Block173Part000SupportExplicit : Finset ℕ :=
  ([7169] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block173Part000 : ℚ :=
  (389040297875 : ℚ) / 748748689233968016

def SurrogateDiagonalTailChunk000Sub000Block173Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7169
    = surrogateDiagTailX0RatChunk000Sub000Block173Part000

theorem surrogateDiagonalTailChunk000Sub000Block173Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block173Part000CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block173Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block173Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block173Part000CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block173Part000SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block173Part000] using hcert

def TailChunk000Sub000Block173Part001SupportExplicit : Finset ℕ :=
  ([7170] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block173Part001 : ℚ :=
  (129861506575 : ℚ) / 8215512178040832

def SurrogateDiagonalTailChunk000Sub000Block173Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7170
    = surrogateDiagTailX0RatChunk000Sub000Block173Part001

theorem surrogateDiagonalTailChunk000Sub000Block173Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block173Part001CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block173Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block173Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block173Part001CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block173Part001SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block173Part001] using hcert

def TailChunk000Sub000Block173Part002SupportExplicit : Finset ℕ :=
  ([7171] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block173Part002 : ℚ :=
  (17800722277 : ℚ) / 34306860000000000

def SurrogateDiagonalTailChunk000Sub000Block173Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7171
    = surrogateDiagTailX0RatChunk000Sub000Block173Part002

theorem surrogateDiagonalTailChunk000Sub000Block173Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block173Part002CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block173Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block173Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block173Part002CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block173Part002SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block173Part002] using hcert

def TailChunk000Sub000Block173Part003SupportExplicit : Finset ℕ :=
  ([7174] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block173Part003 : ℚ :=
  (15482042729 : ℚ) / 6374027958681600

def SurrogateDiagonalTailChunk000Sub000Block173Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7174
    = surrogateDiagTailX0RatChunk000Sub000Block173Part003

theorem surrogateDiagonalTailChunk000Sub000Block173Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block173Part003CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block173Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block173Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block173Part003CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block173Part003SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block173Part003] using hcert

def TailChunk000Sub000Block173Part004SupportExplicit : Finset ℕ :=
  ([7177] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block173Part004 : ℚ :=
  (804833265625 : ℚ) / 1657664312344515072

def SurrogateDiagonalTailChunk000Sub000Block173Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7177
    = surrogateDiagTailX0RatChunk000Sub000Block173Part004

theorem surrogateDiagonalTailChunk000Sub000Block173Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block173Part004CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block173Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block173Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block173Part004CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block173Part004SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block173Part004] using hcert

def TailChunk000Sub000Block173Part005SupportExplicit : Finset ℕ :=
  ([7178] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block173Part005 : ℚ :=
  (29154003625 : ℚ) / 13211679508660224

def SurrogateDiagonalTailChunk000Sub000Block173Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7178
    = surrogateDiagTailX0RatChunk000Sub000Block173Part005

theorem surrogateDiagonalTailChunk000Sub000Block173Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block173Part005CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block173Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block173Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block173Part005CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block173Part005SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block173Part005] using hcert

def TailChunk000Sub000Block173Part006SupportExplicit : Finset ℕ :=
  ([7179] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block173Part006 : ℚ :=
  (214624875 : ℚ) / 130949755715584

def SurrogateDiagonalTailChunk000Sub000Block173Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7179
    = surrogateDiagTailX0RatChunk000Sub000Block173Part006

theorem surrogateDiagonalTailChunk000Sub000Block173Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block173Part006CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block173Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block173Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block173Part006CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block173Part006SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block173Part006] using hcert

def TailChunk000Sub000Block173Part007SupportExplicit : Finset ℕ :=
  ([7181] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block173Part007 : ℚ :=
  (774979446775 : ℚ) / 1477054027959404832

def SurrogateDiagonalTailChunk000Sub000Block173Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7181
    = surrogateDiagTailX0RatChunk000Sub000Block173Part007

theorem surrogateDiagonalTailChunk000Sub000Block173Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block173Part007CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block173Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block173Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block173Part007CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block173Part007SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block173Part007] using hcert

def TailChunk000Sub000Block173Part008SupportExplicit : Finset ℕ :=
  ([7183] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block173Part008 : ℚ :=
  (113861024521 : ℚ) / 180749553498163200

def SurrogateDiagonalTailChunk000Sub000Block173Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7183
    = surrogateDiagTailX0RatChunk000Sub000Block173Part008

theorem surrogateDiagonalTailChunk000Sub000Block173Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block173Part008CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block173Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block173Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block173Part008CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block173Part008SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block173Part008] using hcert

def TailChunk000Sub000Block173Part009SupportExplicit : Finset ℕ :=
  ([7185] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block173Part009 : ℚ :=
  (233698753875 : ℚ) / 89114247242498048

def SurrogateDiagonalTailChunk000Sub000Block173Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7185
    = surrogateDiagTailX0RatChunk000Sub000Block173Part009

theorem surrogateDiagonalTailChunk000Sub000Block173Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block173Part009CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block173Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block173Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block173Part009CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block173Part009SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block173Part009] using hcert

def TailChunk000Sub000Block173Part010SupportExplicit : Finset ℕ :=
  ([7186] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block173Part010 : ℚ :=
  (201713265625 : ℚ) / 104066794991718912

def SurrogateDiagonalTailChunk000Sub000Block173Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7186
    = surrogateDiagTailX0RatChunk000Sub000Block173Part010

theorem surrogateDiagonalTailChunk000Sub000Block173Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block173Part010CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block173Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block173Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block173Part010CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block173Part010SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block173Part010] using hcert

def TailChunk000Sub000Block173Part011SupportExplicit : Finset ℕ :=
  ([7187] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block173Part011 : ℚ :=
  (807077640625 : ℚ) / 1666923691106616402

def SurrogateDiagonalTailChunk000Sub000Block173Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7187
    = surrogateDiagTailX0RatChunk000Sub000Block173Part011

theorem surrogateDiagonalTailChunk000Sub000Block173Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block173Part011CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block173Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block173Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block173Part011CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block173Part011SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block173Part011] using hcert

def TailChunk000Sub000Block173Part012SupportExplicit : Finset ℕ :=
  ([7189] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block173Part012 : ℚ :=
  (2341319035675 : ℚ) / 2487340580582227968

def SurrogateDiagonalTailChunk000Sub000Block173Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7189
    = surrogateDiagTailX0RatChunk000Sub000Block173Part012

theorem surrogateDiagonalTailChunk000Sub000Block173Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block173Part012CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block173Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block173Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block173Part012CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block173Part012SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block173Part012] using hcert

def TailChunk000Sub000Block173Part013SupportExplicit : Finset ℕ :=
  ([7190] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block173Part013 : ℚ :=
  (710211151975 : ℚ) / 170123614447945728

def SurrogateDiagonalTailChunk000Sub000Block173Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7190
    = surrogateDiagTailX0RatChunk000Sub000Block173Part013

theorem surrogateDiagonalTailChunk000Sub000Block173Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block173Part013CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block173Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block173Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block173Part013CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block173Part013SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block173Part013] using hcert

def TailChunk000Sub000Block173Part014SupportExplicit : Finset ℕ :=
  ([7193] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block173Part014 : ℚ :=
  (808425765625 : ℚ) / 1672497905081037312

def SurrogateDiagonalTailChunk000Sub000Block173Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7193
    = surrogateDiagTailX0RatChunk000Sub000Block173Part014

theorem surrogateDiagonalTailChunk000Sub000Block173Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block173Part014CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block173Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block173Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block173Part014CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block173Part014SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block173Part014] using hcert

def TailChunk000Sub000Block173Part015SupportExplicit : Finset ℕ :=
  ([7194] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block173Part015 : ℚ :=
  (7704657797 : ℚ) / 725739230822400

def SurrogateDiagonalTailChunk000Sub000Block173Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7194
    = surrogateDiagTailX0RatChunk000Sub000Block173Part015

theorem surrogateDiagonalTailChunk000Sub000Block173Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block173Part015CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block173Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block173Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block173Part015CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block173Part015SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block173Part015] using hcert

def TailChunk000Sub000Block173Part016SupportExplicit : Finset ℕ :=
  ([7195] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block173Part016 : ℚ :=
  (775978880475 : ℚ) / 912391254207502336

def SurrogateDiagonalTailChunk000Sub000Block173Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7195
    = surrogateDiagTailX0RatChunk000Sub000Block173Part016

theorem surrogateDiagonalTailChunk000Sub000Block173Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block173Part016CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block173Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block173Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block173Part016CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block173Part016SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block173Part016] using hcert

def TailChunk000Sub000Block173Part017SupportExplicit : Finset ℕ :=
  ([7197] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block173Part017 : ℚ :=
  (449478411925 : ℚ) / 330737595924486432

def SurrogateDiagonalTailChunk000Sub000Block173Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7197
    = surrogateDiagTailX0RatChunk000Sub000Block173Part017

theorem surrogateDiagonalTailChunk000Sub000Block173Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block173Part017CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block173Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block173Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block173Part017CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block173Part017SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block173Part017] using hcert

def TailChunk000Sub000Block173Part018SupportExplicit : Finset ℕ :=
  ([7198] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block173Part018 : ℚ :=
  (30996067931 : ℚ) / 7334556025881600

def SurrogateDiagonalTailChunk000Sub000Block173Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7198
    = surrogateDiagTailX0RatChunk000Sub000Block173Part018

theorem surrogateDiagonalTailChunk000Sub000Block173Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block173Part018CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block173Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block173Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block173Part018CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block173Part018SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block173Part018] using hcert

def TailChunk000Sub000Block173Part019SupportExplicit : Finset ℕ :=
  ([7199] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block173Part019 : ℚ :=
  (58524924175 : ℚ) / 106741331176955904

def SurrogateDiagonalTailChunk000Sub000Block173Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7199
    = surrogateDiagTailX0RatChunk000Sub000Block173Part019

theorem surrogateDiagonalTailChunk000Sub000Block173Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block173Part019CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block173Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block173Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block173Part019CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block173Part019SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block173Part019] using hcert

def TailChunk000Sub000Block173Part020SupportExplicit : Finset ℕ :=
  ([7201] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block173Part020 : ℚ :=
  (3006701241925 : ℚ) / 5359003968429030528

def SurrogateDiagonalTailChunk000Sub000Block173Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7201
    = surrogateDiagTailX0RatChunk000Sub000Block173Part020

theorem surrogateDiagonalTailChunk000Sub000Block173Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block173Part020CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block173Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block173Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block173Part020CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block173Part020SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block173Part020] using hcert

def TailChunk000Sub000Block173Part021SupportExplicit : Finset ℕ :=
  ([7202] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block173Part021 : ℚ :=
  (362826888475 : ℚ) / 75219108182433792

def SurrogateDiagonalTailChunk000Sub000Block173Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7202
    = surrogateDiagTailX0RatChunk000Sub000Block173Part021

theorem surrogateDiagonalTailChunk000Sub000Block173Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block173Part021CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block173Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block173Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block173Part021CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block173Part021SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block173Part021] using hcert

def TailChunk000Sub000Block173Part022SupportExplicit : Finset ℕ :=
  ([7205] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block173Part022 : ℚ :=
  (21506235691 : ℚ) / 18282695808000000

def SurrogateDiagonalTailChunk000Sub000Block173Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7205
    = surrogateDiagTailX0RatChunk000Sub000Block173Part022

theorem surrogateDiagonalTailChunk000Sub000Block173Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block173Part022CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block173Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block173Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block173Part022CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block173Part022SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block173Part022] using hcert

def TailChunk000Sub000Block173Part023SupportExplicit : Finset ℕ :=
  ([7206] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block173Part023 : ℚ :=
  (18014650097 : ℚ) / 1659211776000000

def SurrogateDiagonalTailChunk000Sub000Block173Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7206
    = surrogateDiagTailX0RatChunk000Sub000Block173Part023

theorem surrogateDiagonalTailChunk000Sub000Block173Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block173Part023CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block173Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block173Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block173Part023CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block173Part023SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block173Part023] using hcert

def TailChunk000Sub000Block173Part024SupportExplicit : Finset ℕ :=
  ([7207] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block173Part024 : ℚ :=
  (811575765625 : ℚ) / 1685558766633267762

def SurrogateDiagonalTailChunk000Sub000Block173Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7207
    = surrogateDiagTailX0RatChunk000Sub000Block173Part024

theorem surrogateDiagonalTailChunk000Sub000Block173Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block173Part024CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block173Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block173Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block173Part024CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block173Part024SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block173Part024] using hcert

def surrogateDiagonalTailChunk000Sub000Block173HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block173Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block173Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block173Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block173Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block173Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block173Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block173Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block173Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block173Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block173Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block173Head : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block173Part000
    + surrogateDiagTailX0RatChunk000Sub000Block173Part001
    + surrogateDiagTailX0RatChunk000Sub000Block173Part002
    + surrogateDiagTailX0RatChunk000Sub000Block173Part003
    + surrogateDiagTailX0RatChunk000Sub000Block173Part004
    + surrogateDiagTailX0RatChunk000Sub000Block173Part005
    + surrogateDiagTailX0RatChunk000Sub000Block173Part006
    + surrogateDiagTailX0RatChunk000Sub000Block173Part007
    + surrogateDiagTailX0RatChunk000Sub000Block173Part008
    + surrogateDiagTailX0RatChunk000Sub000Block173Part009

def surrogateDiagonalTailChunk000Sub000Block173MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block173Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block173Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block173Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block173Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block173Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block173Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block173Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block173Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block173Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block173Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block173Mid : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block173Part010
    + surrogateDiagTailX0RatChunk000Sub000Block173Part011
    + surrogateDiagTailX0RatChunk000Sub000Block173Part012
    + surrogateDiagTailX0RatChunk000Sub000Block173Part013
    + surrogateDiagTailX0RatChunk000Sub000Block173Part014
    + surrogateDiagTailX0RatChunk000Sub000Block173Part015
    + surrogateDiagTailX0RatChunk000Sub000Block173Part016
    + surrogateDiagTailX0RatChunk000Sub000Block173Part017
    + surrogateDiagTailX0RatChunk000Sub000Block173Part018
    + surrogateDiagTailX0RatChunk000Sub000Block173Part019

def surrogateDiagonalTailChunk000Sub000Block173TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block173Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block173Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block173Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block173Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block173Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block173Tail : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block173Part020
    + surrogateDiagTailX0RatChunk000Sub000Block173Part021
    + surrogateDiagTailX0RatChunk000Sub000Block173Part022
    + surrogateDiagTailX0RatChunk000Sub000Block173Part023
    + surrogateDiagTailX0RatChunk000Sub000Block173Part024

def surrogateDiagonalTailChunk000Sub000Block173Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub000Block173HeadSum X0
    + surrogateDiagonalTailChunk000Sub000Block173MidSum X0
    + surrogateDiagonalTailChunk000Sub000Block173TailSum X0

def surrogateDiagTailX0RatChunk000Sub000Block173 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block173Part000
    + surrogateDiagTailX0RatChunk000Sub000Block173Part001
    + surrogateDiagTailX0RatChunk000Sub000Block173Part002
    + surrogateDiagTailX0RatChunk000Sub000Block173Part003
    + surrogateDiagTailX0RatChunk000Sub000Block173Part004
    + surrogateDiagTailX0RatChunk000Sub000Block173Part005
    + surrogateDiagTailX0RatChunk000Sub000Block173Part006
    + surrogateDiagTailX0RatChunk000Sub000Block173Part007
    + surrogateDiagTailX0RatChunk000Sub000Block173Part008
    + surrogateDiagTailX0RatChunk000Sub000Block173Part009
    + surrogateDiagTailX0RatChunk000Sub000Block173Part010
    + surrogateDiagTailX0RatChunk000Sub000Block173Part011
    + surrogateDiagTailX0RatChunk000Sub000Block173Part012
    + surrogateDiagTailX0RatChunk000Sub000Block173Part013
    + surrogateDiagTailX0RatChunk000Sub000Block173Part014
    + surrogateDiagTailX0RatChunk000Sub000Block173Part015
    + surrogateDiagTailX0RatChunk000Sub000Block173Part016
    + surrogateDiagTailX0RatChunk000Sub000Block173Part017
    + surrogateDiagTailX0RatChunk000Sub000Block173Part018
    + surrogateDiagTailX0RatChunk000Sub000Block173Part019
    + surrogateDiagTailX0RatChunk000Sub000Block173Part020
    + surrogateDiagTailX0RatChunk000Sub000Block173Part021
    + surrogateDiagTailX0RatChunk000Sub000Block173Part022
    + surrogateDiagTailX0RatChunk000Sub000Block173Part023
    + surrogateDiagTailX0RatChunk000Sub000Block173Part024

theorem surrogateDiagTailX0RatChunk000Sub000Block173_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk000Sub000Block173Head + surrogateDiagTailX0RatChunk000Sub000Block173Mid + surrogateDiagTailX0RatChunk000Sub000Block173Tail =
      surrogateDiagTailX0RatChunk000Sub000Block173 := by
  unfold surrogateDiagTailX0RatChunk000Sub000Block173Head surrogateDiagTailX0RatChunk000Sub000Block173Mid surrogateDiagTailX0RatChunk000Sub000Block173Tail surrogateDiagTailX0RatChunk000Sub000Block173
  ring

def SurrogateDiagonalTailChunk000Sub000Block173HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block173HeadSum X0 = surrogateDiagTailX0RatChunk000Sub000Block173Head

def SurrogateDiagonalTailChunk000Sub000Block173MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block173MidSum X0 = surrogateDiagTailX0RatChunk000Sub000Block173Mid

def SurrogateDiagonalTailChunk000Sub000Block173TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block173TailSum X0 = surrogateDiagTailX0RatChunk000Sub000Block173Tail

theorem surrogateDiagonalTailChunk000Sub000Block173_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk000Sub000Block173HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk000Sub000Block173MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk000Sub000Block173TailCertificateAt X0) :
    surrogateDiagonalTailChunk000Sub000Block173Sum X0 = surrogateDiagTailX0RatChunk000Sub000Block173 := by
  unfold SurrogateDiagonalTailChunk000Sub000Block173HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk000Sub000Block173MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk000Sub000Block173TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk000Sub000Block173Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk000Sub000Block173_eq_head_add_mid_add_tail

/-- Block 174 covers tail-support indices [4350,4375) and q from 7210 to 7247. -/

def TailChunk000Sub000Block174Part000SupportExplicit : Finset ℕ :=
  ([7210] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block174Part000 : ℚ :=
  (489191460275 : ℚ) / 44899604664827904

def SurrogateDiagonalTailChunk000Sub000Block174Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7210
    = surrogateDiagTailX0RatChunk000Sub000Block174Part000

theorem surrogateDiagonalTailChunk000Sub000Block174Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block174Part000CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block174Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block174Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block174Part000CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block174Part000SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block174Part000] using hcert

def TailChunk000Sub000Block174Part001SupportExplicit : Finset ℕ :=
  ([7211] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block174Part001 : ℚ :=
  (1299963025 : ℚ) / 2702887122140562

def SurrogateDiagonalTailChunk000Sub000Block174Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7211
    = surrogateDiagTailX0RatChunk000Sub000Block174Part001

theorem surrogateDiagonalTailChunk000Sub000Block174Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block174Part001CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block174Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block174Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block174Part001CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block174Part001SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block174Part001] using hcert

def TailChunk000Sub000Block174Part002SupportExplicit : Finset ℕ :=
  ([7213] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block174Part002 : ℚ :=
  (812927640625 : ℚ) / 1691179633009903392

def SurrogateDiagonalTailChunk000Sub000Block174Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7213
    = surrogateDiagTailX0RatChunk000Sub000Block174Part002

theorem surrogateDiagonalTailChunk000Sub000Block174Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block174Part002CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block174Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block174Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block174Part002CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block174Part002SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block174Part002] using hcert

def TailChunk000Sub000Block174Part003SupportExplicit : Finset ℕ :=
  ([7214] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block174Part003 : ℚ :=
  (1625980863775 : ℚ) / 422794908252475848

def SurrogateDiagonalTailChunk000Sub000Block174Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7214
    = surrogateDiagTailX0RatChunk000Sub000Block174Part003

theorem surrogateDiagonalTailChunk000Sub000Block174Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block174Part003CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block174Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block174Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block174Part003CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block174Part003SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block174Part003] using hcert

def TailChunk000Sub000Block174Part004SupportExplicit : Finset ℕ :=
  ([7215] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block174Part004 : ℚ :=
  (684206167375 : ℚ) / 356715346733826048

def SurrogateDiagonalTailChunk000Sub000Block174Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7215
    = surrogateDiagTailX0RatChunk000Sub000Block174Part004

theorem surrogateDiagonalTailChunk000Sub000Block174Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block174Part004CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block174Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block174Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block174Part004CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block174Part004SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block174Part004] using hcert

def TailChunk000Sub000Block174Part005SupportExplicit : Finset ℕ :=
  ([7217] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block174Part005 : ℚ :=
  (13325610691 : ℚ) / 145895114964355200

def SurrogateDiagonalTailChunk000Sub000Block174Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7217
    = surrogateDiagTailX0RatChunk000Sub000Block174Part005

theorem surrogateDiagonalTailChunk000Sub000Block174Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block174Part005CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block174Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block174Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block174Part005CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block174Part005SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block174Part005] using hcert

def TailChunk000Sub000Block174Part006SupportExplicit : Finset ℕ :=
  ([7219] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block174Part006 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub000Block174Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7219
    = surrogateDiagTailX0RatChunk000Sub000Block174Part006

theorem surrogateDiagonalTailChunk000Sub000Block174Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block174Part006CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block174Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block174Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block174Part006CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block174Part006SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block174Part006] using hcert

def TailChunk000Sub000Block174Part007SupportExplicit : Finset ℕ :=
  ([7221] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block174Part007 : ℚ :=
  (17278709025 : ℚ) / 26471898322386944

def SurrogateDiagonalTailChunk000Sub000Block174Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7221
    = surrogateDiagTailX0RatChunk000Sub000Block174Part007

theorem surrogateDiagonalTailChunk000Sub000Block174Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block174Part007CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block174Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block174Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block174Part007CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block174Part007SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block174Part007] using hcert

def TailChunk000Sub000Block174Part008SupportExplicit : Finset ℕ :=
  ([7222] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block174Part008 : ℚ :=
  (98784935825 : ℚ) / 43363665790638336

def SurrogateDiagonalTailChunk000Sub000Block174Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7222
    = surrogateDiagTailX0RatChunk000Sub000Block174Part008

theorem surrogateDiagonalTailChunk000Sub000Block174Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block174Part008CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block174Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block174Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block174Part008CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block174Part008SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block174Part008] using hcert

def TailChunk000Sub000Block174Part009SupportExplicit : Finset ℕ :=
  ([7223] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block174Part009 : ℚ :=
  (22911691 : ℚ) / 1618660640194560

def SurrogateDiagonalTailChunk000Sub000Block174Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7223
    = surrogateDiagTailX0RatChunk000Sub000Block174Part009

theorem surrogateDiagonalTailChunk000Sub000Block174Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block174Part009CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block174Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block174Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block174Part009CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block174Part009SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block174Part009] using hcert

def TailChunk000Sub000Block174Part010SupportExplicit : Finset ℕ :=
  ([7226] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block174Part010 : ℚ :=
  (203965140625 : ℚ) / 106403970503752992

def SurrogateDiagonalTailChunk000Sub000Block174Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7226
    = surrogateDiagTailX0RatChunk000Sub000Block174Part010

theorem surrogateDiagonalTailChunk000Sub000Block174Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block174Part010CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block174Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block174Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block174Part010CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block174Part010SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block174Part010] using hcert

def TailChunk000Sub000Block174Part011SupportExplicit : Finset ℕ :=
  ([7229] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block174Part011 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub000Block174Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7229
    = surrogateDiagTailX0RatChunk000Sub000Block174Part011

theorem surrogateDiagonalTailChunk000Sub000Block174Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block174Part011CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block174Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block174Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block174Part011CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block174Part011SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block174Part011] using hcert

def TailChunk000Sub000Block174Part012SupportExplicit : Finset ℕ :=
  ([7230] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block174Part012 : ℚ :=
  (3615649 : ℚ) / 209757143040

def SurrogateDiagonalTailChunk000Sub000Block174Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7230
    = surrogateDiagTailX0RatChunk000Sub000Block174Part012

theorem surrogateDiagonalTailChunk000Sub000Block174Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block174Part012CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block174Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block174Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block174Part012CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block174Part012SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block174Part012] using hcert

def TailChunk000Sub000Block174Part013SupportExplicit : Finset ℕ :=
  ([7231] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block174Part013 : ℚ :=
  (267970705525 : ℚ) / 3675789641592373248

def SurrogateDiagonalTailChunk000Sub000Block174Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7231
    = surrogateDiagTailX0RatChunk000Sub000Block174Part013

theorem surrogateDiagonalTailChunk000Sub000Block174Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block174Part013CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block174Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block174Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block174Part013CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block174Part013SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block174Part013] using hcert

def TailChunk000Sub000Block174Part014SupportExplicit : Finset ℕ :=
  ([7233] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block174Part014 : ℚ :=
  (14529843629 : ℚ) / 26992617932097600

def SurrogateDiagonalTailChunk000Sub000Block174Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7233
    = surrogateDiagTailX0RatChunk000Sub000Block174Part014

theorem surrogateDiagonalTailChunk000Sub000Block174Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block174Part014CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block174Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block174Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block174Part014CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block174Part014SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block174Part014] using hcert

def TailChunk000Sub000Block174Part015SupportExplicit : Finset ℕ :=
  ([7234] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block174Part015 : ℚ :=
  (204417015625 : ℚ) / 106876089448660992

def SurrogateDiagonalTailChunk000Sub000Block174Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7234
    = surrogateDiagTailX0RatChunk000Sub000Block174Part015

theorem surrogateDiagonalTailChunk000Sub000Block174Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block174Part015CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block174Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block174Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block174Part015CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block174Part015SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block174Part015] using hcert

def TailChunk000Sub000Block174Part016SupportExplicit : Finset ℕ :=
  ([7235] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block174Part016 : ℚ :=
  (49142529275 : ℚ) / 349824328399984896

def SurrogateDiagonalTailChunk000Sub000Block174Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7235
    = surrogateDiagTailX0RatChunk000Sub000Block174Part016

theorem surrogateDiagonalTailChunk000Sub000Block174Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block174Part016CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block174Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block174Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block174Part016CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block174Part016SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block174Part016] using hcert

def TailChunk000Sub000Block174Part017SupportExplicit : Finset ℕ :=
  ([7237] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block174Part017 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub000Block174Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7237
    = surrogateDiagTailX0RatChunk000Sub000Block174Part017

theorem surrogateDiagonalTailChunk000Sub000Block174Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block174Part017CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block174Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block174Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block174Part017CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block174Part017SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block174Part017] using hcert

def TailChunk000Sub000Block174Part018SupportExplicit : Finset ℕ :=
  ([7238] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block174Part018 : ℚ :=
  (3013816537 : ℚ) / 644882614732800

def SurrogateDiagonalTailChunk000Sub000Block174Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7238
    = surrogateDiagTailX0RatChunk000Sub000Block174Part018

theorem surrogateDiagonalTailChunk000Sub000Block174Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block174Part018CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block174Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block174Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block174Part018CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block174Part018SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block174Part018] using hcert

def TailChunk000Sub000Block174Part019SupportExplicit : Finset ℕ :=
  ([7239] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block174Part019 : ℚ :=
  (236300675 : ℚ) / 342911786563584

def SurrogateDiagonalTailChunk000Sub000Block174Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7239
    = surrogateDiagTailX0RatChunk000Sub000Block174Part019

theorem surrogateDiagonalTailChunk000Sub000Block174Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block174Part019CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block174Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block174Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block174Part019CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block174Part019SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block174Part019] using hcert

def TailChunk000Sub000Block174Part020SupportExplicit : Finset ℕ :=
  ([7241] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block174Part020 : ℚ :=
  (177362837275 : ℚ) / 4955083865762070528

def SurrogateDiagonalTailChunk000Sub000Block174Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7241
    = surrogateDiagTailX0RatChunk000Sub000Block174Part020

theorem surrogateDiagonalTailChunk000Sub000Block174Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block174Part020CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block174Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block174Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block174Part020CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block174Part020SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block174Part020] using hcert

def TailChunk000Sub000Block174Part021SupportExplicit : Finset ℕ :=
  ([7242] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block174Part021 : ℚ :=
  (23968192561 : ℚ) / 2518134502195200

def SurrogateDiagonalTailChunk000Sub000Block174Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7242
    = surrogateDiagTailX0RatChunk000Sub000Block174Part021

theorem surrogateDiagonalTailChunk000Sub000Block174Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block174Part021CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block174Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block174Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block174Part021CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block174Part021SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block174Part021] using hcert

def TailChunk000Sub000Block174Part022SupportExplicit : Finset ℕ :=
  ([7243] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block174Part022 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub000Block174Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7243
    = surrogateDiagTailX0RatChunk000Sub000Block174Part022

theorem surrogateDiagonalTailChunk000Sub000Block174Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block174Part022CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block174Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block174Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block174Part022CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block174Part022SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block174Part022] using hcert

def TailChunk000Sub000Block174Part023SupportExplicit : Finset ℕ :=
  ([7246] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block174Part023 : ℚ :=
  (205095765625 : ℚ) / 107587211518085682

def SurrogateDiagonalTailChunk000Sub000Block174Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7246
    = surrogateDiagTailX0RatChunk000Sub000Block174Part023

theorem surrogateDiagonalTailChunk000Sub000Block174Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block174Part023CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block174Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block174Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block174Part023CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block174Part023SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block174Part023] using hcert

def TailChunk000Sub000Block174Part024SupportExplicit : Finset ℕ :=
  ([7247] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block174Part024 : ℚ :=
  (820609515625 : ℚ) / 1723297215771459282

def SurrogateDiagonalTailChunk000Sub000Block174Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7247
    = surrogateDiagTailX0RatChunk000Sub000Block174Part024

theorem surrogateDiagonalTailChunk000Sub000Block174Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block174Part024CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block174Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block174Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block174Part024CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block174Part024SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block174Part024] using hcert

def surrogateDiagonalTailChunk000Sub000Block174HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block174Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block174Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block174Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block174Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block174Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block174Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block174Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block174Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block174Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block174Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block174Head : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block174Part000
    + surrogateDiagTailX0RatChunk000Sub000Block174Part001
    + surrogateDiagTailX0RatChunk000Sub000Block174Part002
    + surrogateDiagTailX0RatChunk000Sub000Block174Part003
    + surrogateDiagTailX0RatChunk000Sub000Block174Part004
    + surrogateDiagTailX0RatChunk000Sub000Block174Part005
    + surrogateDiagTailX0RatChunk000Sub000Block174Part006
    + surrogateDiagTailX0RatChunk000Sub000Block174Part007
    + surrogateDiagTailX0RatChunk000Sub000Block174Part008
    + surrogateDiagTailX0RatChunk000Sub000Block174Part009

def surrogateDiagonalTailChunk000Sub000Block174MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block174Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block174Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block174Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block174Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block174Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block174Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block174Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block174Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block174Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block174Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block174Mid : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block174Part010
    + surrogateDiagTailX0RatChunk000Sub000Block174Part011
    + surrogateDiagTailX0RatChunk000Sub000Block174Part012
    + surrogateDiagTailX0RatChunk000Sub000Block174Part013
    + surrogateDiagTailX0RatChunk000Sub000Block174Part014
    + surrogateDiagTailX0RatChunk000Sub000Block174Part015
    + surrogateDiagTailX0RatChunk000Sub000Block174Part016
    + surrogateDiagTailX0RatChunk000Sub000Block174Part017
    + surrogateDiagTailX0RatChunk000Sub000Block174Part018
    + surrogateDiagTailX0RatChunk000Sub000Block174Part019

def surrogateDiagonalTailChunk000Sub000Block174TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block174Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block174Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block174Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block174Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block174Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block174Tail : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block174Part020
    + surrogateDiagTailX0RatChunk000Sub000Block174Part021
    + surrogateDiagTailX0RatChunk000Sub000Block174Part022
    + surrogateDiagTailX0RatChunk000Sub000Block174Part023
    + surrogateDiagTailX0RatChunk000Sub000Block174Part024

def surrogateDiagonalTailChunk000Sub000Block174Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub000Block174HeadSum X0
    + surrogateDiagonalTailChunk000Sub000Block174MidSum X0
    + surrogateDiagonalTailChunk000Sub000Block174TailSum X0

def surrogateDiagTailX0RatChunk000Sub000Block174 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block174Part000
    + surrogateDiagTailX0RatChunk000Sub000Block174Part001
    + surrogateDiagTailX0RatChunk000Sub000Block174Part002
    + surrogateDiagTailX0RatChunk000Sub000Block174Part003
    + surrogateDiagTailX0RatChunk000Sub000Block174Part004
    + surrogateDiagTailX0RatChunk000Sub000Block174Part005
    + surrogateDiagTailX0RatChunk000Sub000Block174Part006
    + surrogateDiagTailX0RatChunk000Sub000Block174Part007
    + surrogateDiagTailX0RatChunk000Sub000Block174Part008
    + surrogateDiagTailX0RatChunk000Sub000Block174Part009
    + surrogateDiagTailX0RatChunk000Sub000Block174Part010
    + surrogateDiagTailX0RatChunk000Sub000Block174Part011
    + surrogateDiagTailX0RatChunk000Sub000Block174Part012
    + surrogateDiagTailX0RatChunk000Sub000Block174Part013
    + surrogateDiagTailX0RatChunk000Sub000Block174Part014
    + surrogateDiagTailX0RatChunk000Sub000Block174Part015
    + surrogateDiagTailX0RatChunk000Sub000Block174Part016
    + surrogateDiagTailX0RatChunk000Sub000Block174Part017
    + surrogateDiagTailX0RatChunk000Sub000Block174Part018
    + surrogateDiagTailX0RatChunk000Sub000Block174Part019
    + surrogateDiagTailX0RatChunk000Sub000Block174Part020
    + surrogateDiagTailX0RatChunk000Sub000Block174Part021
    + surrogateDiagTailX0RatChunk000Sub000Block174Part022
    + surrogateDiagTailX0RatChunk000Sub000Block174Part023
    + surrogateDiagTailX0RatChunk000Sub000Block174Part024

theorem surrogateDiagTailX0RatChunk000Sub000Block174_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk000Sub000Block174Head + surrogateDiagTailX0RatChunk000Sub000Block174Mid + surrogateDiagTailX0RatChunk000Sub000Block174Tail =
      surrogateDiagTailX0RatChunk000Sub000Block174 := by
  unfold surrogateDiagTailX0RatChunk000Sub000Block174Head surrogateDiagTailX0RatChunk000Sub000Block174Mid surrogateDiagTailX0RatChunk000Sub000Block174Tail surrogateDiagTailX0RatChunk000Sub000Block174
  ring

def SurrogateDiagonalTailChunk000Sub000Block174HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block174HeadSum X0 = surrogateDiagTailX0RatChunk000Sub000Block174Head

def SurrogateDiagonalTailChunk000Sub000Block174MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block174MidSum X0 = surrogateDiagTailX0RatChunk000Sub000Block174Mid

def SurrogateDiagonalTailChunk000Sub000Block174TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block174TailSum X0 = surrogateDiagTailX0RatChunk000Sub000Block174Tail

theorem surrogateDiagonalTailChunk000Sub000Block174_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk000Sub000Block174HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk000Sub000Block174MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk000Sub000Block174TailCertificateAt X0) :
    surrogateDiagonalTailChunk000Sub000Block174Sum X0 = surrogateDiagTailX0RatChunk000Sub000Block174 := by
  unfold SurrogateDiagonalTailChunk000Sub000Block174HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk000Sub000Block174MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk000Sub000Block174TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk000Sub000Block174Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk000Sub000Block174_eq_head_add_mid_add_tail

/-- Block 175 covers tail-support indices [4375,4400) and q from 7249 to 7289. -/

def TailChunk000Sub000Block175Part000SupportExplicit : Finset ℕ :=
  ([7249] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block175Part000 : ℚ :=
  (115963959679 : ℚ) / 187495316861059200

def SurrogateDiagonalTailChunk000Sub000Block175Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7249
    = surrogateDiagTailX0RatChunk000Sub000Block175Part000

theorem surrogateDiagonalTailChunk000Sub000Block175Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block175Part000CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block175Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block175Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block175Part000CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block175Part000SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block175Part000] using hcert

def TailChunk000Sub000Block175Part001SupportExplicit : Finset ℕ :=
  ([7251] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block175Part001 : ℚ :=
  (912498364925 : ℚ) / 681560739833708544

def SurrogateDiagonalTailChunk000Sub000Block175Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7251
    = surrogateDiagTailX0RatChunk000Sub000Block175Part001

theorem surrogateDiagonalTailChunk000Sub000Block175Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block175Part001CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block175Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block175Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block175Part001CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block175Part001SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block175Part001] using hcert

def TailChunk000Sub000Block175Part002SupportExplicit : Finset ℕ :=
  ([7253] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block175Part002 : ℚ :=
  (821968890625 : ℚ) / 1729012166400382752

def SurrogateDiagonalTailChunk000Sub000Block175Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7253
    = surrogateDiagTailX0RatChunk000Sub000Block175Part002

theorem surrogateDiagonalTailChunk000Sub000Block175Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block175Part002CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block175Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block175Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block175Part002CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block175Part002SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block175Part002] using hcert

def TailChunk000Sub000Block175Part003SupportExplicit : Finset ℕ :=
  ([7255] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block175Part003 : ℚ :=
  (6246104959 : ℚ) / 7074224562000000

def SurrogateDiagonalTailChunk000Sub000Block175Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7255
    = surrogateDiagTailX0RatChunk000Sub000Block175Part003

theorem surrogateDiagonalTailChunk000Sub000Block175Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block175Part003CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block175Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block175Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block175Part003CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block175Part003SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block175Part003] using hcert

def TailChunk000Sub000Block175Part004SupportExplicit : Finset ℕ :=
  ([7257] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block175Part004 : ℚ :=
  (34833772223 : ℚ) / 23180819044761600

def SurrogateDiagonalTailChunk000Sub000Block175Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7257
    = surrogateDiagTailX0RatChunk000Sub000Block175Part004

theorem surrogateDiagonalTailChunk000Sub000Block175Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block175Part004CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block175Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block175Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block175Part004CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block175Part004SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block175Part004] using hcert

def TailChunk000Sub000Block175Part005SupportExplicit : Finset ℕ :=
  ([7258] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block175Part005 : ℚ :=
  (60880733431 : ℚ) / 13683313411459200

def SurrogateDiagonalTailChunk000Sub000Block175Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7258
    = surrogateDiagTailX0RatChunk000Sub000Block175Part005

theorem surrogateDiagonalTailChunk000Sub000Block175Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block175Part005CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block175Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block175Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block175Part005CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block175Part005SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block175Part005] using hcert

def TailChunk000Sub000Block175Part006SupportExplicit : Finset ℕ :=
  ([7259] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block175Part006 : ℚ :=
  (5950686949 : ℚ) / 6881083077427200

def SurrogateDiagonalTailChunk000Sub000Block175Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7259
    = surrogateDiagTailX0RatChunk000Sub000Block175Part006

theorem surrogateDiagonalTailChunk000Sub000Block175Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block175Part006CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block175Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block175Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block175Part006CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block175Part006SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block175Part006] using hcert

def TailChunk000Sub000Block175Part007SupportExplicit : Finset ℕ :=
  ([7261] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block175Part007 : ℚ :=
  (3184208889025 : ℚ) / 6254547093831548928

def SurrogateDiagonalTailChunk000Sub000Block175Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7261
    = surrogateDiagTailX0RatChunk000Sub000Block175Part007

theorem surrogateDiagonalTailChunk000Sub000Block175Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block175Part007CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block175Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block175Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block175Part007CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block175Part007SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block175Part007] using hcert

def TailChunk000Sub000Block175Part008SupportExplicit : Finset ℕ :=
  ([7262] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block175Part008 : ℚ :=
  (65907620839 : ℚ) / 17366541974872200

def SurrogateDiagonalTailChunk000Sub000Block175Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7262
    = surrogateDiagTailX0RatChunk000Sub000Block175Part008

theorem surrogateDiagonalTailChunk000Sub000Block175Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block175Part008CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block175Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block175Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block175Part008CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block175Part008SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block175Part008] using hcert

def TailChunk000Sub000Block175Part009SupportExplicit : Finset ℕ :=
  ([7265] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block175Part009 : ℚ :=
  (2373461223325 : ℚ) / 2845334237163061248

def SurrogateDiagonalTailChunk000Sub000Block175Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7265
    = surrogateDiagTailX0RatChunk000Sub000Block175Part009

theorem surrogateDiagonalTailChunk000Sub000Block175Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block175Part009CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block175Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block175Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block175Part009CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block175Part009SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block175Part009] using hcert

def TailChunk000Sub000Block175Part010SupportExplicit : Finset ℕ :=
  ([7266] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block175Part010 : ℚ :=
  (30549207125 : ℚ) / 1680745149333504

def SurrogateDiagonalTailChunk000Sub000Block175Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7266
    = surrogateDiagTailX0RatChunk000Sub000Block175Part010

theorem surrogateDiagonalTailChunk000Sub000Block175Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block175Part010CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block175Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block175Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block175Part010CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block175Part010SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block175Part010] using hcert

def TailChunk000Sub000Block175Part011SupportExplicit : Finset ℕ :=
  ([7269] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block175Part011 : ℚ :=
  (458517357775 : ℚ) / 344178236833550112

def SurrogateDiagonalTailChunk000Sub000Block175Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7269
    = surrogateDiagTailX0RatChunk000Sub000Block175Part011

theorem surrogateDiagonalTailChunk000Sub000Block175Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block175Part011CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block175Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block175Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block175Part011CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block175Part011SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block175Part011] using hcert

def TailChunk000Sub000Block175Part012SupportExplicit : Finset ℕ :=
  ([7270] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block175Part012 : ℚ :=
  (242032582925 : ℚ) / 59277796607563776

def SurrogateDiagonalTailChunk000Sub000Block175Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7270
    = surrogateDiagTailX0RatChunk000Sub000Block175Part012

theorem surrogateDiagonalTailChunk000Sub000Block175Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block175Part012CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block175Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block175Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block175Part012CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block175Part012SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block175Part012] using hcert

def TailChunk000Sub000Block175Part013SupportExplicit : Finset ℕ :=
  ([7271] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block175Part013 : ℚ :=
  (350237809 : ℚ) / 575106998400000

def SurrogateDiagonalTailChunk000Sub000Block175Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7271
    = surrogateDiagTailX0RatChunk000Sub000Block175Part013

theorem surrogateDiagonalTailChunk000Sub000Block175Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block175Part013CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block175Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block175Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block175Part013CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block175Part013SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block175Part013] using hcert

def TailChunk000Sub000Block175Part014SupportExplicit : Finset ℕ :=
  ([7273] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block175Part014 : ℚ :=
  (2695966901875 : ℚ) / 3762021510812032128

def SurrogateDiagonalTailChunk000Sub000Block175Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7273
    = surrogateDiagTailX0RatChunk000Sub000Block175Part014

theorem surrogateDiagonalTailChunk000Sub000Block175Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block175Part014CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block175Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block175Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block175Part014CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block175Part014SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block175Part014] using hcert

def TailChunk000Sub000Block175Part015SupportExplicit : Finset ℕ :=
  ([7274] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block175Part015 : ℚ :=
  (206683890625 : ℚ) / 109260294243070752

def SurrogateDiagonalTailChunk000Sub000Block175Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7274
    = surrogateDiagTailX0RatChunk000Sub000Block175Part015

theorem surrogateDiagonalTailChunk000Sub000Block175Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block175Part015CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block175Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block175Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block175Part015CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block175Part015SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block175Part015] using hcert

def TailChunk000Sub000Block175Part016SupportExplicit : Finset ℕ :=
  ([7277] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block175Part016 : ℚ :=
  (3070552635925 : ℚ) / 5589466157070914688

def SurrogateDiagonalTailChunk000Sub000Block175Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7277
    = surrogateDiagTailX0RatChunk000Sub000Block175Part016

theorem surrogateDiagonalTailChunk000Sub000Block175Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block175Part016CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block175Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block175Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block175Part016CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block175Part016SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block175Part016] using hcert

def TailChunk000Sub000Block175Part017SupportExplicit : Finset ℕ :=
  ([7278] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block175Part017 : ℚ :=
  (643397952925 : ℚ) / 86329121377241088

def SurrogateDiagonalTailChunk000Sub000Block175Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7278
    = surrogateDiagTailX0RatChunk000Sub000Block175Part017

theorem surrogateDiagonalTailChunk000Sub000Block175Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block175Part017CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block175Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block175Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block175Part017CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block175Part017SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block175Part017] using hcert

def TailChunk000Sub000Block175Part018SupportExplicit : Finset ℕ :=
  ([7279] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block175Part018 : ℚ :=
  (41893878891 : ℚ) / 80049340000000000

def SurrogateDiagonalTailChunk000Sub000Block175Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7279
    = surrogateDiagTailX0RatChunk000Sub000Block175Part018

theorem surrogateDiagonalTailChunk000Sub000Block175Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block175Part018CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block175Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block175Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block175Part018CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block175Part018SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block175Part018] using hcert

def TailChunk000Sub000Block175Part019SupportExplicit : Finset ℕ :=
  ([7282] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block175Part019 : ℚ :=
  (15583340237 : ℚ) / 5930790921000000

def SurrogateDiagonalTailChunk000Sub000Block175Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7282
    = surrogateDiagTailX0RatChunk000Sub000Block175Part019

theorem surrogateDiagonalTailChunk000Sub000Block175Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block175Part019CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block175Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block175Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block175Part019CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block175Part019SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block175Part019] using hcert

def TailChunk000Sub000Block175Part020SupportExplicit : Finset ℕ :=
  ([7283] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block175Part020 : ℚ :=
  (828782640625 : ℚ) / 1757800428269306322

def SurrogateDiagonalTailChunk000Sub000Block175Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7283
    = surrogateDiagTailX0RatChunk000Sub000Block175Part020

theorem surrogateDiagonalTailChunk000Sub000Block175Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block175Part020CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block175Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block175Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block175Part020CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block175Part020SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block175Part020] using hcert

def TailChunk000Sub000Block175Part021SupportExplicit : Finset ℕ :=
  ([7285] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block175Part021 : ℚ :=
  (7443882451 : ℚ) / 7738591376793600

def SurrogateDiagonalTailChunk000Sub000Block175Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7285
    = surrogateDiagTailX0RatChunk000Sub000Block175Part021

theorem surrogateDiagonalTailChunk000Sub000Block175Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block175Part021CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block175Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block175Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block175Part021CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block175Part021SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block175Part021] using hcert

def TailChunk000Sub000Block175Part022SupportExplicit : Finset ℕ :=
  ([7286] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block175Part022 : ℚ :=
  (207366390625 : ℚ) / 109983271392637362

def SurrogateDiagonalTailChunk000Sub000Block175Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7286
    = surrogateDiagTailX0RatChunk000Sub000Block175Part022

theorem surrogateDiagonalTailChunk000Sub000Block175Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block175Part022CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block175Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block175Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block175Part022CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block175Part022SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block175Part022] using hcert

def TailChunk000Sub000Block175Part023SupportExplicit : Finset ℕ :=
  ([7287] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block175Part023 : ℚ :=
  (768915540725 : ℚ) / 371557680080200704

def SurrogateDiagonalTailChunk000Sub000Block175Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7287
    = surrogateDiagTailX0RatChunk000Sub000Block175Part023

theorem surrogateDiagonalTailChunk000Sub000Block175Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block175Part023CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block175Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block175Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block175Part023CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block175Part023SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block175Part023] using hcert

def TailChunk000Sub000Block175Part024SupportExplicit : Finset ℕ :=
  ([7289] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block175Part024 : ℚ :=
  (117816389225 : ℚ) / 229560616931917824

def SurrogateDiagonalTailChunk000Sub000Block175Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7289
    = surrogateDiagTailX0RatChunk000Sub000Block175Part024

theorem surrogateDiagonalTailChunk000Sub000Block175Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block175Part024CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block175Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block175Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block175Part024CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block175Part024SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block175Part024] using hcert

def surrogateDiagonalTailChunk000Sub000Block175HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block175Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block175Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block175Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block175Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block175Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block175Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block175Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block175Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block175Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block175Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block175Head : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block175Part000
    + surrogateDiagTailX0RatChunk000Sub000Block175Part001
    + surrogateDiagTailX0RatChunk000Sub000Block175Part002
    + surrogateDiagTailX0RatChunk000Sub000Block175Part003
    + surrogateDiagTailX0RatChunk000Sub000Block175Part004
    + surrogateDiagTailX0RatChunk000Sub000Block175Part005
    + surrogateDiagTailX0RatChunk000Sub000Block175Part006
    + surrogateDiagTailX0RatChunk000Sub000Block175Part007
    + surrogateDiagTailX0RatChunk000Sub000Block175Part008
    + surrogateDiagTailX0RatChunk000Sub000Block175Part009

def surrogateDiagonalTailChunk000Sub000Block175MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block175Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block175Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block175Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block175Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block175Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block175Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block175Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block175Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block175Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block175Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block175Mid : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block175Part010
    + surrogateDiagTailX0RatChunk000Sub000Block175Part011
    + surrogateDiagTailX0RatChunk000Sub000Block175Part012
    + surrogateDiagTailX0RatChunk000Sub000Block175Part013
    + surrogateDiagTailX0RatChunk000Sub000Block175Part014
    + surrogateDiagTailX0RatChunk000Sub000Block175Part015
    + surrogateDiagTailX0RatChunk000Sub000Block175Part016
    + surrogateDiagTailX0RatChunk000Sub000Block175Part017
    + surrogateDiagTailX0RatChunk000Sub000Block175Part018
    + surrogateDiagTailX0RatChunk000Sub000Block175Part019

def surrogateDiagonalTailChunk000Sub000Block175TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block175Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block175Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block175Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block175Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block175Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block175Tail : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block175Part020
    + surrogateDiagTailX0RatChunk000Sub000Block175Part021
    + surrogateDiagTailX0RatChunk000Sub000Block175Part022
    + surrogateDiagTailX0RatChunk000Sub000Block175Part023
    + surrogateDiagTailX0RatChunk000Sub000Block175Part024

def surrogateDiagonalTailChunk000Sub000Block175Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub000Block175HeadSum X0
    + surrogateDiagonalTailChunk000Sub000Block175MidSum X0
    + surrogateDiagonalTailChunk000Sub000Block175TailSum X0

def surrogateDiagTailX0RatChunk000Sub000Block175 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block175Part000
    + surrogateDiagTailX0RatChunk000Sub000Block175Part001
    + surrogateDiagTailX0RatChunk000Sub000Block175Part002
    + surrogateDiagTailX0RatChunk000Sub000Block175Part003
    + surrogateDiagTailX0RatChunk000Sub000Block175Part004
    + surrogateDiagTailX0RatChunk000Sub000Block175Part005
    + surrogateDiagTailX0RatChunk000Sub000Block175Part006
    + surrogateDiagTailX0RatChunk000Sub000Block175Part007
    + surrogateDiagTailX0RatChunk000Sub000Block175Part008
    + surrogateDiagTailX0RatChunk000Sub000Block175Part009
    + surrogateDiagTailX0RatChunk000Sub000Block175Part010
    + surrogateDiagTailX0RatChunk000Sub000Block175Part011
    + surrogateDiagTailX0RatChunk000Sub000Block175Part012
    + surrogateDiagTailX0RatChunk000Sub000Block175Part013
    + surrogateDiagTailX0RatChunk000Sub000Block175Part014
    + surrogateDiagTailX0RatChunk000Sub000Block175Part015
    + surrogateDiagTailX0RatChunk000Sub000Block175Part016
    + surrogateDiagTailX0RatChunk000Sub000Block175Part017
    + surrogateDiagTailX0RatChunk000Sub000Block175Part018
    + surrogateDiagTailX0RatChunk000Sub000Block175Part019
    + surrogateDiagTailX0RatChunk000Sub000Block175Part020
    + surrogateDiagTailX0RatChunk000Sub000Block175Part021
    + surrogateDiagTailX0RatChunk000Sub000Block175Part022
    + surrogateDiagTailX0RatChunk000Sub000Block175Part023
    + surrogateDiagTailX0RatChunk000Sub000Block175Part024

theorem surrogateDiagTailX0RatChunk000Sub000Block175_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk000Sub000Block175Head + surrogateDiagTailX0RatChunk000Sub000Block175Mid + surrogateDiagTailX0RatChunk000Sub000Block175Tail =
      surrogateDiagTailX0RatChunk000Sub000Block175 := by
  unfold surrogateDiagTailX0RatChunk000Sub000Block175Head surrogateDiagTailX0RatChunk000Sub000Block175Mid surrogateDiagTailX0RatChunk000Sub000Block175Tail surrogateDiagTailX0RatChunk000Sub000Block175
  ring

def SurrogateDiagonalTailChunk000Sub000Block175HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block175HeadSum X0 = surrogateDiagTailX0RatChunk000Sub000Block175Head

def SurrogateDiagonalTailChunk000Sub000Block175MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block175MidSum X0 = surrogateDiagTailX0RatChunk000Sub000Block175Mid

def SurrogateDiagonalTailChunk000Sub000Block175TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block175TailSum X0 = surrogateDiagTailX0RatChunk000Sub000Block175Tail

theorem surrogateDiagonalTailChunk000Sub000Block175_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk000Sub000Block175HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk000Sub000Block175MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk000Sub000Block175TailCertificateAt X0) :
    surrogateDiagonalTailChunk000Sub000Block175Sum X0 = surrogateDiagTailX0RatChunk000Sub000Block175 := by
  unfold SurrogateDiagonalTailChunk000Sub000Block175HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk000Sub000Block175MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk000Sub000Block175TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk000Sub000Block175Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk000Sub000Block175_eq_head_add_mid_add_tail

/-- Block 176 covers tail-support indices [4400,4425) and q from 7291 to 7330. -/

def TailChunk000Sub000Block176Part000SupportExplicit : Finset ℕ :=
  ([7291] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block176Part000 : ℚ :=
  (32517220575 : ℚ) / 60840766885139648

def SurrogateDiagonalTailChunk000Sub000Block176Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7291
    = surrogateDiagTailX0RatChunk000Sub000Block176Part000

theorem surrogateDiagonalTailChunk000Sub000Block176Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block176Part000CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block176Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block176Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block176Part000CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block176Part000SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block176Part000] using hcert

def TailChunk000Sub000Block176Part001SupportExplicit : Finset ℕ :=
  ([7293] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block176Part001 : ℚ :=
  (55965245563 : ℚ) / 21747620590387200

def SurrogateDiagonalTailChunk000Sub000Block176Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7293
    = surrogateDiagTailX0RatChunk000Sub000Block176Part001

theorem surrogateDiagonalTailChunk000Sub000Block176Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block176Part001CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block176Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block176Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block176Part001CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block176Part001SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block176Part001] using hcert

def TailChunk000Sub000Block176Part002SupportExplicit : Finset ℕ :=
  ([7294] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block176Part002 : ℚ :=
  (3388860797 : ℚ) / 1053083278540800

def SurrogateDiagonalTailChunk000Sub000Block176Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7294
    = surrogateDiagTailX0RatChunk000Sub000Block176Part002

theorem surrogateDiagonalTailChunk000Sub000Block176Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block176Part002CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block176Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block176Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block176Part002CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block176Part002SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block176Part002] using hcert

def TailChunk000Sub000Block176Part003SupportExplicit : Finset ℕ :=
  ([7295] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block176Part003 : ℚ :=
  (105253050775 : ℚ) / 120527369552339712

def SurrogateDiagonalTailChunk000Sub000Block176Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7295
    = surrogateDiagTailX0RatChunk000Sub000Block176Part003

theorem surrogateDiagonalTailChunk000Sub000Block176Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block176Part003CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block176Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block176Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block176Part003CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block176Part003SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block176Part003] using hcert

def TailChunk000Sub000Block176Part004SupportExplicit : Finset ℕ :=
  ([7297] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block176Part004 : ℚ :=
  (831972015625 : ℚ) / 1771357289349906432

def SurrogateDiagonalTailChunk000Sub000Block176Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7297
    = surrogateDiagTailX0RatChunk000Sub000Block176Part004

theorem surrogateDiagonalTailChunk000Sub000Block176Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block176Part004CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block176Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block176Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block176Part004CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block176Part004SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block176Part004] using hcert

def TailChunk000Sub000Block176Part005SupportExplicit : Finset ℕ :=
  ([7298] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block176Part005 : ℚ :=
  (10853904477 : ℚ) / 5118423885414400

def SurrogateDiagonalTailChunk000Sub000Block176Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7298
    = surrogateDiagTailX0RatChunk000Sub000Block176Part005

theorem surrogateDiagonalTailChunk000Sub000Block176Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block176Part005CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block176Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block176Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block176Part005CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block176Part005SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block176Part005] using hcert

def TailChunk000Sub000Block176Part006SupportExplicit : Finset ℕ :=
  ([7302] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block176Part006 : ℚ :=
  (462447701225 : ℚ) / 43737217020985344

def SurrogateDiagonalTailChunk000Sub000Block176Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7302
    = surrogateDiagTailX0RatChunk000Sub000Block176Part006

theorem surrogateDiagonalTailChunk000Sub000Block176Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block176Part006CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block176Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block176Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block176Part006CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block176Part006SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block176Part006] using hcert

def TailChunk000Sub000Block176Part007SupportExplicit : Finset ℕ :=
  ([7303] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block176Part007 : ℚ :=
  (22426126325 : ℚ) / 44826530956048512

def SurrogateDiagonalTailChunk000Sub000Block176Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7303
    = surrogateDiagTailX0RatChunk000Sub000Block176Part007

theorem surrogateDiagonalTailChunk000Sub000Block176Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block176Part007CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block176Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block176Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block176Part007CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block176Part007SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block176Part007] using hcert

def TailChunk000Sub000Block176Part008SupportExplicit : Finset ℕ :=
  ([7305] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block176Part008 : ℚ :=
  (695158160675 : ℚ) / 285694505605545984

def SurrogateDiagonalTailChunk000Sub000Block176Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7305
    = surrogateDiagTailX0RatChunk000Sub000Block176Part008

theorem surrogateDiagonalTailChunk000Sub000Block176Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block176Part008CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block176Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block176Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block176Part008CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block176Part008SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block176Part008] using hcert

def TailChunk000Sub000Block176Part009SupportExplicit : Finset ℕ :=
  ([7306] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block176Part009 : ℚ :=
  (4978567409 : ℚ) / 1062337993113600

def SurrogateDiagonalTailChunk000Sub000Block176Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7306
    = surrogateDiagTailX0RatChunk000Sub000Block176Part009

theorem surrogateDiagonalTailChunk000Sub000Block176Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block176Part009CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block176Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block176Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block176Part009CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block176Part009SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block176Part009] using hcert

def TailChunk000Sub000Block176Part010SupportExplicit : Finset ℕ :=
  ([7307] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block176Part010 : ℚ :=
  (834253890625 : ℚ) / 1781088662095928562

def SurrogateDiagonalTailChunk000Sub000Block176Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7307
    = surrogateDiagTailX0RatChunk000Sub000Block176Part010

theorem surrogateDiagonalTailChunk000Sub000Block176Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block176Part010CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block176Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block176Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block176Part010CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block176Part010SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block176Part010] using hcert

def TailChunk000Sub000Block176Part011SupportExplicit : Finset ℕ :=
  ([7309] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block176Part011 : ℚ :=
  (834710640625 : ℚ) / 1783039738086849312

def SurrogateDiagonalTailChunk000Sub000Block176Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7309
    = surrogateDiagTailX0RatChunk000Sub000Block176Part011

theorem surrogateDiagonalTailChunk000Sub000Block176Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block176Part011CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block176Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block176Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block176Part011CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block176Part011SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block176Part011] using hcert

def TailChunk000Sub000Block176Part012SupportExplicit : Finset ℕ :=
  ([7310] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block176Part012 : ℚ :=
  (79337494925 : ℚ) / 9324292328128512

def SurrogateDiagonalTailChunk000Sub000Block176Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7310
    = surrogateDiagTailX0RatChunk000Sub000Block176Part012

theorem surrogateDiagonalTailChunk000Sub000Block176Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block176Part012CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block176Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block176Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block176Part012CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block176Part012SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block176Part012] using hcert

def TailChunk000Sub000Block176Part013SupportExplicit : Finset ℕ :=
  ([7311] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block176Part013 : ℚ :=
  (927663290675 : ℚ) / 704410760725668864

def SurrogateDiagonalTailChunk000Sub000Block176Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7311
    = surrogateDiagTailX0RatChunk000Sub000Block176Part013

theorem surrogateDiagonalTailChunk000Sub000Block176Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block176Part013CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block176Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block176Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block176Part013CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block176Part013SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block176Part013] using hcert

def TailChunk000Sub000Block176Part014SupportExplicit : Finset ℕ :=
  ([7313] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block176Part014 : ℚ :=
  (7197330877 : ℚ) / 14441330000462400

def SurrogateDiagonalTailChunk000Sub000Block176Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7313
    = surrogateDiagTailX0RatChunk000Sub000Block176Part014

theorem surrogateDiagonalTailChunk000Sub000Block176Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block176Part014CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block176Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block176Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block176Part014CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block176Part014SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block176Part014] using hcert

def TailChunk000Sub000Block176Part015SupportExplicit : Finset ℕ :=
  ([7314] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block176Part015 : ℚ :=
  (215507851375 : ℚ) / 17131324756795392

def SurrogateDiagonalTailChunk000Sub000Block176Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7314
    = surrogateDiagTailX0RatChunk000Sub000Block176Part015

theorem surrogateDiagonalTailChunk000Sub000Block176Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block176Part015CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block176Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block176Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block176Part015CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block176Part015SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block176Part015] using hcert

def TailChunk000Sub000Block176Part016SupportExplicit : Finset ℕ :=
  ([7315] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block176Part016 : ℚ :=
  (23123986127 : ℚ) / 11611827693158400

def SurrogateDiagonalTailChunk000Sub000Block176Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7315
    = surrogateDiagTailX0RatChunk000Sub000Block176Part016

theorem surrogateDiagonalTailChunk000Sub000Block176Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block176Part016CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block176Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block176Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block176Part016CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block176Part016SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block176Part016] using hcert

def TailChunk000Sub000Block176Part017SupportExplicit : Finset ℕ :=
  ([7318] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block176Part017 : ℚ :=
  (1673200417975 : ℚ) / 447715019022024648

def SurrogateDiagonalTailChunk000Sub000Block176Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7318
    = surrogateDiagTailX0RatChunk000Sub000Block176Part017

theorem surrogateDiagonalTailChunk000Sub000Block176Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block176Part017CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block176Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block176Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block176Part017CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block176Part017SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block176Part017] using hcert

def TailChunk000Sub000Block176Part018SupportExplicit : Finset ℕ :=
  ([7319] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block176Part018 : ℚ :=
  (10090831825 : ℚ) / 323278723584793728

def SurrogateDiagonalTailChunk000Sub000Block176Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7319
    = surrogateDiagTailX0RatChunk000Sub000Block176Part018

theorem surrogateDiagonalTailChunk000Sub000Block176Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block176Part018CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block176Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block176Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block176Part018CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block176Part018SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block176Part018] using hcert

def TailChunk000Sub000Block176Part019SupportExplicit : Finset ℕ :=
  ([7321] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block176Part019 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub000Block176Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7321
    = surrogateDiagTailX0RatChunk000Sub000Block176Part019

theorem surrogateDiagonalTailChunk000Sub000Block176Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block176Part019CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block176Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block176Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block176Part019CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block176Part019SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block176Part019] using hcert

def TailChunk000Sub000Block176Part020SupportExplicit : Finset ℕ :=
  ([7322] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block176Part020 : ℚ :=
  (751339329925 : ℚ) / 240610110429045888

def SurrogateDiagonalTailChunk000Sub000Block176Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7322
    = surrogateDiagTailX0RatChunk000Sub000Block176Part020

theorem surrogateDiagonalTailChunk000Sub000Block176Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block176Part020CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block176Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block176Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block176Part020CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block176Part020SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block176Part020] using hcert

def TailChunk000Sub000Block176Part021SupportExplicit : Finset ℕ :=
  ([7323] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block176Part021 : ℚ :=
  (244156079 : ℚ) / 464950059417600

def SurrogateDiagonalTailChunk000Sub000Block176Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7323
    = surrogateDiagTailX0RatChunk000Sub000Block176Part021

theorem surrogateDiagonalTailChunk000Sub000Block176Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block176Part021CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block176Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block176Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block176Part021CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block176Part021SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block176Part021] using hcert

def TailChunk000Sub000Block176Part022SupportExplicit : Finset ℕ :=
  ([7327] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block176Part022 : ℚ :=
  (329655163 : ℚ) / 14006209577779200

def SurrogateDiagonalTailChunk000Sub000Block176Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7327
    = surrogateDiagTailX0RatChunk000Sub000Block176Part022

theorem surrogateDiagonalTailChunk000Sub000Block176Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block176Part022CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block176Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block176Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block176Part022CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block176Part022SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block176Part022] using hcert

def TailChunk000Sub000Block176Part023SupportExplicit : Finset ℕ :=
  ([7329] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block176Part023 : ℚ :=
  (27884508775 : ℚ) / 28164695139385344

def SurrogateDiagonalTailChunk000Sub000Block176Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7329
    = surrogateDiagTailX0RatChunk000Sub000Block176Part023

theorem surrogateDiagonalTailChunk000Sub000Block176Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block176Part023CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block176Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block176Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block176Part023CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block176Part023SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block176Part023] using hcert

def TailChunk000Sub000Block176Part024SupportExplicit : Finset ℕ :=
  ([7330] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block176Part024 : ℚ :=
  (704652801625 : ℚ) / 183785459486588928

def SurrogateDiagonalTailChunk000Sub000Block176Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7330
    = surrogateDiagTailX0RatChunk000Sub000Block176Part024

theorem surrogateDiagonalTailChunk000Sub000Block176Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block176Part024CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block176Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block176Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block176Part024CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block176Part024SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block176Part024] using hcert

def surrogateDiagonalTailChunk000Sub000Block176HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block176Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block176Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block176Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block176Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block176Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block176Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block176Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block176Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block176Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block176Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block176Head : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block176Part000
    + surrogateDiagTailX0RatChunk000Sub000Block176Part001
    + surrogateDiagTailX0RatChunk000Sub000Block176Part002
    + surrogateDiagTailX0RatChunk000Sub000Block176Part003
    + surrogateDiagTailX0RatChunk000Sub000Block176Part004
    + surrogateDiagTailX0RatChunk000Sub000Block176Part005
    + surrogateDiagTailX0RatChunk000Sub000Block176Part006
    + surrogateDiagTailX0RatChunk000Sub000Block176Part007
    + surrogateDiagTailX0RatChunk000Sub000Block176Part008
    + surrogateDiagTailX0RatChunk000Sub000Block176Part009

def surrogateDiagonalTailChunk000Sub000Block176MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block176Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block176Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block176Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block176Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block176Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block176Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block176Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block176Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block176Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block176Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block176Mid : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block176Part010
    + surrogateDiagTailX0RatChunk000Sub000Block176Part011
    + surrogateDiagTailX0RatChunk000Sub000Block176Part012
    + surrogateDiagTailX0RatChunk000Sub000Block176Part013
    + surrogateDiagTailX0RatChunk000Sub000Block176Part014
    + surrogateDiagTailX0RatChunk000Sub000Block176Part015
    + surrogateDiagTailX0RatChunk000Sub000Block176Part016
    + surrogateDiagTailX0RatChunk000Sub000Block176Part017
    + surrogateDiagTailX0RatChunk000Sub000Block176Part018
    + surrogateDiagTailX0RatChunk000Sub000Block176Part019

def surrogateDiagonalTailChunk000Sub000Block176TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block176Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block176Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block176Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block176Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block176Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block176Tail : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block176Part020
    + surrogateDiagTailX0RatChunk000Sub000Block176Part021
    + surrogateDiagTailX0RatChunk000Sub000Block176Part022
    + surrogateDiagTailX0RatChunk000Sub000Block176Part023
    + surrogateDiagTailX0RatChunk000Sub000Block176Part024

def surrogateDiagonalTailChunk000Sub000Block176Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub000Block176HeadSum X0
    + surrogateDiagonalTailChunk000Sub000Block176MidSum X0
    + surrogateDiagonalTailChunk000Sub000Block176TailSum X0

def surrogateDiagTailX0RatChunk000Sub000Block176 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block176Part000
    + surrogateDiagTailX0RatChunk000Sub000Block176Part001
    + surrogateDiagTailX0RatChunk000Sub000Block176Part002
    + surrogateDiagTailX0RatChunk000Sub000Block176Part003
    + surrogateDiagTailX0RatChunk000Sub000Block176Part004
    + surrogateDiagTailX0RatChunk000Sub000Block176Part005
    + surrogateDiagTailX0RatChunk000Sub000Block176Part006
    + surrogateDiagTailX0RatChunk000Sub000Block176Part007
    + surrogateDiagTailX0RatChunk000Sub000Block176Part008
    + surrogateDiagTailX0RatChunk000Sub000Block176Part009
    + surrogateDiagTailX0RatChunk000Sub000Block176Part010
    + surrogateDiagTailX0RatChunk000Sub000Block176Part011
    + surrogateDiagTailX0RatChunk000Sub000Block176Part012
    + surrogateDiagTailX0RatChunk000Sub000Block176Part013
    + surrogateDiagTailX0RatChunk000Sub000Block176Part014
    + surrogateDiagTailX0RatChunk000Sub000Block176Part015
    + surrogateDiagTailX0RatChunk000Sub000Block176Part016
    + surrogateDiagTailX0RatChunk000Sub000Block176Part017
    + surrogateDiagTailX0RatChunk000Sub000Block176Part018
    + surrogateDiagTailX0RatChunk000Sub000Block176Part019
    + surrogateDiagTailX0RatChunk000Sub000Block176Part020
    + surrogateDiagTailX0RatChunk000Sub000Block176Part021
    + surrogateDiagTailX0RatChunk000Sub000Block176Part022
    + surrogateDiagTailX0RatChunk000Sub000Block176Part023
    + surrogateDiagTailX0RatChunk000Sub000Block176Part024

theorem surrogateDiagTailX0RatChunk000Sub000Block176_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk000Sub000Block176Head + surrogateDiagTailX0RatChunk000Sub000Block176Mid + surrogateDiagTailX0RatChunk000Sub000Block176Tail =
      surrogateDiagTailX0RatChunk000Sub000Block176 := by
  unfold surrogateDiagTailX0RatChunk000Sub000Block176Head surrogateDiagTailX0RatChunk000Sub000Block176Mid surrogateDiagTailX0RatChunk000Sub000Block176Tail surrogateDiagTailX0RatChunk000Sub000Block176
  ring

def SurrogateDiagonalTailChunk000Sub000Block176HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block176HeadSum X0 = surrogateDiagTailX0RatChunk000Sub000Block176Head

def SurrogateDiagonalTailChunk000Sub000Block176MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block176MidSum X0 = surrogateDiagTailX0RatChunk000Sub000Block176Mid

def SurrogateDiagonalTailChunk000Sub000Block176TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block176TailSum X0 = surrogateDiagTailX0RatChunk000Sub000Block176Tail

theorem surrogateDiagonalTailChunk000Sub000Block176_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk000Sub000Block176HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk000Sub000Block176MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk000Sub000Block176TailCertificateAt X0) :
    surrogateDiagonalTailChunk000Sub000Block176Sum X0 = surrogateDiagTailX0RatChunk000Sub000Block176 := by
  unfold SurrogateDiagonalTailChunk000Sub000Block176HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk000Sub000Block176MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk000Sub000Block176TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk000Sub000Block176Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk000Sub000Block176_eq_head_add_mid_add_tail

/-- Block 177 covers tail-support indices [4425,4450) and q from 7331 to 7369. -/

def TailChunk000Sub000Block177Part000SupportExplicit : Finset ℕ :=
  ([7331] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block177Part000 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub000Block177Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7331
    = surrogateDiagTailX0RatChunk000Sub000Block177Part000

theorem surrogateDiagonalTailChunk000Sub000Block177Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block177Part000CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block177Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block177Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block177Part000CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block177Part000SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block177Part000] using hcert

def TailChunk000Sub000Block177Part001SupportExplicit : Finset ℕ :=
  ([7333] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block177Part001 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub000Block177Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7333
    = surrogateDiagTailX0RatChunk000Sub000Block177Part001

theorem surrogateDiagonalTailChunk000Sub000Block177Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block177Part001CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block177Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block177Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block177Part001CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block177Part001SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block177Part001] using hcert

def TailChunk000Sub000Block177Part002SupportExplicit : Finset ℕ :=
  ([7334] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block177Part002 : ℚ :=
  (117163675 : ℚ) / 51608123080704

def SurrogateDiagonalTailChunk000Sub000Block177Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7334
    = surrogateDiagTailX0RatChunk000Sub000Block177Part002

theorem surrogateDiagonalTailChunk000Sub000Block177Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block177Part002CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block177Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block177Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block177Part002CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block177Part002SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block177Part002] using hcert

def TailChunk000Sub000Block177Part003SupportExplicit : Finset ℕ :=
  ([7337] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block177Part003 : ℚ :=
  (1147223307 : ℚ) / 12001304442265600

def SurrogateDiagonalTailChunk000Sub000Block177Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7337
    = surrogateDiagTailX0RatChunk000Sub000Block177Part003

theorem surrogateDiagonalTailChunk000Sub000Block177Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block177Part003CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block177Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block177Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block177Part003CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block177Part003SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block177Part003] using hcert

def TailChunk000Sub000Block177Part004SupportExplicit : Finset ℕ :=
  ([7338] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block177Part004 : ℚ :=
  (654048528175 : ℚ) / 89213723363077248

def SurrogateDiagonalTailChunk000Sub000Block177Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7338
    = surrogateDiagTailX0RatChunk000Sub000Block177Part004

theorem surrogateDiagonalTailChunk000Sub000Block177Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block177Part004CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block177Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block177Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block177Part004CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block177Part004SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block177Part004] using hcert

def TailChunk000Sub000Block177Part005SupportExplicit : Finset ℕ :=
  ([7339] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block177Part005 : ℚ :=
  (901995339 : ℚ) / 85681205859942400

def SurrogateDiagonalTailChunk000Sub000Block177Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7339
    = surrogateDiagTailX0RatChunk000Sub000Block177Part005

theorem surrogateDiagonalTailChunk000Sub000Block177Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block177Part005CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block177Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block177Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block177Part005CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block177Part005SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block177Part005] using hcert

def TailChunk000Sub000Block177Part006SupportExplicit : Finset ℕ :=
  ([7341] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block177Part006 : ℚ :=
  (374169903725 : ℚ) / 716048858396572224

def SurrogateDiagonalTailChunk000Sub000Block177Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7341
    = surrogateDiagTailX0RatChunk000Sub000Block177Part006

theorem surrogateDiagonalTailChunk000Sub000Block177Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block177Part006CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block177Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block177Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block177Part006CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block177Part006SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block177Part006] using hcert

def TailChunk000Sub000Block177Part007SupportExplicit : Finset ℕ :=
  ([7342] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block177Part007 : ℚ :=
  (336906025 : ℚ) / 181447549463442

def SurrogateDiagonalTailChunk000Sub000Block177Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7342
    = surrogateDiagTailX0RatChunk000Sub000Block177Part007

theorem surrogateDiagonalTailChunk000Sub000Block177Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block177Part007CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block177Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block177Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block177Part007CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block177Part007SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block177Part007] using hcert

def TailChunk000Sub000Block177Part008SupportExplicit : Finset ℕ :=
  ([7343] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block177Part008 : ℚ :=
  (344819661775 : ℚ) / 3909101895634157568

def SurrogateDiagonalTailChunk000Sub000Block177Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7343
    = surrogateDiagTailX0RatChunk000Sub000Block177Part008

theorem surrogateDiagonalTailChunk000Sub000Block177Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block177Part008CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block177Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block177Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block177Part008CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block177Part008SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block177Part008] using hcert

def TailChunk000Sub000Block177Part009SupportExplicit : Finset ℕ :=
  ([7345] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block177Part009 : ℚ :=
  (492288843925 : ℚ) / 2088641481500786688

def SurrogateDiagonalTailChunk000Sub000Block177Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7345
    = surrogateDiagTailX0RatChunk000Sub000Block177Part009

theorem surrogateDiagonalTailChunk000Sub000Block177Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block177Part009CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block177Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block177Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block177Part009CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block177Part009SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block177Part009] using hcert

def TailChunk000Sub000Block177Part010SupportExplicit : Finset ℕ :=
  ([7346] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block177Part010 : ℚ :=
  (210795765625 : ℚ) / 113652124307845632

def SurrogateDiagonalTailChunk000Sub000Block177Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7346
    = surrogateDiagTailX0RatChunk000Sub000Block177Part010

theorem surrogateDiagonalTailChunk000Sub000Block177Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block177Part010CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block177Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block177Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block177Part010CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block177Part010SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block177Part010] using hcert

def TailChunk000Sub000Block177Part011SupportExplicit : Finset ℕ :=
  ([7347] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block177Part011 : ℚ :=
  (222252089 : ℚ) / 355415606507520

def SurrogateDiagonalTailChunk000Sub000Block177Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7347
    = surrogateDiagTailX0RatChunk000Sub000Block177Part011

theorem surrogateDiagonalTailChunk000Sub000Block177Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block177Part011CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block177Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block177Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block177Part011CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block177Part011SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block177Part011] using hcert

def TailChunk000Sub000Block177Part012SupportExplicit : Finset ℕ :=
  ([7349] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block177Part012 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub000Block177Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7349
    = surrogateDiagTailX0RatChunk000Sub000Block177Part012

theorem surrogateDiagonalTailChunk000Sub000Block177Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block177Part012CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block177Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block177Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block177Part012CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block177Part012SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block177Part012] using hcert

def TailChunk000Sub000Block177Part013SupportExplicit : Finset ℕ :=
  ([7351] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block177Part013 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub000Block177Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7351
    = surrogateDiagTailX0RatChunk000Sub000Block177Part013

theorem surrogateDiagonalTailChunk000Sub000Block177Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block177Part013CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block177Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block177Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block177Part013CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block177Part013SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block177Part013] using hcert

def TailChunk000Sub000Block177Part014SupportExplicit : Finset ℕ :=
  ([7354] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block177Part014 : ℚ :=
  (1689703116775 : ℚ) / 456592601201628288

def SurrogateDiagonalTailChunk000Sub000Block177Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7354
    = surrogateDiagTailX0RatChunk000Sub000Block177Part014

theorem surrogateDiagonalTailChunk000Sub000Block177Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block177Part014CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block177Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block177Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block177Part014CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block177Part014SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block177Part014] using hcert

def TailChunk000Sub000Block177Part015SupportExplicit : Finset ℕ :=
  ([7355] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block177Part015 : ℚ :=
  (8559350417 : ℚ) / 9963568443225600

def SurrogateDiagonalTailChunk000Sub000Block177Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7355
    = surrogateDiagTailX0RatChunk000Sub000Block177Part015

theorem surrogateDiagonalTailChunk000Sub000Block177Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block177Part015CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block177Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block177Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block177Part015CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block177Part015SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block177Part015] using hcert

def TailChunk000Sub000Block177Part016SupportExplicit : Finset ℕ :=
  ([7357] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block177Part016 : ℚ :=
  (110344726963 : ℚ) / 157561115922000000

def SurrogateDiagonalTailChunk000Sub000Block177Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7357
    = surrogateDiagTailX0RatChunk000Sub000Block177Part016

theorem surrogateDiagonalTailChunk000Sub000Block177Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block177Part016CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block177Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block177Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block177Part016CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block177Part016SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block177Part016] using hcert

def TailChunk000Sub000Block177Part017SupportExplicit : Finset ℕ :=
  ([7358] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block177Part017 : ℚ :=
  (378732398275 : ℚ) / 81976294805524992

def SurrogateDiagonalTailChunk000Sub000Block177Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7358
    = surrogateDiagTailX0RatChunk000Sub000Block177Part017

theorem surrogateDiagonalTailChunk000Sub000Block177Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block177Part017CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block177Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block177Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block177Part017CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block177Part017SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block177Part017] using hcert

def TailChunk000Sub000Block177Part018SupportExplicit : Finset ℕ :=
  ([7359] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block177Part018 : ℚ :=
  (6654586861 : ℚ) / 3887037501649920

def SurrogateDiagonalTailChunk000Sub000Block177Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7359
    = surrogateDiagTailX0RatChunk000Sub000Block177Part018

theorem surrogateDiagonalTailChunk000Sub000Block177Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block177Part018CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block177Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block177Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block177Part018CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block177Part018SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block177Part018] using hcert

def TailChunk000Sub000Block177Part019SupportExplicit : Finset ℕ :=
  ([7361] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block177Part019 : ℚ :=
  (779958650275 : ℚ) / 1426861386935304192

def SurrogateDiagonalTailChunk000Sub000Block177Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7361
    = surrogateDiagTailX0RatChunk000Sub000Block177Part019

theorem surrogateDiagonalTailChunk000Sub000Block177Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block177Part019CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block177Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block177Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block177Part019CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block177Part019SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block177Part019] using hcert

def TailChunk000Sub000Block177Part020SupportExplicit : Finset ℕ :=
  ([7363] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block177Part020 : ℚ :=
  (120224595625 : ℚ) / 239074831765592064

def SurrogateDiagonalTailChunk000Sub000Block177Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7363
    = surrogateDiagTailX0RatChunk000Sub000Block177Part020

theorem surrogateDiagonalTailChunk000Sub000Block177Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block177Part020CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block177Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block177Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block177Part020CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block177Part020SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block177Part020] using hcert

def TailChunk000Sub000Block177Part021SupportExplicit : Finset ℕ :=
  ([7365] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block177Part021 : ℚ :=
  (28265102843 : ℚ) / 11808673710489600

def SurrogateDiagonalTailChunk000Sub000Block177Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7365
    = surrogateDiagTailX0RatChunk000Sub000Block177Part021

theorem surrogateDiagonalTailChunk000Sub000Block177Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block177Part021CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block177Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block177Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block177Part021CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block177Part021SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block177Part021] using hcert

def TailChunk000Sub000Block177Part022SupportExplicit : Finset ℕ :=
  ([7366] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block177Part022 : ℚ :=
  (400359354925 : ℚ) / 96845885268152832

def SurrogateDiagonalTailChunk000Sub000Block177Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7366
    = surrogateDiagTailX0RatChunk000Sub000Block177Part022

theorem surrogateDiagonalTailChunk000Sub000Block177Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block177Part022CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block177Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block177Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block177Part022CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block177Part022SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block177Part022] using hcert

def TailChunk000Sub000Block177Part023SupportExplicit : Finset ℕ :=
  ([7367] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block177Part023 : ℚ :=
  (3276872641525 : ℚ) / 6630657249378060288

def SurrogateDiagonalTailChunk000Sub000Block177Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7367
    = surrogateDiagTailX0RatChunk000Sub000Block177Part023

theorem surrogateDiagonalTailChunk000Sub000Block177Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block177Part023CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block177Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block177Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block177Part023CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block177Part023SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block177Part023] using hcert

def TailChunk000Sub000Block177Part024SupportExplicit : Finset ℕ :=
  ([7369] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block177Part024 : ℚ :=
  (848471265625 : ℚ) / 1842321143397929472

def SurrogateDiagonalTailChunk000Sub000Block177Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7369
    = surrogateDiagTailX0RatChunk000Sub000Block177Part024

theorem surrogateDiagonalTailChunk000Sub000Block177Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block177Part024CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block177Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block177Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block177Part024CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block177Part024SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block177Part024] using hcert

def surrogateDiagonalTailChunk000Sub000Block177HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block177Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block177Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block177Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block177Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block177Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block177Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block177Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block177Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block177Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block177Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block177Head : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block177Part000
    + surrogateDiagTailX0RatChunk000Sub000Block177Part001
    + surrogateDiagTailX0RatChunk000Sub000Block177Part002
    + surrogateDiagTailX0RatChunk000Sub000Block177Part003
    + surrogateDiagTailX0RatChunk000Sub000Block177Part004
    + surrogateDiagTailX0RatChunk000Sub000Block177Part005
    + surrogateDiagTailX0RatChunk000Sub000Block177Part006
    + surrogateDiagTailX0RatChunk000Sub000Block177Part007
    + surrogateDiagTailX0RatChunk000Sub000Block177Part008
    + surrogateDiagTailX0RatChunk000Sub000Block177Part009

def surrogateDiagonalTailChunk000Sub000Block177MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block177Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block177Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block177Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block177Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block177Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block177Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block177Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block177Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block177Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block177Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block177Mid : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block177Part010
    + surrogateDiagTailX0RatChunk000Sub000Block177Part011
    + surrogateDiagTailX0RatChunk000Sub000Block177Part012
    + surrogateDiagTailX0RatChunk000Sub000Block177Part013
    + surrogateDiagTailX0RatChunk000Sub000Block177Part014
    + surrogateDiagTailX0RatChunk000Sub000Block177Part015
    + surrogateDiagTailX0RatChunk000Sub000Block177Part016
    + surrogateDiagTailX0RatChunk000Sub000Block177Part017
    + surrogateDiagTailX0RatChunk000Sub000Block177Part018
    + surrogateDiagTailX0RatChunk000Sub000Block177Part019

def surrogateDiagonalTailChunk000Sub000Block177TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block177Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block177Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block177Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block177Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block177Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block177Tail : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block177Part020
    + surrogateDiagTailX0RatChunk000Sub000Block177Part021
    + surrogateDiagTailX0RatChunk000Sub000Block177Part022
    + surrogateDiagTailX0RatChunk000Sub000Block177Part023
    + surrogateDiagTailX0RatChunk000Sub000Block177Part024

def surrogateDiagonalTailChunk000Sub000Block177Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub000Block177HeadSum X0
    + surrogateDiagonalTailChunk000Sub000Block177MidSum X0
    + surrogateDiagonalTailChunk000Sub000Block177TailSum X0

def surrogateDiagTailX0RatChunk000Sub000Block177 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block177Part000
    + surrogateDiagTailX0RatChunk000Sub000Block177Part001
    + surrogateDiagTailX0RatChunk000Sub000Block177Part002
    + surrogateDiagTailX0RatChunk000Sub000Block177Part003
    + surrogateDiagTailX0RatChunk000Sub000Block177Part004
    + surrogateDiagTailX0RatChunk000Sub000Block177Part005
    + surrogateDiagTailX0RatChunk000Sub000Block177Part006
    + surrogateDiagTailX0RatChunk000Sub000Block177Part007
    + surrogateDiagTailX0RatChunk000Sub000Block177Part008
    + surrogateDiagTailX0RatChunk000Sub000Block177Part009
    + surrogateDiagTailX0RatChunk000Sub000Block177Part010
    + surrogateDiagTailX0RatChunk000Sub000Block177Part011
    + surrogateDiagTailX0RatChunk000Sub000Block177Part012
    + surrogateDiagTailX0RatChunk000Sub000Block177Part013
    + surrogateDiagTailX0RatChunk000Sub000Block177Part014
    + surrogateDiagTailX0RatChunk000Sub000Block177Part015
    + surrogateDiagTailX0RatChunk000Sub000Block177Part016
    + surrogateDiagTailX0RatChunk000Sub000Block177Part017
    + surrogateDiagTailX0RatChunk000Sub000Block177Part018
    + surrogateDiagTailX0RatChunk000Sub000Block177Part019
    + surrogateDiagTailX0RatChunk000Sub000Block177Part020
    + surrogateDiagTailX0RatChunk000Sub000Block177Part021
    + surrogateDiagTailX0RatChunk000Sub000Block177Part022
    + surrogateDiagTailX0RatChunk000Sub000Block177Part023
    + surrogateDiagTailX0RatChunk000Sub000Block177Part024

theorem surrogateDiagTailX0RatChunk000Sub000Block177_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk000Sub000Block177Head + surrogateDiagTailX0RatChunk000Sub000Block177Mid + surrogateDiagTailX0RatChunk000Sub000Block177Tail =
      surrogateDiagTailX0RatChunk000Sub000Block177 := by
  unfold surrogateDiagTailX0RatChunk000Sub000Block177Head surrogateDiagTailX0RatChunk000Sub000Block177Mid surrogateDiagTailX0RatChunk000Sub000Block177Tail surrogateDiagTailX0RatChunk000Sub000Block177
  ring

def SurrogateDiagonalTailChunk000Sub000Block177HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block177HeadSum X0 = surrogateDiagTailX0RatChunk000Sub000Block177Head

def SurrogateDiagonalTailChunk000Sub000Block177MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block177MidSum X0 = surrogateDiagTailX0RatChunk000Sub000Block177Mid

def SurrogateDiagonalTailChunk000Sub000Block177TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block177TailSum X0 = surrogateDiagTailX0RatChunk000Sub000Block177Tail

theorem surrogateDiagonalTailChunk000Sub000Block177_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk000Sub000Block177HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk000Sub000Block177MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk000Sub000Block177TailCertificateAt X0) :
    surrogateDiagonalTailChunk000Sub000Block177Sum X0 = surrogateDiagTailX0RatChunk000Sub000Block177 := by
  unfold SurrogateDiagonalTailChunk000Sub000Block177HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk000Sub000Block177MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk000Sub000Block177TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk000Sub000Block177Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk000Sub000Block177_eq_head_add_mid_add_tail

/-- Block 178 covers tail-support indices [4450,4475) and q from 7370 to 7413. -/

def TailChunk000Sub000Block178Part000SupportExplicit : Finset ℕ :=
  ([7370] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block178Part000 : ℚ :=
  (21826964459 : ℚ) / 2429251961241600

def SurrogateDiagonalTailChunk000Sub000Block178Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7370
    = surrogateDiagTailX0RatChunk000Sub000Block178Part000

theorem surrogateDiagonalTailChunk000Sub000Block178Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block178Part000CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block178Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block178Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block178Part000CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block178Part000SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block178Part000] using hcert

def TailChunk000Sub000Block178Part001SupportExplicit : Finset ℕ :=
  ([7373] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block178Part001 : ℚ :=
  (65864543153 : ℚ) / 134396153856000000

def SurrogateDiagonalTailChunk000Sub000Block178Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7373
    = surrogateDiagTailX0RatChunk000Sub000Block178Part001

theorem surrogateDiagonalTailChunk000Sub000Block178Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block178Part001CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block178Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block178Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block178Part001CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block178Part001SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block178Part001] using hcert

def TailChunk000Sub000Block178Part002SupportExplicit : Finset ℕ :=
  ([7374] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block178Part002 : ℚ :=
  (660480880525 : ℚ) / 90978821896194048

def SurrogateDiagonalTailChunk000Sub000Block178Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7374
    = surrogateDiagTailX0RatChunk000Sub000Block178Part002

theorem surrogateDiagonalTailChunk000Sub000Block178Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block178Part002CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block178Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block178Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block178Part002CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block178Part002SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block178Part002] using hcert

def TailChunk000Sub000Block178Part003SupportExplicit : Finset ℕ :=
  ([7377] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block178Part003 : ℚ :=
  (236122276775 : ℚ) / 182551064070711696

def SurrogateDiagonalTailChunk000Sub000Block178Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7377
    = surrogateDiagTailX0RatChunk000Sub000Block178Part003

theorem surrogateDiagonalTailChunk000Sub000Block178Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block178Part003CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block178Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block178Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block178Part003CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block178Part003SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block178Part003] using hcert

def TailChunk000Sub000Block178Part004SupportExplicit : Finset ℕ :=
  ([7378] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block178Part004 : ℚ :=
  (360064847 : ℚ) / 84951642931200

def SurrogateDiagonalTailChunk000Sub000Block178Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7378
    = surrogateDiagTailX0RatChunk000Sub000Block178Part004

theorem surrogateDiagonalTailChunk000Sub000Block178Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block178Part004CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block178Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block178Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block178Part004CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block178Part004SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block178Part004] using hcert

def TailChunk000Sub000Block178Part005SupportExplicit : Finset ℕ :=
  ([7379] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block178Part005 : ℚ :=
  (410045344625 : ℚ) / 828832156172257536

def SurrogateDiagonalTailChunk000Sub000Block178Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7379
    = surrogateDiagTailX0RatChunk000Sub000Block178Part005

theorem surrogateDiagonalTailChunk000Sub000Block178Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block178Part005CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block178Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block178Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block178Part005CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block178Part005SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block178Part005] using hcert

def TailChunk000Sub000Block178Part006SupportExplicit : Finset ℕ :=
  ([7382] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block178Part006 : ℚ :=
  (340587025 : ℚ) / 185435258845842

def SurrogateDiagonalTailChunk000Sub000Block178Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7382
    = surrogateDiagTailX0RatChunk000Sub000Block178Part006

theorem surrogateDiagonalTailChunk000Sub000Block178Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block178Part006CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block178Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block178Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block178Part006CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block178Part006SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block178Part006] using hcert

def TailChunk000Sub000Block178Part007SupportExplicit : Finset ℕ :=
  ([7383] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block178Part007 : ℚ :=
  (1776471548275 : ℚ) / 1183207805209233408

def SurrogateDiagonalTailChunk000Sub000Block178Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7383
    = surrogateDiagTailX0RatChunk000Sub000Block178Part007

theorem surrogateDiagonalTailChunk000Sub000Block178Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block178Part007CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block178Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block178Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block178Part007CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block178Part007SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block178Part007] using hcert

def TailChunk000Sub000Block178Part008SupportExplicit : Finset ℕ :=
  ([7385] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block178Part008 : ℚ :=
  (40341505163 : ℚ) / 32268516540825600

def SurrogateDiagonalTailChunk000Sub000Block178Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7385
    = surrogateDiagTailX0RatChunk000Sub000Block178Part008

theorem surrogateDiagonalTailChunk000Sub000Block178Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block178Part008CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block178Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block178Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block178Part008CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block178Part008SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block178Part008] using hcert

def TailChunk000Sub000Block178Part009SupportExplicit : Finset ℕ :=
  ([7386] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block178Part009 : ℚ :=
  (26505279967 : ℚ) / 3662918693251200

def SurrogateDiagonalTailChunk000Sub000Block178Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7386
    = surrogateDiagTailX0RatChunk000Sub000Block178Part009

theorem surrogateDiagonalTailChunk000Sub000Block178Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block178Part009CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block178Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block178Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block178Part009CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block178Part009SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block178Part009] using hcert

def TailChunk000Sub000Block178Part010SupportExplicit : Finset ℕ :=
  ([7387] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block178Part010 : ℚ :=
  (826803308425 : ℚ) / 1694934679320993792

def SurrogateDiagonalTailChunk000Sub000Block178Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7387
    = surrogateDiagTailX0RatChunk000Sub000Block178Part010

theorem surrogateDiagonalTailChunk000Sub000Block178Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block178Part010CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block178Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block178Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block178Part010CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block178Part010SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block178Part010] using hcert

def TailChunk000Sub000Block178Part011SupportExplicit : Finset ℕ :=
  ([7390] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block178Part011 : ℚ :=
  (250085899325 : ℚ) / 63295235019380736

def SurrogateDiagonalTailChunk000Sub000Block178Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7390
    = surrogateDiagTailX0RatChunk000Sub000Block178Part011

theorem surrogateDiagonalTailChunk000Sub000Block178Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block178Part011CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block178Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block178Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block178Part011CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block178Part011SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block178Part011] using hcert

def TailChunk000Sub000Block178Part012SupportExplicit : Finset ℕ :=
  ([7391] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block178Part012 : ℚ :=
  (3167589951925 : ℚ) / 5948997435018528768

def SurrogateDiagonalTailChunk000Sub000Block178Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7391
    = surrogateDiagTailX0RatChunk000Sub000Block178Part012

theorem surrogateDiagonalTailChunk000Sub000Block178Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block178Part012CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block178Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block178Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block178Part012CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block178Part012SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block178Part012] using hcert

def TailChunk000Sub000Block178Part013SupportExplicit : Finset ℕ :=
  ([7393] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block178Part013 : ℚ :=
  (854007015625 : ℚ) / 1866442866861146112

def SurrogateDiagonalTailChunk000Sub000Block178Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7393
    = surrogateDiagTailX0RatChunk000Sub000Block178Part013

theorem surrogateDiagonalTailChunk000Sub000Block178Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block178Part013CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block178Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block178Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block178Part013CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block178Part013SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block178Part013] using hcert

def TailChunk000Sub000Block178Part014SupportExplicit : Finset ℕ :=
  ([7394] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block178Part014 : ℚ :=
  (213559515625 : ℚ) / 116652679178821632

def SurrogateDiagonalTailChunk000Sub000Block178Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7394
    = surrogateDiagTailX0RatChunk000Sub000Block178Part014

theorem surrogateDiagonalTailChunk000Sub000Block178Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block178Part014CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block178Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block178Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block178Part014CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block178Part014SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block178Part014] using hcert

def TailChunk000Sub000Block178Part015SupportExplicit : Finset ℕ :=
  ([7395] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block178Part015 : ℚ :=
  (426488123625 : ℚ) / 137523718946553856

def SurrogateDiagonalTailChunk000Sub000Block178Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7395
    = surrogateDiagTailX0RatChunk000Sub000Block178Part015

theorem surrogateDiagonalTailChunk000Sub000Block178Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block178Part015CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block178Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block178Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block178Part015CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block178Part015SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block178Part015] using hcert

def TailChunk000Sub000Block178Part016SupportExplicit : Finset ℕ :=
  ([7397] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block178Part016 : ℚ :=
  (5994572675 : ℚ) / 10540840090788864

def SurrogateDiagonalTailChunk000Sub000Block178Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7397
    = surrogateDiagTailX0RatChunk000Sub000Block178Part016

theorem surrogateDiagonalTailChunk000Sub000Block178Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block178Part016CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block178Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block178Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block178Part016CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block178Part016SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block178Part016] using hcert

def TailChunk000Sub000Block178Part017SupportExplicit : Finset ℕ :=
  ([7401] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block178Part017 : ℚ :=
  (118830636475 : ℚ) / 92469635969988168

def SurrogateDiagonalTailChunk000Sub000Block178Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7401
    = surrogateDiagTailX0RatChunk000Sub000Block178Part017

theorem surrogateDiagonalTailChunk000Sub000Block178Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block178Part017CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block178Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block178Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block178Part017CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block178Part017SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block178Part017] using hcert

def TailChunk000Sub000Block178Part018SupportExplicit : Finset ℕ :=
  ([7402] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block178Part018 : ℚ :=
  (13697401 : ℚ) / 7498143328800

def SurrogateDiagonalTailChunk000Sub000Block178Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7402
    = surrogateDiagTailX0RatChunk000Sub000Block178Part018

theorem surrogateDiagonalTailChunk000Sub000Block178Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block178Part018CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block178Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block178Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block178Part018CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block178Part018SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block178Part018] using hcert

def TailChunk000Sub000Block178Part019SupportExplicit : Finset ℕ :=
  ([7403] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block178Part019 : ℚ :=
  (120945722101 : ℚ) / 203968894677811200

def SurrogateDiagonalTailChunk000Sub000Block178Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7403
    = surrogateDiagTailX0RatChunk000Sub000Block178Part019

theorem surrogateDiagonalTailChunk000Sub000Block178Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block178Part019CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block178Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block178Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block178Part019CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block178Part019SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block178Part019] using hcert

def TailChunk000Sub000Block178Part020SupportExplicit : Finset ℕ :=
  ([7405] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block178Part020 : ℚ :=
  (32877781239 : ℚ) / 40949860099686400

def SurrogateDiagonalTailChunk000Sub000Block178Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7405
    = surrogateDiagTailX0RatChunk000Sub000Block178Part020

theorem surrogateDiagonalTailChunk000Sub000Block178Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block178Part020CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block178Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block178Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block178Part020CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block178Part020SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block178Part020] using hcert

def TailChunk000Sub000Block178Part021SupportExplicit : Finset ℕ :=
  ([7409] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block178Part021 : ℚ :=
  (32633565667 : ℚ) / 64985985002080800

def SurrogateDiagonalTailChunk000Sub000Block178Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7409
    = surrogateDiagTailX0RatChunk000Sub000Block178Part021

theorem surrogateDiagonalTailChunk000Sub000Block178Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block178Part021CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block178Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block178Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block178Part021CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block178Part021SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block178Part021] using hcert

def TailChunk000Sub000Block178Part022SupportExplicit : Finset ℕ :=
  ([7410] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block178Part022 : ℚ :=
  (311505088925 : ℚ) / 11147354585432064

def SurrogateDiagonalTailChunk000Sub000Block178Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7410
    = surrogateDiagTailX0RatChunk000Sub000Block178Part022

theorem surrogateDiagonalTailChunk000Sub000Block178Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block178Part022CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block178Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block178Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block178Part022CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block178Part022SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block178Part022] using hcert

def TailChunk000Sub000Block178Part023SupportExplicit : Finset ℕ :=
  ([7411] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block178Part023 : ℚ :=
  (1373073025 : ℚ) / 3015502425499122

def SurrogateDiagonalTailChunk000Sub000Block178Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7411
    = surrogateDiagTailX0RatChunk000Sub000Block178Part023

theorem surrogateDiagonalTailChunk000Sub000Block178Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block178Part023CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block178Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block178Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block178Part023CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block178Part023SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block178Part023] using hcert

def TailChunk000Sub000Block178Part024SupportExplicit : Finset ℕ :=
  ([7413] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block178Part024 : ℚ :=
  (86692566775 : ℚ) / 44223182369980416

def SurrogateDiagonalTailChunk000Sub000Block178Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7413
    = surrogateDiagTailX0RatChunk000Sub000Block178Part024

theorem surrogateDiagonalTailChunk000Sub000Block178Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block178Part024CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block178Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block178Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block178Part024CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block178Part024SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block178Part024] using hcert

def surrogateDiagonalTailChunk000Sub000Block178HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block178Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block178Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block178Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block178Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block178Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block178Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block178Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block178Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block178Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block178Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block178Head : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block178Part000
    + surrogateDiagTailX0RatChunk000Sub000Block178Part001
    + surrogateDiagTailX0RatChunk000Sub000Block178Part002
    + surrogateDiagTailX0RatChunk000Sub000Block178Part003
    + surrogateDiagTailX0RatChunk000Sub000Block178Part004
    + surrogateDiagTailX0RatChunk000Sub000Block178Part005
    + surrogateDiagTailX0RatChunk000Sub000Block178Part006
    + surrogateDiagTailX0RatChunk000Sub000Block178Part007
    + surrogateDiagTailX0RatChunk000Sub000Block178Part008
    + surrogateDiagTailX0RatChunk000Sub000Block178Part009

def surrogateDiagonalTailChunk000Sub000Block178MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block178Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block178Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block178Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block178Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block178Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block178Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block178Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block178Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block178Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block178Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block178Mid : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block178Part010
    + surrogateDiagTailX0RatChunk000Sub000Block178Part011
    + surrogateDiagTailX0RatChunk000Sub000Block178Part012
    + surrogateDiagTailX0RatChunk000Sub000Block178Part013
    + surrogateDiagTailX0RatChunk000Sub000Block178Part014
    + surrogateDiagTailX0RatChunk000Sub000Block178Part015
    + surrogateDiagTailX0RatChunk000Sub000Block178Part016
    + surrogateDiagTailX0RatChunk000Sub000Block178Part017
    + surrogateDiagTailX0RatChunk000Sub000Block178Part018
    + surrogateDiagTailX0RatChunk000Sub000Block178Part019

def surrogateDiagonalTailChunk000Sub000Block178TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block178Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block178Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block178Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block178Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block178Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block178Tail : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block178Part020
    + surrogateDiagTailX0RatChunk000Sub000Block178Part021
    + surrogateDiagTailX0RatChunk000Sub000Block178Part022
    + surrogateDiagTailX0RatChunk000Sub000Block178Part023
    + surrogateDiagTailX0RatChunk000Sub000Block178Part024

def surrogateDiagonalTailChunk000Sub000Block178Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub000Block178HeadSum X0
    + surrogateDiagonalTailChunk000Sub000Block178MidSum X0
    + surrogateDiagonalTailChunk000Sub000Block178TailSum X0

def surrogateDiagTailX0RatChunk000Sub000Block178 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block178Part000
    + surrogateDiagTailX0RatChunk000Sub000Block178Part001
    + surrogateDiagTailX0RatChunk000Sub000Block178Part002
    + surrogateDiagTailX0RatChunk000Sub000Block178Part003
    + surrogateDiagTailX0RatChunk000Sub000Block178Part004
    + surrogateDiagTailX0RatChunk000Sub000Block178Part005
    + surrogateDiagTailX0RatChunk000Sub000Block178Part006
    + surrogateDiagTailX0RatChunk000Sub000Block178Part007
    + surrogateDiagTailX0RatChunk000Sub000Block178Part008
    + surrogateDiagTailX0RatChunk000Sub000Block178Part009
    + surrogateDiagTailX0RatChunk000Sub000Block178Part010
    + surrogateDiagTailX0RatChunk000Sub000Block178Part011
    + surrogateDiagTailX0RatChunk000Sub000Block178Part012
    + surrogateDiagTailX0RatChunk000Sub000Block178Part013
    + surrogateDiagTailX0RatChunk000Sub000Block178Part014
    + surrogateDiagTailX0RatChunk000Sub000Block178Part015
    + surrogateDiagTailX0RatChunk000Sub000Block178Part016
    + surrogateDiagTailX0RatChunk000Sub000Block178Part017
    + surrogateDiagTailX0RatChunk000Sub000Block178Part018
    + surrogateDiagTailX0RatChunk000Sub000Block178Part019
    + surrogateDiagTailX0RatChunk000Sub000Block178Part020
    + surrogateDiagTailX0RatChunk000Sub000Block178Part021
    + surrogateDiagTailX0RatChunk000Sub000Block178Part022
    + surrogateDiagTailX0RatChunk000Sub000Block178Part023
    + surrogateDiagTailX0RatChunk000Sub000Block178Part024

theorem surrogateDiagTailX0RatChunk000Sub000Block178_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk000Sub000Block178Head + surrogateDiagTailX0RatChunk000Sub000Block178Mid + surrogateDiagTailX0RatChunk000Sub000Block178Tail =
      surrogateDiagTailX0RatChunk000Sub000Block178 := by
  unfold surrogateDiagTailX0RatChunk000Sub000Block178Head surrogateDiagTailX0RatChunk000Sub000Block178Mid surrogateDiagTailX0RatChunk000Sub000Block178Tail surrogateDiagTailX0RatChunk000Sub000Block178
  ring

def SurrogateDiagonalTailChunk000Sub000Block178HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block178HeadSum X0 = surrogateDiagTailX0RatChunk000Sub000Block178Head

def SurrogateDiagonalTailChunk000Sub000Block178MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block178MidSum X0 = surrogateDiagTailX0RatChunk000Sub000Block178Mid

def SurrogateDiagonalTailChunk000Sub000Block178TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block178TailSum X0 = surrogateDiagTailX0RatChunk000Sub000Block178Tail

theorem surrogateDiagonalTailChunk000Sub000Block178_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk000Sub000Block178HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk000Sub000Block178MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk000Sub000Block178TailCertificateAt X0) :
    surrogateDiagonalTailChunk000Sub000Block178Sum X0 = surrogateDiagTailX0RatChunk000Sub000Block178 := by
  unfold SurrogateDiagonalTailChunk000Sub000Block178HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk000Sub000Block178MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk000Sub000Block178TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk000Sub000Block178Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk000Sub000Block178_eq_head_add_mid_add_tail

/-- Block 179 covers tail-support indices [4475,4500) and q from 7414 to 7453. -/

def TailChunk000Sub000Block179Part000SupportExplicit : Finset ℕ :=
  ([7414] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block179Part000 : ℚ :=
  (1673638273 : ℚ) / 354112664371200

def SurrogateDiagonalTailChunk000Sub000Block179Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7414
    = surrogateDiagTailX0RatChunk000Sub000Block179Part000

theorem surrogateDiagonalTailChunk000Sub000Block179Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block179Part000CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block179Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block179Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block179Part000CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block179Part000SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block179Part000] using hcert

def TailChunk000Sub000Block179Part001SupportExplicit : Finset ℕ :=
  ([7415] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block179Part001 : ℚ :=
  (2472499129825 : ℚ) / 3087874483711100928

def SurrogateDiagonalTailChunk000Sub000Block179Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7415
    = surrogateDiagTailX0RatChunk000Sub000Block179Part001

theorem surrogateDiagonalTailChunk000Sub000Block179Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block179Part001CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block179Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block179Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block179Part001CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block179Part001SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block179Part001] using hcert

def TailChunk000Sub000Block179Part002SupportExplicit : Finset ℕ :=
  ([7417] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block179Part002 : ℚ :=
  (859560765625 : ℚ) / 1890800689938043392

def SurrogateDiagonalTailChunk000Sub000Block179Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7417
    = surrogateDiagTailX0RatChunk000Sub000Block179Part002

theorem surrogateDiagonalTailChunk000Sub000Block179Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block179Part002CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block179Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block179Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block179Part002CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block179Part002SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block179Part002] using hcert

def TailChunk000Sub000Block179Part003SupportExplicit : Finset ℕ :=
  ([7418] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block179Part003 : ℚ :=
  (1719241207975 : ℚ) / 472700172484510848

def SurrogateDiagonalTailChunk000Sub000Block179Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7418
    = surrogateDiagTailX0RatChunk000Sub000Block179Part003

theorem surrogateDiagonalTailChunk000Sub000Block179Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block179Part003CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block179Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block179Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block179Part003CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block179Part003SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block179Part003] using hcert

def TailChunk000Sub000Block179Part004SupportExplicit : Finset ℕ :=
  ([7419] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block179Part004 : ℚ :=
  (955275207425 : ℚ) / 746982988617498624

def SurrogateDiagonalTailChunk000Sub000Block179Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7419
    = surrogateDiagTailX0RatChunk000Sub000Block179Part004

theorem surrogateDiagonalTailChunk000Sub000Block179Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block179Part004CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block179Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block179Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block179Part004CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block179Part004SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block179Part004] using hcert

def TailChunk000Sub000Block179Part005SupportExplicit : Finset ℕ :=
  ([7421] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block179Part005 : ℚ :=
  (22051136779 : ℚ) / 44798717952000000

def SurrogateDiagonalTailChunk000Sub000Block179Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7421
    = surrogateDiagTailX0RatChunk000Sub000Block179Part005

theorem surrogateDiagonalTailChunk000Sub000Block179Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block179Part005CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block179Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block179Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block179Part005CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block179Part005SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block179Part005] using hcert

def TailChunk000Sub000Block179Part006SupportExplicit : Finset ℕ :=
  ([7422] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block179Part006 : ℚ :=
  (477774539225 : ℚ) / 46686436788593664

def SurrogateDiagonalTailChunk000Sub000Block179Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7422
    = surrogateDiagTailX0RatChunk000Sub000Block179Part006

theorem surrogateDiagonalTailChunk000Sub000Block179Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block179Part006CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block179Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block179Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block179Part006CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block179Part006SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block179Part006] using hcert

def TailChunk000Sub000Block179Part007SupportExplicit : Finset ℕ :=
  ([7423] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block179Part007 : ℚ :=
  (858568633 : ℚ) / 1520368156828800

def SurrogateDiagonalTailChunk000Sub000Block179Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7423
    = surrogateDiagTailX0RatChunk000Sub000Block179Part007

theorem surrogateDiagonalTailChunk000Sub000Block179Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block179Part007CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block179Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block179Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block179Part007CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block179Part007SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block179Part007] using hcert

def TailChunk000Sub000Block179Part008SupportExplicit : Finset ℕ :=
  ([7426] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block179Part008 : ℚ :=
  (1646722531075 : ℚ) / 414416078086128768

def SurrogateDiagonalTailChunk000Sub000Block179Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7426
    = surrogateDiagTailX0RatChunk000Sub000Block179Part008

theorem surrogateDiagonalTailChunk000Sub000Block179Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block179Part008CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block179Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block179Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block179Part008CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block179Part008SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block179Part008] using hcert

def TailChunk000Sub000Block179Part009SupportExplicit : Finset ℕ :=
  ([7427] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block179Part009 : ℚ :=
  (11304236653 : ℚ) / 163649737418803200

def SurrogateDiagonalTailChunk000Sub000Block179Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7427
    = surrogateDiagTailX0RatChunk000Sub000Block179Part009

theorem surrogateDiagonalTailChunk000Sub000Block179Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block179Part009CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block179Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block179Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block179Part009CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block179Part009SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block179Part009] using hcert

def TailChunk000Sub000Block179Part010SupportExplicit : Finset ℕ :=
  ([7429] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block179Part010 : ℚ :=
  (102096852025 : ℚ) / 1343279164488155136

def SurrogateDiagonalTailChunk000Sub000Block179Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7429
    = surrogateDiagTailX0RatChunk000Sub000Block179Part010

theorem surrogateDiagonalTailChunk000Sub000Block179Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block179Part010CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block179Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block179Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block179Part010CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block179Part010SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block179Part010] using hcert

def TailChunk000Sub000Block179Part011SupportExplicit : Finset ℕ :=
  ([7430] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block179Part011 : ℚ :=
  (758399028775 : ℚ) / 194036059033356288

def SurrogateDiagonalTailChunk000Sub000Block179Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7430
    = surrogateDiagTailX0RatChunk000Sub000Block179Part011

theorem surrogateDiagonalTailChunk000Sub000Block179Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block179Part011CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block179Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block179Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block179Part011CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block179Part011SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block179Part011] using hcert

def TailChunk000Sub000Block179Part012SupportExplicit : Finset ℕ :=
  ([7431] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block179Part012 : ℚ :=
  (383396806475 : ℚ) / 751829577683887104

def SurrogateDiagonalTailChunk000Sub000Block179Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7431
    = surrogateDiagTailX0RatChunk000Sub000Block179Part012

theorem surrogateDiagonalTailChunk000Sub000Block179Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block179Part012CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block179Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block179Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block179Part012CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block179Part012SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block179Part012] using hcert

def TailChunk000Sub000Block179Part013SupportExplicit : Finset ℕ :=
  ([7433] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block179Part013 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub000Block179Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7433
    = surrogateDiagTailX0RatChunk000Sub000Block179Part013

theorem surrogateDiagonalTailChunk000Sub000Block179Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block179Part013CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block179Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block179Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block179Part013CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block179Part013SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block179Part013] using hcert

def TailChunk000Sub000Block179Part014SupportExplicit : Finset ℕ :=
  ([7435] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block179Part014 : ℚ :=
  (25945088575 : ℚ) / 195084192013235328

def SurrogateDiagonalTailChunk000Sub000Block179Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7435
    = surrogateDiagTailX0RatChunk000Sub000Block179Part014

theorem surrogateDiagonalTailChunk000Sub000Block179Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block179Part014CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block179Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block179Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block179Part014CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block179Part014SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block179Part014] using hcert

def TailChunk000Sub000Block179Part015SupportExplicit : Finset ℕ :=
  ([7437] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block179Part015 : ℚ :=
  (34914471925 : ℚ) / 57957534973476864

def SurrogateDiagonalTailChunk000Sub000Block179Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7437
    = surrogateDiagTailX0RatChunk000Sub000Block179Part015

theorem surrogateDiagonalTailChunk000Sub000Block179Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block179Part015CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block179Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block179Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block179Part015CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block179Part015SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block179Part015] using hcert

def TailChunk000Sub000Block179Part016SupportExplicit : Finset ℕ :=
  ([7438] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block179Part016 : ℚ :=
  (216108765625 : ℚ) / 119455021088582322

def SurrogateDiagonalTailChunk000Sub000Block179Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7438
    = surrogateDiagTailX0RatChunk000Sub000Block179Part016

theorem surrogateDiagonalTailChunk000Sub000Block179Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block179Part016CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block179Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block179Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block179Part016CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block179Part016SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block179Part016] using hcert

def TailChunk000Sub000Block179Part017SupportExplicit : Finset ℕ :=
  ([7439] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block179Part017 : ℚ :=
  (66518649625 : ℚ) / 6809854112240191488

def SurrogateDiagonalTailChunk000Sub000Block179Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7439
    = surrogateDiagTailX0RatChunk000Sub000Block179Part017

theorem surrogateDiagonalTailChunk000Sub000Block179Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block179Part017CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block179Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block179Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block179Part017CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block179Part017SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block179Part017] using hcert

def TailChunk000Sub000Block179Part018SupportExplicit : Finset ℕ :=
  ([7441] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block179Part018 : ℚ :=
  (354043523275 : ℚ) / 4122208243001881728

def SurrogateDiagonalTailChunk000Sub000Block179Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7441
    = surrogateDiagTailX0RatChunk000Sub000Block179Part018

theorem surrogateDiagonalTailChunk000Sub000Block179Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block179Part018CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block179Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block179Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block179Part018CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block179Part018SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block179Part018] using hcert

def TailChunk000Sub000Block179Part019SupportExplicit : Finset ℕ :=
  ([7445] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block179Part019 : ℚ :=
  (277226843675 : ℚ) / 1569092524629295104

def SurrogateDiagonalTailChunk000Sub000Block179Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7445
    = surrogateDiagTailX0RatChunk000Sub000Block179Part019

theorem surrogateDiagonalTailChunk000Sub000Block179Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block179Part019CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block179Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block179Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block179Part019CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block179Part019SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block179Part019] using hcert

def TailChunk000Sub000Block179Part020SupportExplicit : Finset ℕ :=
  ([7446] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block179Part020 : ℚ :=
  (210581258725 : ℚ) / 23487430237618176

def SurrogateDiagonalTailChunk000Sub000Block179Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7446
    = surrogateDiagTailX0RatChunk000Sub000Block179Part020

theorem surrogateDiagonalTailChunk000Sub000Block179Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block179Part020CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block179Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block179Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block179Part020CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block179Part020SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block179Part020] using hcert

def TailChunk000Sub000Block179Part021SupportExplicit : Finset ℕ :=
  ([7447] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block179Part021 : ℚ :=
  (2704184637 : ℚ) / 69622943329638400

def SurrogateDiagonalTailChunk000Sub000Block179Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7447
    = surrogateDiagTailX0RatChunk000Sub000Block179Part021

theorem surrogateDiagonalTailChunk000Sub000Block179Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block179Part021CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block179Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block179Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block179Part021CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block179Part021SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block179Part021] using hcert

def TailChunk000Sub000Block179Part022SupportExplicit : Finset ℕ :=
  ([7449] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block179Part022 : ℚ :=
  (30886773397 : ℚ) / 43246027572019200

def SurrogateDiagonalTailChunk000Sub000Block179Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7449
    = surrogateDiagTailX0RatChunk000Sub000Block179Part022

theorem surrogateDiagonalTailChunk000Sub000Block179Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block179Part022CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block179Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block179Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block179Part022CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block179Part022SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block179Part022] using hcert

def TailChunk000Sub000Block179Part023SupportExplicit : Finset ℕ :=
  ([7451] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block179Part023 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub000Block179Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7451
    = surrogateDiagTailX0RatChunk000Sub000Block179Part023

theorem surrogateDiagonalTailChunk000Sub000Block179Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block179Part023CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block179Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block179Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block179Part023CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block179Part023SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block179Part023] using hcert

def TailChunk000Sub000Block179Part024SupportExplicit : Finset ℕ :=
  ([7453] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block179Part024 : ℚ :=
  (86273474275 : ℚ) / 6601138509434585088

def SurrogateDiagonalTailChunk000Sub000Block179Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7453
    = surrogateDiagTailX0RatChunk000Sub000Block179Part024

theorem surrogateDiagonalTailChunk000Sub000Block179Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block179Part024CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block179Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block179Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block179Part024CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block179Part024SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block179Part024] using hcert

def surrogateDiagonalTailChunk000Sub000Block179HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block179Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block179Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block179Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block179Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block179Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block179Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block179Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block179Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block179Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block179Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block179Head : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block179Part000
    + surrogateDiagTailX0RatChunk000Sub000Block179Part001
    + surrogateDiagTailX0RatChunk000Sub000Block179Part002
    + surrogateDiagTailX0RatChunk000Sub000Block179Part003
    + surrogateDiagTailX0RatChunk000Sub000Block179Part004
    + surrogateDiagTailX0RatChunk000Sub000Block179Part005
    + surrogateDiagTailX0RatChunk000Sub000Block179Part006
    + surrogateDiagTailX0RatChunk000Sub000Block179Part007
    + surrogateDiagTailX0RatChunk000Sub000Block179Part008
    + surrogateDiagTailX0RatChunk000Sub000Block179Part009

def surrogateDiagonalTailChunk000Sub000Block179MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block179Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block179Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block179Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block179Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block179Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block179Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block179Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block179Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block179Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block179Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block179Mid : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block179Part010
    + surrogateDiagTailX0RatChunk000Sub000Block179Part011
    + surrogateDiagTailX0RatChunk000Sub000Block179Part012
    + surrogateDiagTailX0RatChunk000Sub000Block179Part013
    + surrogateDiagTailX0RatChunk000Sub000Block179Part014
    + surrogateDiagTailX0RatChunk000Sub000Block179Part015
    + surrogateDiagTailX0RatChunk000Sub000Block179Part016
    + surrogateDiagTailX0RatChunk000Sub000Block179Part017
    + surrogateDiagTailX0RatChunk000Sub000Block179Part018
    + surrogateDiagTailX0RatChunk000Sub000Block179Part019

def surrogateDiagonalTailChunk000Sub000Block179TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block179Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block179Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block179Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block179Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block179Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block179Tail : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block179Part020
    + surrogateDiagTailX0RatChunk000Sub000Block179Part021
    + surrogateDiagTailX0RatChunk000Sub000Block179Part022
    + surrogateDiagTailX0RatChunk000Sub000Block179Part023
    + surrogateDiagTailX0RatChunk000Sub000Block179Part024

def surrogateDiagonalTailChunk000Sub000Block179Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub000Block179HeadSum X0
    + surrogateDiagonalTailChunk000Sub000Block179MidSum X0
    + surrogateDiagonalTailChunk000Sub000Block179TailSum X0

def surrogateDiagTailX0RatChunk000Sub000Block179 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block179Part000
    + surrogateDiagTailX0RatChunk000Sub000Block179Part001
    + surrogateDiagTailX0RatChunk000Sub000Block179Part002
    + surrogateDiagTailX0RatChunk000Sub000Block179Part003
    + surrogateDiagTailX0RatChunk000Sub000Block179Part004
    + surrogateDiagTailX0RatChunk000Sub000Block179Part005
    + surrogateDiagTailX0RatChunk000Sub000Block179Part006
    + surrogateDiagTailX0RatChunk000Sub000Block179Part007
    + surrogateDiagTailX0RatChunk000Sub000Block179Part008
    + surrogateDiagTailX0RatChunk000Sub000Block179Part009
    + surrogateDiagTailX0RatChunk000Sub000Block179Part010
    + surrogateDiagTailX0RatChunk000Sub000Block179Part011
    + surrogateDiagTailX0RatChunk000Sub000Block179Part012
    + surrogateDiagTailX0RatChunk000Sub000Block179Part013
    + surrogateDiagTailX0RatChunk000Sub000Block179Part014
    + surrogateDiagTailX0RatChunk000Sub000Block179Part015
    + surrogateDiagTailX0RatChunk000Sub000Block179Part016
    + surrogateDiagTailX0RatChunk000Sub000Block179Part017
    + surrogateDiagTailX0RatChunk000Sub000Block179Part018
    + surrogateDiagTailX0RatChunk000Sub000Block179Part019
    + surrogateDiagTailX0RatChunk000Sub000Block179Part020
    + surrogateDiagTailX0RatChunk000Sub000Block179Part021
    + surrogateDiagTailX0RatChunk000Sub000Block179Part022
    + surrogateDiagTailX0RatChunk000Sub000Block179Part023
    + surrogateDiagTailX0RatChunk000Sub000Block179Part024

theorem surrogateDiagTailX0RatChunk000Sub000Block179_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk000Sub000Block179Head + surrogateDiagTailX0RatChunk000Sub000Block179Mid + surrogateDiagTailX0RatChunk000Sub000Block179Tail =
      surrogateDiagTailX0RatChunk000Sub000Block179 := by
  unfold surrogateDiagTailX0RatChunk000Sub000Block179Head surrogateDiagTailX0RatChunk000Sub000Block179Mid surrogateDiagTailX0RatChunk000Sub000Block179Tail surrogateDiagTailX0RatChunk000Sub000Block179
  ring

def SurrogateDiagonalTailChunk000Sub000Block179HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block179HeadSum X0 = surrogateDiagTailX0RatChunk000Sub000Block179Head

def SurrogateDiagonalTailChunk000Sub000Block179MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block179MidSum X0 = surrogateDiagTailX0RatChunk000Sub000Block179Mid

def SurrogateDiagonalTailChunk000Sub000Block179TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block179TailSum X0 = surrogateDiagTailX0RatChunk000Sub000Block179Tail

theorem surrogateDiagonalTailChunk000Sub000Block179_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk000Sub000Block179HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk000Sub000Block179MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk000Sub000Block179TailCertificateAt X0) :
    surrogateDiagonalTailChunk000Sub000Block179Sum X0 = surrogateDiagTailX0RatChunk000Sub000Block179 := by
  unfold SurrogateDiagonalTailChunk000Sub000Block179HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk000Sub000Block179MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk000Sub000Block179TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk000Sub000Block179Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk000Sub000Block179_eq_head_add_mid_add_tail

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

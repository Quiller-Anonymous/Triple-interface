import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0TailPilot25

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

open scoped BigOperators

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

/- Generated direct-term certificate blocks for tail chunk 000, subchunk 000, blocks [170,171). -/

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

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

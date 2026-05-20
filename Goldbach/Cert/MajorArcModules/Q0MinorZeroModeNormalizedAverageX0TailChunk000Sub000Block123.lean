import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0TailPilot25

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

open scoped BigOperators

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

/- Generated direct-term certificate blocks for tail chunk 000, subchunk 000, blocks [123,124). -/

/- Block 123 covers tail-support indices [3075,3100) and q from 5111 to 5151. -/

def TailChunk000Sub000Block123Part000SupportExplicit : Finset ℕ :=
  ([5111] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block123Part000 : ℚ :=
  (385286666875 : ℚ) / 338529144785859072

def SurrogateDiagonalTailChunk000Sub000Block123Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5111
    = surrogateDiagTailX0RatChunk000Sub000Block123Part000

theorem surrogateDiagonalTailChunk000Sub000Block123Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block123Part000CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block123Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block123Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block123Part000CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block123Part000SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block123Part000] using hcert

def TailChunk000Sub000Block123Part001SupportExplicit : Finset ℕ :=
  ([5113] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block123Part001 : ℚ :=
  (408480765625 : ℚ) / 426904023676948992

def SurrogateDiagonalTailChunk000Sub000Block123Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5113
    = surrogateDiagTailX0RatChunk000Sub000Block123Part001

theorem surrogateDiagonalTailChunk000Sub000Block123Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block123Part001CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block123Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block123Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block123Part001CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block123Part001SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block123Part001] using hcert

def TailChunk000Sub000Block123Part002SupportExplicit : Finset ℕ :=
  ([5114] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block123Part002 : ℚ :=
  (817117668775 : ℚ) / 106726005919237248

def SurrogateDiagonalTailChunk000Sub000Block123Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5114
    = surrogateDiagTailX0RatChunk000Sub000Block123Part002

theorem surrogateDiagonalTailChunk000Sub000Block123Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block123Part002CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block123Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block123Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block123Part002CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block123Part002SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block123Part002] using hcert

def TailChunk000Sub000Block123Part003SupportExplicit : Finset ℕ :=
  ([5115] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block123Part003 : ℚ :=
  (30432257983 : ℚ) / 3318423552000000

def SurrogateDiagonalTailChunk000Sub000Block123Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5115
    = surrogateDiagTailX0RatChunk000Sub000Block123Part003

theorem surrogateDiagonalTailChunk000Sub000Block123Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block123Part003CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block123Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block123Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block123Part003CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block123Part003SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block123Part003] using hcert

def TailChunk000Sub000Block123Part004SupportExplicit : Finset ℕ :=
  ([5117] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block123Part004 : ℚ :=
  (642474813425 : ℚ) / 330429609378054144

def SurrogateDiagonalTailChunk000Sub000Block123Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5117
    = surrogateDiagTailX0RatChunk000Sub000Block123Part004

theorem surrogateDiagonalTailChunk000Sub000Block123Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block123Part004CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block123Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block123Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block123Part004CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block123Part004SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block123Part004] using hcert

def TailChunk000Sub000Block123Part005SupportExplicit : Finset ℕ :=
  ([5118] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block123Part005 : ℚ :=
  (4037425 : ℚ) / 156129368064

def SurrogateDiagonalTailChunk000Sub000Block123Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5118
    = surrogateDiagTailX0RatChunk000Sub000Block123Part005

theorem surrogateDiagonalTailChunk000Sub000Block123Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block123Part005CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block123Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block123Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block123Part005CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block123Part005SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block123Part005] using hcert

def TailChunk000Sub000Block123Part006SupportExplicit : Finset ℕ :=
  ([5119] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block123Part006 : ℚ :=
  (409440015625 : ℚ) / 428911799280424722

def SurrogateDiagonalTailChunk000Sub000Block123Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5119
    = surrogateDiagTailX0RatChunk000Sub000Block123Part006

theorem surrogateDiagonalTailChunk000Sub000Block123Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block123Part006CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block123Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block123Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block123Part006CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block123Part006SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block123Part006] using hcert

def TailChunk000Sub000Block123Part007SupportExplicit : Finset ℕ :=
  ([5122] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block123Part007 : ℚ :=
  (187648671475 : ℚ) / 19130051410993152

def SurrogateDiagonalTailChunk000Sub000Block123Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5122
    = surrogateDiagTailX0RatChunk000Sub000Block123Part007

theorem surrogateDiagonalTailChunk000Sub000Block123Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block123Part007CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block123Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block123Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block123Part007CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block123Part007SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block123Part007] using hcert

def TailChunk000Sub000Block123Part008SupportExplicit : Finset ℕ :=
  ([5123] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block123Part008 : ℚ :=
  (1589876081875 : ℚ) / 1523186940694284288

def SurrogateDiagonalTailChunk000Sub000Block123Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5123
    = surrogateDiagTailX0RatChunk000Sub000Block123Part008

theorem surrogateDiagonalTailChunk000Sub000Block123Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block123Part008CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block123Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block123Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block123Part008CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block123Part008SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block123Part008] using hcert

def TailChunk000Sub000Block123Part009SupportExplicit : Finset ℕ :=
  ([5126] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block123Part009 : ℚ :=
  (5946742109 : ℚ) / 579520476119040

def SurrogateDiagonalTailChunk000Sub000Block123Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5126
    = surrogateDiagTailX0RatChunk000Sub000Block123Part009

theorem surrogateDiagonalTailChunk000Sub000Block123Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block123Part009CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block123Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block123Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block123Part009CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block123Part009SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block123Part009] using hcert

def TailChunk000Sub000Block123Part010SupportExplicit : Finset ℕ :=
  ([5127] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block123Part010 : ℚ :=
  (319125 : ℚ) / 99246988288

def SurrogateDiagonalTailChunk000Sub000Block123Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5127
    = surrogateDiagTailX0RatChunk000Sub000Block123Part010

theorem surrogateDiagonalTailChunk000Sub000Block123Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block123Part010CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block123Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block123Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block123Part010CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block123Part010SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block123Part010] using hcert

def TailChunk000Sub000Block123Part011SupportExplicit : Finset ℕ :=
  ([5129] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block123Part011 : ℚ :=
  (1562669730475 : ℚ) / 1422752901541411968

def SurrogateDiagonalTailChunk000Sub000Block123Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5129
    = surrogateDiagTailX0RatChunk000Sub000Block123Part011

theorem surrogateDiagonalTailChunk000Sub000Block123Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block123Part011CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block123Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block123Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block123Part011CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block123Part011SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block123Part011] using hcert

def TailChunk000Sub000Block123Part012SupportExplicit : Finset ℕ :=
  ([5131] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block123Part012 : ℚ :=
  (1375189087975 : ℚ) / 930413888650856448

def SurrogateDiagonalTailChunk000Sub000Block123Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5131
    = surrogateDiagTailX0RatChunk000Sub000Block123Part012

theorem surrogateDiagonalTailChunk000Sub000Block123Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block123Part012CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block123Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block123Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block123Part012CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block123Part012SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block123Part012] using hcert

def TailChunk000Sub000Block123Part013SupportExplicit : Finset ℕ :=
  ([5133] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block123Part013 : ℚ :=
  (520615959125 : ℚ) / 139142866316181504

def SurrogateDiagonalTailChunk000Sub000Block123Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5133
    = surrogateDiagTailX0RatChunk000Sub000Block123Part013

theorem surrogateDiagonalTailChunk000Sub000Block123Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block123Part013CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block123Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block123Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block123Part013CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block123Part013SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block123Part013] using hcert

def TailChunk000Sub000Block123Part014SupportExplicit : Finset ℕ :=
  ([5134] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block123Part014 : ℚ :=
  (15374228303 : ℚ) / 1659211776000000

def SurrogateDiagonalTailChunk000Sub000Block123Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5134
    = surrogateDiagTailX0RatChunk000Sub000Block123Part014

theorem surrogateDiagonalTailChunk000Sub000Block123Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block123Part014CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block123Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block123Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block123Part014CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block123Part014SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block123Part014] using hcert

def TailChunk000Sub000Block123Part015SupportExplicit : Finset ℕ :=
  ([5135] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block123Part015 : ℚ :=
  (1200679166425 : ℚ) / 491326534435995648

def SurrogateDiagonalTailChunk000Sub000Block123Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5135
    = surrogateDiagTailX0RatChunk000Sub000Block123Part015

theorem surrogateDiagonalTailChunk000Sub000Block123Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block123Part015CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block123Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block123Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block123Part015CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block123Part015SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block123Part015] using hcert

def TailChunk000Sub000Block123Part016SupportExplicit : Finset ℕ :=
  ([5137] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block123Part016 : ℚ :=
  (2992735427 : ℚ) / 2358307984083360

def SurrogateDiagonalTailChunk000Sub000Block123Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5137
    = surrogateDiagTailX0RatChunk000Sub000Block123Part016

theorem surrogateDiagonalTailChunk000Sub000Block123Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block123Part016CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block123Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block123Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block123Part016CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block123Part016SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block123Part016] using hcert

def TailChunk000Sub000Block123Part017SupportExplicit : Finset ℕ :=
  ([5138] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block123Part017 : ℚ :=
  (78364357225 : ℚ) / 6461207560075392

def SurrogateDiagonalTailChunk000Sub000Block123Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5138
    = surrogateDiagTailX0RatChunk000Sub000Block123Part017

theorem surrogateDiagonalTailChunk000Sub000Block123Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block123Part017CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block123Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block123Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block123Part017CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block123Part017SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block123Part017] using hcert

def TailChunk000Sub000Block123Part018SupportExplicit : Finset ℕ :=
  ([5141] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block123Part018 : ℚ :=
  (534463333925 : ℚ) / 517611493068374016

def SurrogateDiagonalTailChunk000Sub000Block123Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5141
    = surrogateDiagTailX0RatChunk000Sub000Block123Part018

theorem surrogateDiagonalTailChunk000Sub000Block123Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block123Part018CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block123Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block123Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block123Part018CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block123Part018SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block123Part018] using hcert

def TailChunk000Sub000Block123Part019SupportExplicit : Finset ℕ :=
  ([5142] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block123Part019 : ℚ :=
  (110035275 : ℚ) / 4295216365568

def SurrogateDiagonalTailChunk000Sub000Block123Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5142
    = surrogateDiagTailX0RatChunk000Sub000Block123Part019

theorem surrogateDiagonalTailChunk000Sub000Block123Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block123Part019CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block123Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block123Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block123Part019CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block123Part019SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block123Part019] using hcert

def TailChunk000Sub000Block123Part020SupportExplicit : Finset ℕ :=
  ([5143] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block123Part020 : ℚ :=
  (1595697500425 : ℚ) / 1523186940694284288

def SurrogateDiagonalTailChunk000Sub000Block123Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5143
    = surrogateDiagTailX0RatChunk000Sub000Block123Part020

theorem surrogateDiagonalTailChunk000Sub000Block123Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block123Part020CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block123Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block123Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block123Part020CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block123Part020SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block123Part020] using hcert

def TailChunk000Sub000Block123Part021SupportExplicit : Finset ℕ :=
  ([5146] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block123Part021 : ℚ :=
  (31608990049 : ℚ) / 3662918693251200

def SurrogateDiagonalTailChunk000Sub000Block123Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5146
    = surrogateDiagTailX0RatChunk000Sub000Block123Part021

theorem surrogateDiagonalTailChunk000Sub000Block123Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block123Part021CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block123Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block123Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block123Part021CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block123Part021SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block123Part021] using hcert

def TailChunk000Sub000Block123Part022SupportExplicit : Finset ℕ :=
  ([5147] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block123Part022 : ℚ :=
  (413931390625 : ℚ) / 438375218194546482

def SurrogateDiagonalTailChunk000Sub000Block123Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5147
    = surrogateDiagTailX0RatChunk000Sub000Block123Part022

theorem surrogateDiagonalTailChunk000Sub000Block123Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block123Part022CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block123Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block123Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block123Part022CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block123Part022SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block123Part022] using hcert

def TailChunk000Sub000Block123Part023SupportExplicit : Finset ℕ :=
  ([5149] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block123Part023 : ℚ :=
  (31191854471 : ℚ) / 27899854063041600

def SurrogateDiagonalTailChunk000Sub000Block123Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5149
    = surrogateDiagTailX0RatChunk000Sub000Block123Part023

theorem surrogateDiagonalTailChunk000Sub000Block123Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block123Part023CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block123Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block123Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block123Part023CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block123Part023SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block123Part023] using hcert

def TailChunk000Sub000Block123Part024SupportExplicit : Finset ℕ :=
  ([5151] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block123Part024 : ℚ :=
  (8220796751 : ℚ) / 2097571430400000

def SurrogateDiagonalTailChunk000Sub000Block123Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5151
    = surrogateDiagTailX0RatChunk000Sub000Block123Part024

theorem surrogateDiagonalTailChunk000Sub000Block123Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block123Part024CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block123Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block123Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block123Part024CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block123Part024SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block123Part024] using hcert

def surrogateDiagonalTailChunk000Sub000Block123HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block123Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block123Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block123Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block123Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block123Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block123Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block123Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block123Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block123Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block123Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block123Head : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block123Part000
    + surrogateDiagTailX0RatChunk000Sub000Block123Part001
    + surrogateDiagTailX0RatChunk000Sub000Block123Part002
    + surrogateDiagTailX0RatChunk000Sub000Block123Part003
    + surrogateDiagTailX0RatChunk000Sub000Block123Part004
    + surrogateDiagTailX0RatChunk000Sub000Block123Part005
    + surrogateDiagTailX0RatChunk000Sub000Block123Part006
    + surrogateDiagTailX0RatChunk000Sub000Block123Part007
    + surrogateDiagTailX0RatChunk000Sub000Block123Part008
    + surrogateDiagTailX0RatChunk000Sub000Block123Part009

def surrogateDiagonalTailChunk000Sub000Block123MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block123Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block123Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block123Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block123Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block123Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block123Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block123Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block123Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block123Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block123Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block123Mid : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block123Part010
    + surrogateDiagTailX0RatChunk000Sub000Block123Part011
    + surrogateDiagTailX0RatChunk000Sub000Block123Part012
    + surrogateDiagTailX0RatChunk000Sub000Block123Part013
    + surrogateDiagTailX0RatChunk000Sub000Block123Part014
    + surrogateDiagTailX0RatChunk000Sub000Block123Part015
    + surrogateDiagTailX0RatChunk000Sub000Block123Part016
    + surrogateDiagTailX0RatChunk000Sub000Block123Part017
    + surrogateDiagTailX0RatChunk000Sub000Block123Part018
    + surrogateDiagTailX0RatChunk000Sub000Block123Part019

def surrogateDiagonalTailChunk000Sub000Block123TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block123Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block123Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block123Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block123Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block123Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block123Tail : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block123Part020
    + surrogateDiagTailX0RatChunk000Sub000Block123Part021
    + surrogateDiagTailX0RatChunk000Sub000Block123Part022
    + surrogateDiagTailX0RatChunk000Sub000Block123Part023
    + surrogateDiagTailX0RatChunk000Sub000Block123Part024

def surrogateDiagonalTailChunk000Sub000Block123Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub000Block123HeadSum X0
    + surrogateDiagonalTailChunk000Sub000Block123MidSum X0
    + surrogateDiagonalTailChunk000Sub000Block123TailSum X0

def surrogateDiagTailX0RatChunk000Sub000Block123 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block123Part000
    + surrogateDiagTailX0RatChunk000Sub000Block123Part001
    + surrogateDiagTailX0RatChunk000Sub000Block123Part002
    + surrogateDiagTailX0RatChunk000Sub000Block123Part003
    + surrogateDiagTailX0RatChunk000Sub000Block123Part004
    + surrogateDiagTailX0RatChunk000Sub000Block123Part005
    + surrogateDiagTailX0RatChunk000Sub000Block123Part006
    + surrogateDiagTailX0RatChunk000Sub000Block123Part007
    + surrogateDiagTailX0RatChunk000Sub000Block123Part008
    + surrogateDiagTailX0RatChunk000Sub000Block123Part009
    + surrogateDiagTailX0RatChunk000Sub000Block123Part010
    + surrogateDiagTailX0RatChunk000Sub000Block123Part011
    + surrogateDiagTailX0RatChunk000Sub000Block123Part012
    + surrogateDiagTailX0RatChunk000Sub000Block123Part013
    + surrogateDiagTailX0RatChunk000Sub000Block123Part014
    + surrogateDiagTailX0RatChunk000Sub000Block123Part015
    + surrogateDiagTailX0RatChunk000Sub000Block123Part016
    + surrogateDiagTailX0RatChunk000Sub000Block123Part017
    + surrogateDiagTailX0RatChunk000Sub000Block123Part018
    + surrogateDiagTailX0RatChunk000Sub000Block123Part019
    + surrogateDiagTailX0RatChunk000Sub000Block123Part020
    + surrogateDiagTailX0RatChunk000Sub000Block123Part021
    + surrogateDiagTailX0RatChunk000Sub000Block123Part022
    + surrogateDiagTailX0RatChunk000Sub000Block123Part023
    + surrogateDiagTailX0RatChunk000Sub000Block123Part024

theorem surrogateDiagTailX0RatChunk000Sub000Block123_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk000Sub000Block123Head + surrogateDiagTailX0RatChunk000Sub000Block123Mid + surrogateDiagTailX0RatChunk000Sub000Block123Tail =
      surrogateDiagTailX0RatChunk000Sub000Block123 := by
  unfold surrogateDiagTailX0RatChunk000Sub000Block123Head surrogateDiagTailX0RatChunk000Sub000Block123Mid surrogateDiagTailX0RatChunk000Sub000Block123Tail surrogateDiagTailX0RatChunk000Sub000Block123
  ring

def SurrogateDiagonalTailChunk000Sub000Block123HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block123HeadSum X0 = surrogateDiagTailX0RatChunk000Sub000Block123Head

def SurrogateDiagonalTailChunk000Sub000Block123MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block123MidSum X0 = surrogateDiagTailX0RatChunk000Sub000Block123Mid

def SurrogateDiagonalTailChunk000Sub000Block123TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block123TailSum X0 = surrogateDiagTailX0RatChunk000Sub000Block123Tail

theorem surrogateDiagonalTailChunk000Sub000Block123_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk000Sub000Block123HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk000Sub000Block123MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk000Sub000Block123TailCertificateAt X0) :
    surrogateDiagonalTailChunk000Sub000Block123Sum X0 = surrogateDiagTailX0RatChunk000Sub000Block123 := by
  unfold SurrogateDiagonalTailChunk000Sub000Block123HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk000Sub000Block123MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk000Sub000Block123TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk000Sub000Block123Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk000Sub000Block123_eq_head_add_mid_add_tail

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0TailPilot25

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

open scoped BigOperators

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

/- Generated direct-term certificate blocks for tail chunk 000, subchunk 000, blocks [2,3). -/

/- Block 002 covers tail-support indices [50,75) and q from 133 to 174. -/

def TailChunk000Sub000Block002Part000SupportExplicit : Finset ℕ :=
  ([133] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block002Part000 : ℚ :=
  (2083322575 : ℚ) / 21261891528

def SurrogateDiagonalTailChunk000Sub000Block002Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 133
    = surrogateDiagTailX0RatChunk000Sub000Block002Part000

theorem surrogateDiagonalTailChunk000Sub000Block002Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block002Part000CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block002Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block002Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block002Part000CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block002Part000SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block002Part000] using hcert

def TailChunk000Sub000Block002Part001SupportExplicit : Finset ℕ :=
  ([134] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block002Part001 : ℚ :=
  (2303418125 : ℚ) / 5271814152

def SurrogateDiagonalTailChunk000Sub000Block002Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 134
    = surrogateDiagTailX0RatChunk000Sub000Block002Part001

theorem surrogateDiagonalTailChunk000Sub000Block002Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block002Part001CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block002Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block002Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block002Part001CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block002Part001SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block002Part001] using hcert

def TailChunk000Sub000Block002Part002SupportExplicit : Finset ℕ :=
  ([137] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block002Part002 : ℚ :=
  (1267376725 : ℚ) / 25159590912

def SurrogateDiagonalTailChunk000Sub000Block002Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 137
    = surrogateDiagTailX0RatChunk000Sub000Block002Part002

theorem surrogateDiagonalTailChunk000Sub000Block002Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block002Part002CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block002Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block002Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block002Part002CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block002Part002SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block002Part002] using hcert

def TailChunk000Sub000Block002Part003SupportExplicit : Finset ℕ :=
  ([138] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block002Part003 : ℚ :=
  (6849522575 : ℚ) / 4686057024

def SurrogateDiagonalTailChunk000Sub000Block002Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 138
    = surrogateDiagTailX0RatChunk000Sub000Block002Part003

theorem surrogateDiagonalTailChunk000Sub000Block002Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block002Part003CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block002Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block002Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block002Part003CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block002Part003SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block002Part003] using hcert

def TailChunk000Sub000Block002Part004SupportExplicit : Finset ℕ :=
  ([139] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block002Part004 : ℚ :=
  (799406375 : ℚ) / 16793818092

def SurrogateDiagonalTailChunk000Sub000Block002Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 139
    = surrogateDiagTailX0RatChunk000Sub000Block002Part004

theorem surrogateDiagonalTailChunk000Sub000Block002Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block002Part004CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block002Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block002Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block002Part004CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block002Part004SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block002Part004] using hcert

def TailChunk000Sub000Block002Part005SupportExplicit : Finset ℕ :=
  ([141] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block002Part005 : ℚ :=
  (28522363225 : ℚ) / 179134059648

def SurrogateDiagonalTailChunk000Sub000Block002Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 141
    = surrogateDiagTailX0RatChunk000Sub000Block002Part005

theorem surrogateDiagonalTailChunk000Sub000Block002Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block002Part005CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block002Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block002Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block002Part005CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block002Part005SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block002Part005] using hcert

def TailChunk000Sub000Block002Part006SupportExplicit : Finset ℕ :=
  ([142] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block002Part006 : ℚ :=
  (24857171 : ℚ) / 68613720

def SurrogateDiagonalTailChunk000Sub000Block002Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 142
    = surrogateDiagTailX0RatChunk000Sub000Block002Part006

theorem surrogateDiagonalTailChunk000Sub000Block002Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block002Part006CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block002Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block002Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block002Part006CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block002Part006SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block002Part006] using hcert

def TailChunk000Sub000Block002Part007SupportExplicit : Finset ℕ :=
  ([143] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block002Part007 : ℚ :=
  (150179029 : ℚ) / 2074014720

def SurrogateDiagonalTailChunk000Sub000Block002Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 143
    = surrogateDiagTailX0RatChunk000Sub000Block002Part007

theorem surrogateDiagonalTailChunk000Sub000Block002Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block002Part007CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block002Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block002Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block002Part007CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block002Part007SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block002Part007] using hcert

def TailChunk000Sub000Block002Part008SupportExplicit : Finset ℕ :=
  ([145] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block002Part008 : ℚ :=
  (34633252225 : ℚ) / 393458515968

def SurrogateDiagonalTailChunk000Sub000Block002Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 145
    = surrogateDiagTailX0RatChunk000Sub000Block002Part008

theorem surrogateDiagonalTailChunk000Sub000Block002Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block002Part008CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block002Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block002Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block002Part008CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block002Part008SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block002Part008] using hcert

def TailChunk000Sub000Block002Part009SupportExplicit : Finset ℕ :=
  ([146] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block002Part009 : ℚ :=
  (11172381725 : ℚ) / 33599038464

def SurrogateDiagonalTailChunk000Sub000Block002Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 146
    = surrogateDiagTailX0RatChunk000Sub000Block002Part009

theorem surrogateDiagonalTailChunk000Sub000Block002Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block002Part009CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block002Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block002Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block002Part009CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block002Part009SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block002Part009] using hcert

def TailChunk000Sub000Block002Part010SupportExplicit : Finset ℕ :=
  ([149] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block002Part010 : ℚ :=
  (46865755975 : ℚ) / 1199702932608

def SurrogateDiagonalTailChunk000Sub000Block002Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 149
    = surrogateDiagTailX0RatChunk000Sub000Block002Part010

theorem surrogateDiagonalTailChunk000Sub000Block002Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block002Part010CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block002Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block002Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block002Part010CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block002Part010SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block002Part010] using hcert

def TailChunk000Sub000Block002Part011SupportExplicit : Finset ℕ :=
  ([151] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block002Part011 : ℚ :=
  (5768653 : ℚ) / 156281250

def SurrogateDiagonalTailChunk000Sub000Block002Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 151
    = surrogateDiagTailX0RatChunk000Sub000Block002Part011

theorem surrogateDiagonalTailChunk000Sub000Block002Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block002Part011CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block002Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block002Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block002Part011CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block002Part011SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block002Part011] using hcert

def TailChunk000Sub000Block002Part012SupportExplicit : Finset ℕ :=
  ([154] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block002Part012 : ℚ :=
  (41711257 : ℚ) / 72014400

def SurrogateDiagonalTailChunk000Sub000Block002Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 154
    = surrogateDiagTailX0RatChunk000Sub000Block002Part012

theorem surrogateDiagonalTailChunk000Sub000Block002Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block002Part012CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block002Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block002Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block002Part012CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block002Part012SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block002Part012] using hcert

def TailChunk000Sub000Block002Part013SupportExplicit : Finset ℕ :=
  ([155] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block002Part013 : ℚ :=
  (6352907 : ℚ) / 86417280

def SurrogateDiagonalTailChunk000Sub000Block002Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 155
    = surrogateDiagTailX0RatChunk000Sub000Block002Part013

theorem surrogateDiagonalTailChunk000Sub000Block002Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block002Part013CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block002Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block002Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block002Part013CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block002Part013SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block002Part013] using hcert

def TailChunk000Sub000Block002Part014SupportExplicit : Finset ℕ :=
  ([157] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block002Part014 : ℚ :=
  (3062022025 : ℚ) / 92556147528

def SurrogateDiagonalTailChunk000Sub000Block002Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 157
    = surrogateDiagTailX0RatChunk000Sub000Block002Part014

theorem surrogateDiagonalTailChunk000Sub000Block002Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block002Part014CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block002Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block002Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block002Part014CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block002Part014SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block002Part014] using hcert

def TailChunk000Sub000Block002Part015SupportExplicit : Finset ℕ :=
  ([158] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block002Part015 : ℚ :=
  (898860025 : ℚ) / 3428005464

def SurrogateDiagonalTailChunk000Sub000Block002Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 158
    = surrogateDiagTailX0RatChunk000Sub000Block002Part015

theorem surrogateDiagonalTailChunk000Sub000Block002Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block002Part015CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block002Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block002Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block002Part015CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block002Part015SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block002Part015] using hcert

def TailChunk000Sub000Block002Part016SupportExplicit : Finset ℕ :=
  ([159] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block002Part016 : ℚ :=
  (32898730825 : ℚ) / 292523132928

def SurrogateDiagonalTailChunk000Sub000Block002Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 159
    = surrogateDiagTailX0RatChunk000Sub000Block002Part016

theorem surrogateDiagonalTailChunk000Sub000Block002Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block002Part016CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block002Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block002Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block002Part016CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block002Part016SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block002Part016] using hcert

def TailChunk000Sub000Block002Part017SupportExplicit : Finset ℕ :=
  ([161] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block002Part017 : ℚ :=
  (1144077725 : ℚ) / 21087256608

def SurrogateDiagonalTailChunk000Sub000Block002Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 161
    = surrogateDiagTailX0RatChunk000Sub000Block002Part017

theorem surrogateDiagonalTailChunk000Sub000Block002Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block002Part017CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block002Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block002Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block002Part017CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block002Part017SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block002Part017] using hcert

def TailChunk000Sub000Block002Part018SupportExplicit : Finset ℕ :=
  ([163] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block002Part018 : ℚ :=
  (51168572875 : ℚ) / 1722213213768

def SurrogateDiagonalTailChunk000Sub000Block002Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 163
    = surrogateDiagTailX0RatChunk000Sub000Block002Part018

theorem surrogateDiagonalTailChunk000Sub000Block002Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block002Part018CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block002Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block002Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block002Part018CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block002Part018SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block002Part018] using hcert

def TailChunk000Sub000Block002Part019SupportExplicit : Finset ℕ :=
  ([165] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block002Part019 : ℚ :=
  (6235237 : ℚ) / 25605120

def SurrogateDiagonalTailChunk000Sub000Block002Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 165
    = surrogateDiagTailX0RatChunk000Sub000Block002Part019

theorem surrogateDiagonalTailChunk000Sub000Block002Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block002Part019CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block002Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block002Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block002Part019CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block002Part019SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block002Part019] using hcert

def TailChunk000Sub000Block002Part020SupportExplicit : Finset ℕ :=
  ([166] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block002Part020 : ℚ :=
  (4254818625 : ℚ) / 18842174348

def SurrogateDiagonalTailChunk000Sub000Block002Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 166
    = surrogateDiagTailX0RatChunk000Sub000Block002Part020

theorem surrogateDiagonalTailChunk000Sub000Block002Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block002Part020CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block002Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block002Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block002Part020CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block002Part020SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block002Part020] using hcert

def TailChunk000Sub000Block002Part021SupportExplicit : Finset ℕ :=
  ([167] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block002Part021 : ℚ :=
  (25132869575 : ℚ) / 949356253284

def SurrogateDiagonalTailChunk000Sub000Block002Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 167
    = surrogateDiagTailX0RatChunk000Sub000Block002Part021

theorem surrogateDiagonalTailChunk000Sub000Block002Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block002Part021CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block002Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block002Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block002Part021CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block002Part021SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block002Part021] using hcert

def TailChunk000Sub000Block002Part022SupportExplicit : Finset ℕ :=
  ([170] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block002Part022 : ℚ :=
  (10022659325 : ℚ) / 20975714304

def SurrogateDiagonalTailChunk000Sub000Block002Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 170
    = surrogateDiagTailX0RatChunk000Sub000Block002Part022

theorem surrogateDiagonalTailChunk000Sub000Block002Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block002Part022CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block002Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block002Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block002Part022CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block002Part022SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block002Part022] using hcert

def TailChunk000Sub000Block002Part023SupportExplicit : Finset ℕ :=
  ([173] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block002Part023 : ℚ :=
  (26971266575 : ℚ) / 1094235123264

def SurrogateDiagonalTailChunk000Sub000Block002Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 173
    = surrogateDiagTailX0RatChunk000Sub000Block002Part023

theorem surrogateDiagonalTailChunk000Sub000Block002Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block002Part023CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block002Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block002Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block002Part023CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block002Part023SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block002Part023] using hcert

def TailChunk000Sub000Block002Part024SupportExplicit : Finset ℕ :=
  ([174] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block002Part024 : ℚ :=
  (17414159125 : ℚ) / 24591157248

def SurrogateDiagonalTailChunk000Sub000Block002Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 174
    = surrogateDiagTailX0RatChunk000Sub000Block002Part024

theorem surrogateDiagonalTailChunk000Sub000Block002Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block002Part024CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block002Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block002Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block002Part024CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block002Part024SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block002Part024] using hcert

def surrogateDiagonalTailChunk000Sub000Block002HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block002Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block002Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block002Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block002Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block002Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block002Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block002Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block002Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block002Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block002Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block002Head : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block002Part000
    + surrogateDiagTailX0RatChunk000Sub000Block002Part001
    + surrogateDiagTailX0RatChunk000Sub000Block002Part002
    + surrogateDiagTailX0RatChunk000Sub000Block002Part003
    + surrogateDiagTailX0RatChunk000Sub000Block002Part004
    + surrogateDiagTailX0RatChunk000Sub000Block002Part005
    + surrogateDiagTailX0RatChunk000Sub000Block002Part006
    + surrogateDiagTailX0RatChunk000Sub000Block002Part007
    + surrogateDiagTailX0RatChunk000Sub000Block002Part008
    + surrogateDiagTailX0RatChunk000Sub000Block002Part009

def surrogateDiagonalTailChunk000Sub000Block002MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block002Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block002Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block002Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block002Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block002Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block002Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block002Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block002Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block002Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block002Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block002Mid : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block002Part010
    + surrogateDiagTailX0RatChunk000Sub000Block002Part011
    + surrogateDiagTailX0RatChunk000Sub000Block002Part012
    + surrogateDiagTailX0RatChunk000Sub000Block002Part013
    + surrogateDiagTailX0RatChunk000Sub000Block002Part014
    + surrogateDiagTailX0RatChunk000Sub000Block002Part015
    + surrogateDiagTailX0RatChunk000Sub000Block002Part016
    + surrogateDiagTailX0RatChunk000Sub000Block002Part017
    + surrogateDiagTailX0RatChunk000Sub000Block002Part018
    + surrogateDiagTailX0RatChunk000Sub000Block002Part019

def surrogateDiagonalTailChunk000Sub000Block002TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block002Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block002Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block002Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block002Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block002Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block002Tail : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block002Part020
    + surrogateDiagTailX0RatChunk000Sub000Block002Part021
    + surrogateDiagTailX0RatChunk000Sub000Block002Part022
    + surrogateDiagTailX0RatChunk000Sub000Block002Part023
    + surrogateDiagTailX0RatChunk000Sub000Block002Part024

def surrogateDiagonalTailChunk000Sub000Block002Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub000Block002HeadSum X0
    + surrogateDiagonalTailChunk000Sub000Block002MidSum X0
    + surrogateDiagonalTailChunk000Sub000Block002TailSum X0

def surrogateDiagTailX0RatChunk000Sub000Block002 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block002Part000
    + surrogateDiagTailX0RatChunk000Sub000Block002Part001
    + surrogateDiagTailX0RatChunk000Sub000Block002Part002
    + surrogateDiagTailX0RatChunk000Sub000Block002Part003
    + surrogateDiagTailX0RatChunk000Sub000Block002Part004
    + surrogateDiagTailX0RatChunk000Sub000Block002Part005
    + surrogateDiagTailX0RatChunk000Sub000Block002Part006
    + surrogateDiagTailX0RatChunk000Sub000Block002Part007
    + surrogateDiagTailX0RatChunk000Sub000Block002Part008
    + surrogateDiagTailX0RatChunk000Sub000Block002Part009
    + surrogateDiagTailX0RatChunk000Sub000Block002Part010
    + surrogateDiagTailX0RatChunk000Sub000Block002Part011
    + surrogateDiagTailX0RatChunk000Sub000Block002Part012
    + surrogateDiagTailX0RatChunk000Sub000Block002Part013
    + surrogateDiagTailX0RatChunk000Sub000Block002Part014
    + surrogateDiagTailX0RatChunk000Sub000Block002Part015
    + surrogateDiagTailX0RatChunk000Sub000Block002Part016
    + surrogateDiagTailX0RatChunk000Sub000Block002Part017
    + surrogateDiagTailX0RatChunk000Sub000Block002Part018
    + surrogateDiagTailX0RatChunk000Sub000Block002Part019
    + surrogateDiagTailX0RatChunk000Sub000Block002Part020
    + surrogateDiagTailX0RatChunk000Sub000Block002Part021
    + surrogateDiagTailX0RatChunk000Sub000Block002Part022
    + surrogateDiagTailX0RatChunk000Sub000Block002Part023
    + surrogateDiagTailX0RatChunk000Sub000Block002Part024

theorem surrogateDiagTailX0RatChunk000Sub000Block002_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk000Sub000Block002Head + surrogateDiagTailX0RatChunk000Sub000Block002Mid + surrogateDiagTailX0RatChunk000Sub000Block002Tail =
      surrogateDiagTailX0RatChunk000Sub000Block002 := by
  unfold surrogateDiagTailX0RatChunk000Sub000Block002Head surrogateDiagTailX0RatChunk000Sub000Block002Mid surrogateDiagTailX0RatChunk000Sub000Block002Tail surrogateDiagTailX0RatChunk000Sub000Block002
  ring

def SurrogateDiagonalTailChunk000Sub000Block002HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block002HeadSum X0 = surrogateDiagTailX0RatChunk000Sub000Block002Head

def SurrogateDiagonalTailChunk000Sub000Block002MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block002MidSum X0 = surrogateDiagTailX0RatChunk000Sub000Block002Mid

def SurrogateDiagonalTailChunk000Sub000Block002TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block002TailSum X0 = surrogateDiagTailX0RatChunk000Sub000Block002Tail

theorem surrogateDiagonalTailChunk000Sub000Block002_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk000Sub000Block002HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk000Sub000Block002MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk000Sub000Block002TailCertificateAt X0) :
    surrogateDiagonalTailChunk000Sub000Block002Sum X0 = surrogateDiagTailX0RatChunk000Sub000Block002 := by
  unfold SurrogateDiagonalTailChunk000Sub000Block002HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk000Sub000Block002MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk000Sub000Block002TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk000Sub000Block002Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk000Sub000Block002_eq_head_add_mid_add_tail

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

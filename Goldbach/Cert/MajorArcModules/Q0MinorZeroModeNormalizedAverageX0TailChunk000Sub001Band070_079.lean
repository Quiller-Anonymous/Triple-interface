import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0TailPilot25

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

open scoped BigOperators

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

/- Generated direct-term certificate blocks for tail chunk 000, subchunk 001, blocks [70,80). -/

/-- Block 070 covers tail-support indices [6750,6775) and q from 11158 to 11198. -/

def TailChunk000Sub001Block070Part000SupportExplicit : Finset ℕ :=
  ([11158] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block070Part000 : ℚ :=
  (1625829977575 : ℚ) / 1301020474942015488

def SurrogateDiagonalTailChunk000Sub001Block070Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11158
    = surrogateDiagTailX0RatChunk000Sub001Block070Part000

theorem surrogateDiagonalTailChunk000Sub001Block070Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block070Part000CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block070Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block070Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block070Part000CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block070Part000SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block070Part000] using hcert

def TailChunk000Sub001Block070Part001SupportExplicit : Finset ℕ :=
  ([11159] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block070Part001 : ℚ :=
  (1945676265625 : ℚ) / 9689743834335426162

def SurrogateDiagonalTailChunk000Sub001Block070Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11159
    = surrogateDiagTailX0RatChunk000Sub001Block070Part001

theorem surrogateDiagonalTailChunk000Sub001Block070Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block070Part001CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block070Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block070Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block070Part001CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block070Part001SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block070Part001] using hcert

def TailChunk000Sub001Block070Part002SupportExplicit : Finset ℕ :=
  ([11161] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block070Part002 : ℚ :=
  (3114198025 : ℚ) / 15514708800655872

def SurrogateDiagonalTailChunk000Sub001Block070Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11161
    = surrogateDiagTailX0RatChunk000Sub001Block070Part002

theorem surrogateDiagonalTailChunk000Sub001Block070Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block070Part002CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block070Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block070Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block070Part002CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block070Part002SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block070Part002] using hcert

def TailChunk000Sub001Block070Part003SupportExplicit : Finset ℕ :=
  ([11162] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block070Part003 : ℚ :=
  (778689025 : ℚ) / 969669300040992

def SurrogateDiagonalTailChunk000Sub001Block070Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11162
    = surrogateDiagTailX0RatChunk000Sub001Block070Part003

theorem surrogateDiagonalTailChunk000Sub001Block070Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block070Part003CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block070Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block070Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block070Part003CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block070Part003SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block070Part003] using hcert

def TailChunk000Sub001Block070Part004SupportExplicit : Finset ℕ :=
  ([11165] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block070Part004 : ℚ :=
  (1611667021 : ℚ) / 2266321051975680

def SurrogateDiagonalTailChunk000Sub001Block070Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11165
    = surrogateDiagTailX0RatChunk000Sub001Block070Part004

theorem surrogateDiagonalTailChunk000Sub001Block070Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block070Part004CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block070Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block070Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block070Part004CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block070Part004SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block070Part004] using hcert

def TailChunk000Sub001Block070Part005SupportExplicit : Finset ℕ :=
  ([11166] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block070Part005 : ℚ :=
  (1730633 : ℚ) / 638337715200

def SurrogateDiagonalTailChunk000Sub001Block070Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11166
    = surrogateDiagTailX0RatChunk000Sub001Block070Part005

theorem surrogateDiagonalTailChunk000Sub001Block070Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block070Part005CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block070Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block070Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block070Part005CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block070Part005SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block070Part005] using hcert

def TailChunk000Sub001Block070Part006SupportExplicit : Finset ℕ :=
  ([11167] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block070Part006 : ℚ :=
  (3407017142225 : ℚ) / 14049827716166820864

def SurrogateDiagonalTailChunk000Sub001Block070Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11167
    = surrogateDiagTailX0RatChunk000Sub001Block070Part006

theorem surrogateDiagonalTailChunk000Sub001Block070Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block070Part006CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block070Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block070Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block070Part006CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block070Part006SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block070Part006] using hcert

def TailChunk000Sub001Block070Part007SupportExplicit : Finset ℕ :=
  ([11170] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block070Part007 : ℚ :=
  (779190681875 : ℚ) / 496470681620987904

def SurrogateDiagonalTailChunk000Sub001Block070Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11170
    = surrogateDiagTailX0RatChunk000Sub001Block070Part007

theorem surrogateDiagonalTailChunk000Sub001Block070Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block070Part007CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block070Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block070Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block070Part007CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block070Part007SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block070Part007] using hcert

def TailChunk000Sub001Block070Part008SupportExplicit : Finset ℕ :=
  ([11171] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block070Part008 : ℚ :=
  (3119781025 : ℚ) / 15570391862891442

def SurrogateDiagonalTailChunk000Sub001Block070Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11171
    = surrogateDiagTailX0RatChunk000Sub001Block070Part008

theorem surrogateDiagonalTailChunk000Sub001Block070Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block070Part008CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block070Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block070Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block070Part008CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block070Part008SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block070Part008] using hcert

def TailChunk000Sub001Block070Part009SupportExplicit : Finset ℕ :=
  ([11173] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block070Part009 : ℚ :=
  (1950561390625 : ℚ) / 9738466523172025632

def SurrogateDiagonalTailChunk000Sub001Block070Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11173
    = surrogateDiagTailX0RatChunk000Sub001Block070Part009

theorem surrogateDiagonalTailChunk000Sub001Block070Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block070Part009CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block070Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block070Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block070Part009CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block070Part009SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block070Part009] using hcert

def TailChunk000Sub001Block070Part010SupportExplicit : Finset ℕ :=
  ([11174] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block070Part010 : ℚ :=
  (75161088199 : ℚ) / 85047566112000000

def SurrogateDiagonalTailChunk000Sub001Block070Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11174
    = surrogateDiagTailX0RatChunk000Sub001Block070Part010

theorem surrogateDiagonalTailChunk000Sub001Block070Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block070Part010CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block070Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block070Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block070Part010CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block070Part010SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block070Part010] using hcert

def TailChunk000Sub001Block070Part011SupportExplicit : Finset ℕ :=
  ([11177] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block070Part011 : ℚ :=
  (1951958265625 : ℚ) / 9752420977712067072

def SurrogateDiagonalTailChunk000Sub001Block070Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11177
    = surrogateDiagTailX0RatChunk000Sub001Block070Part011

theorem surrogateDiagonalTailChunk000Sub001Block070Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block070Part011CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block070Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block070Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block070Part011CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block070Part011SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block070Part011] using hcert

def TailChunk000Sub001Block070Part012SupportExplicit : Finset ℕ :=
  ([11179] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block070Part012 : ℚ :=
  (216150350125 : ℚ) / 750940240020880896

def SurrogateDiagonalTailChunk000Sub001Block070Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11179
    = surrogateDiagTailX0RatChunk000Sub001Block070Part012

theorem surrogateDiagonalTailChunk000Sub001Block070Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block070Part012CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block070Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block070Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block070Part012CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block070Part012SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block070Part012] using hcert

def TailChunk000Sub001Block070Part013SupportExplicit : Finset ℕ :=
  ([11181] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block070Part013 : ℚ :=
  (3471393627325 : ℚ) / 7711133887264814208

def SurrogateDiagonalTailChunk000Sub001Block070Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11181
    = surrogateDiagTailX0RatChunk000Sub001Block070Part013

theorem surrogateDiagonalTailChunk000Sub001Block070Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block070Part013CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block070Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block070Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block070Part013CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block070Part013SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block070Part013] using hcert

def TailChunk000Sub001Block070Part014SupportExplicit : Finset ℕ :=
  ([11182] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block070Part014 : ℚ :=
  (781482025 : ℚ) / 976639042360722

def SurrogateDiagonalTailChunk000Sub001Block070Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11182
    = surrogateDiagTailX0RatChunk000Sub001Block070Part014

theorem surrogateDiagonalTailChunk000Sub001Block070Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block070Part014CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block070Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block070Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block070Part014CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block070Part014SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block070Part014] using hcert

def TailChunk000Sub001Block070Part015SupportExplicit : Finset ℕ :=
  ([11183] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block070Part015 : ℚ :=
  (301341143767 : ℚ) / 1422254785374259200

def SurrogateDiagonalTailChunk000Sub001Block070Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11183
    = surrogateDiagTailX0RatChunk000Sub001Block070Part015

theorem surrogateDiagonalTailChunk000Sub001Block070Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block070Part015CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block070Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block070Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block070Part015CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block070Part015SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block070Part015] using hcert

def TailChunk000Sub001Block070Part016SupportExplicit : Finset ℕ :=
  ([11185] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block070Part016 : ℚ :=
  (5313927324775 : ℚ) / 16001254070038069248

def SurrogateDiagonalTailChunk000Sub001Block070Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11185
    = surrogateDiagTailX0RatChunk000Sub001Block070Part016

theorem surrogateDiagonalTailChunk000Sub001Block070Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block070Part016CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block070Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block070Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block070Part016CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block070Part016SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block070Part016] using hcert

def TailChunk000Sub001Block070Part017SupportExplicit : Finset ℕ :=
  ([11186] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block070Part017 : ℚ :=
  (1529432426125 : ℚ) / 950918108380397568

def SurrogateDiagonalTailChunk000Sub001Block070Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11186
    = surrogateDiagTailX0RatChunk000Sub001Block070Part017

theorem surrogateDiagonalTailChunk000Sub001Block070Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block070Part017CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block070Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block070Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block070Part017CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block070Part017SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block070Part017] using hcert

def TailChunk000Sub001Block070Part018SupportExplicit : Finset ℕ :=
  ([11189] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block070Part018 : ℚ :=
  (7571811188275 : ℚ) / 36027568552026066048

def SurrogateDiagonalTailChunk000Sub001Block070Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11189
    = surrogateDiagTailX0RatChunk000Sub001Block070Part018

theorem surrogateDiagonalTailChunk000Sub001Block070Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block070Part018CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block070Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block070Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block070Part018CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block070Part018SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block070Part018] using hcert

def TailChunk000Sub001Block070Part019SupportExplicit : Finset ℕ :=
  ([11190] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block070Part019 : ℚ :=
  (893503422625 : ℚ) / 196136565578661888

def SurrogateDiagonalTailChunk000Sub001Block070Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11190
    = surrogateDiagTailX0RatChunk000Sub001Block070Part019

theorem surrogateDiagonalTailChunk000Sub001Block070Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block070Part019CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block070Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block070Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block070Part019CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block070Part019SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block070Part019] using hcert

def TailChunk000Sub001Block070Part020SupportExplicit : Finset ℕ :=
  ([11193] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block070Part020 : ℚ :=
  (24491616349 : ℚ) / 27524332309708800

def SurrogateDiagonalTailChunk000Sub001Block070Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11193
    = surrogateDiagTailX0RatChunk000Sub001Block070Part020

theorem surrogateDiagonalTailChunk000Sub001Block070Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block070Part020CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block070Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block070Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block070Part020CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block070Part020SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block070Part020] using hcert

def TailChunk000Sub001Block070Part021SupportExplicit : Finset ℕ :=
  ([11194] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block070Part021 : ℚ :=
  (133784670875 : ℚ) / 149188677250056192

def SurrogateDiagonalTailChunk000Sub001Block070Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11194
    = surrogateDiagTailX0RatChunk000Sub001Block070Part021

theorem surrogateDiagonalTailChunk000Sub001Block070Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block070Part021CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block070Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block070Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block070Part021CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block070Part021SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block070Part021] using hcert

def TailChunk000Sub001Block070Part022SupportExplicit : Finset ℕ :=
  ([11195] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block070Part022 : ℚ :=
  (5323435469725 : ℚ) / 16058580493875038208

def SurrogateDiagonalTailChunk000Sub001Block070Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11195
    = surrogateDiagTailX0RatChunk000Sub001Block070Part022

theorem surrogateDiagonalTailChunk000Sub001Block070Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block070Part022CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block070Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block070Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block070Part022CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block070Part022SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block070Part022] using hcert

def TailChunk000Sub001Block070Part023SupportExplicit : Finset ℕ :=
  ([11197] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block070Part023 : ℚ :=
  (1958950140625 : ℚ) / 9822418335457081632

def SurrogateDiagonalTailChunk000Sub001Block070Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11197
    = surrogateDiagTailX0RatChunk000Sub001Block070Part023

theorem surrogateDiagonalTailChunk000Sub001Block070Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block070Part023CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block070Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block070Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block070Part023CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block070Part023SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block070Part023] using hcert

def TailChunk000Sub001Block070Part024SupportExplicit : Finset ℕ :=
  ([11198] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block070Part024 : ℚ :=
  (17615311111 : ℚ) / 16652586875404800

def SurrogateDiagonalTailChunk000Sub001Block070Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11198
    = surrogateDiagTailX0RatChunk000Sub001Block070Part024

theorem surrogateDiagonalTailChunk000Sub001Block070Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block070Part024CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block070Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block070Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block070Part024CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block070Part024SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block070Part024] using hcert

def surrogateDiagonalTailChunk000Sub001Block070HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block070Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block070Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block070Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block070Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block070Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block070Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block070Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block070Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block070Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block070Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block070Head : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block070Part000
    + surrogateDiagTailX0RatChunk000Sub001Block070Part001
    + surrogateDiagTailX0RatChunk000Sub001Block070Part002
    + surrogateDiagTailX0RatChunk000Sub001Block070Part003
    + surrogateDiagTailX0RatChunk000Sub001Block070Part004
    + surrogateDiagTailX0RatChunk000Sub001Block070Part005
    + surrogateDiagTailX0RatChunk000Sub001Block070Part006
    + surrogateDiagTailX0RatChunk000Sub001Block070Part007
    + surrogateDiagTailX0RatChunk000Sub001Block070Part008
    + surrogateDiagTailX0RatChunk000Sub001Block070Part009

def surrogateDiagonalTailChunk000Sub001Block070MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block070Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block070Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block070Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block070Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block070Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block070Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block070Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block070Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block070Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block070Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block070Mid : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block070Part010
    + surrogateDiagTailX0RatChunk000Sub001Block070Part011
    + surrogateDiagTailX0RatChunk000Sub001Block070Part012
    + surrogateDiagTailX0RatChunk000Sub001Block070Part013
    + surrogateDiagTailX0RatChunk000Sub001Block070Part014
    + surrogateDiagTailX0RatChunk000Sub001Block070Part015
    + surrogateDiagTailX0RatChunk000Sub001Block070Part016
    + surrogateDiagTailX0RatChunk000Sub001Block070Part017
    + surrogateDiagTailX0RatChunk000Sub001Block070Part018
    + surrogateDiagTailX0RatChunk000Sub001Block070Part019

def surrogateDiagonalTailChunk000Sub001Block070TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block070Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block070Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block070Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block070Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block070Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block070Tail : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block070Part020
    + surrogateDiagTailX0RatChunk000Sub001Block070Part021
    + surrogateDiagTailX0RatChunk000Sub001Block070Part022
    + surrogateDiagTailX0RatChunk000Sub001Block070Part023
    + surrogateDiagTailX0RatChunk000Sub001Block070Part024

def surrogateDiagonalTailChunk000Sub001Block070Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub001Block070HeadSum X0
    + surrogateDiagonalTailChunk000Sub001Block070MidSum X0
    + surrogateDiagonalTailChunk000Sub001Block070TailSum X0

def surrogateDiagTailX0RatChunk000Sub001Block070 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block070Part000
    + surrogateDiagTailX0RatChunk000Sub001Block070Part001
    + surrogateDiagTailX0RatChunk000Sub001Block070Part002
    + surrogateDiagTailX0RatChunk000Sub001Block070Part003
    + surrogateDiagTailX0RatChunk000Sub001Block070Part004
    + surrogateDiagTailX0RatChunk000Sub001Block070Part005
    + surrogateDiagTailX0RatChunk000Sub001Block070Part006
    + surrogateDiagTailX0RatChunk000Sub001Block070Part007
    + surrogateDiagTailX0RatChunk000Sub001Block070Part008
    + surrogateDiagTailX0RatChunk000Sub001Block070Part009
    + surrogateDiagTailX0RatChunk000Sub001Block070Part010
    + surrogateDiagTailX0RatChunk000Sub001Block070Part011
    + surrogateDiagTailX0RatChunk000Sub001Block070Part012
    + surrogateDiagTailX0RatChunk000Sub001Block070Part013
    + surrogateDiagTailX0RatChunk000Sub001Block070Part014
    + surrogateDiagTailX0RatChunk000Sub001Block070Part015
    + surrogateDiagTailX0RatChunk000Sub001Block070Part016
    + surrogateDiagTailX0RatChunk000Sub001Block070Part017
    + surrogateDiagTailX0RatChunk000Sub001Block070Part018
    + surrogateDiagTailX0RatChunk000Sub001Block070Part019
    + surrogateDiagTailX0RatChunk000Sub001Block070Part020
    + surrogateDiagTailX0RatChunk000Sub001Block070Part021
    + surrogateDiagTailX0RatChunk000Sub001Block070Part022
    + surrogateDiagTailX0RatChunk000Sub001Block070Part023
    + surrogateDiagTailX0RatChunk000Sub001Block070Part024

theorem surrogateDiagTailX0RatChunk000Sub001Block070_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk000Sub001Block070Head + surrogateDiagTailX0RatChunk000Sub001Block070Mid + surrogateDiagTailX0RatChunk000Sub001Block070Tail =
      surrogateDiagTailX0RatChunk000Sub001Block070 := by
  unfold surrogateDiagTailX0RatChunk000Sub001Block070Head surrogateDiagTailX0RatChunk000Sub001Block070Mid surrogateDiagTailX0RatChunk000Sub001Block070Tail surrogateDiagTailX0RatChunk000Sub001Block070
  ring

def SurrogateDiagonalTailChunk000Sub001Block070HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block070HeadSum X0 = surrogateDiagTailX0RatChunk000Sub001Block070Head

def SurrogateDiagonalTailChunk000Sub001Block070MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block070MidSum X0 = surrogateDiagTailX0RatChunk000Sub001Block070Mid

def SurrogateDiagonalTailChunk000Sub001Block070TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block070TailSum X0 = surrogateDiagTailX0RatChunk000Sub001Block070Tail

theorem surrogateDiagonalTailChunk000Sub001Block070_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk000Sub001Block070HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk000Sub001Block070MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk000Sub001Block070TailCertificateAt X0) :
    surrogateDiagonalTailChunk000Sub001Block070Sum X0 = surrogateDiagTailX0RatChunk000Sub001Block070 := by
  unfold SurrogateDiagonalTailChunk000Sub001Block070HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk000Sub001Block070MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk000Sub001Block070TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk000Sub001Block070Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk000Sub001Block070_eq_head_add_mid_add_tail

/-- Block 071 covers tail-support indices [6775,6800) and q from 11199 to 11238. -/

def TailChunk000Sub001Block071Part000SupportExplicit : Finset ℕ :=
  ([11199] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block071Part000 : ℚ :=
  (2176883117675 : ℚ) / 3880461564625019904

def SurrogateDiagonalTailChunk000Sub001Block071Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11199
    = surrogateDiagTailX0RatChunk000Sub001Block071Part000

theorem surrogateDiagonalTailChunk000Sub001Block071Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block071Part000CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block071Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block071Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block071Part000CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block071Part000SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block071Part000] using hcert

def TailChunk000Sub001Block071Part001SupportExplicit : Finset ℕ :=
  ([11201] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block071Part001 : ℚ :=
  (7285576008325 : ℚ) / 32678541066959365248

def SurrogateDiagonalTailChunk000Sub001Block071Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11201
    = surrogateDiagTailX0RatChunk000Sub001Block071Part001

theorem surrogateDiagonalTailChunk000Sub001Block071Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block071Part001CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block071Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block071Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block071Part001CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block071Part001SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block071Part001] using hcert

def TailChunk000Sub001Block071Part002SupportExplicit : Finset ℕ :=
  ([11202] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block071Part002 : ℚ :=
  (43545275 : ℚ) / 16165356781248

def SurrogateDiagonalTailChunk000Sub001Block071Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11202
    = surrogateDiagTailX0RatChunk000Sub001Block071Part002

theorem surrogateDiagonalTailChunk000Sub001Block071Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block071Part002CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block071Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block071Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block071Part002CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block071Part002SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block071Part002] using hcert

def TailChunk000Sub001Block071Part003SupportExplicit : Finset ℕ :=
  ([11203] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block071Part003 : ℚ :=
  (169590755025 : ℚ) / 731410302726569984

def SurrogateDiagonalTailChunk000Sub001Block071Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11203
    = surrogateDiagTailX0RatChunk000Sub001Block071Part003

theorem surrogateDiagonalTailChunk000Sub001Block071Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block071Part003CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block071Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block071Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block071Part003CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block071Part003SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block071Part003] using hcert

def TailChunk000Sub001Block071Part004SupportExplicit : Finset ℕ :=
  ([11206] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block071Part004 : ℚ :=
  (23783384723 : ℚ) / 23635478662502400

def SurrogateDiagonalTailChunk000Sub001Block071Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11206
    = surrogateDiagTailX0RatChunk000Sub001Block071Part004

theorem surrogateDiagonalTailChunk000Sub001Block071Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block071Part004CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block071Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block071Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block071Part004CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block071Part004SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block071Part004] using hcert

def TailChunk000Sub001Block071Part005SupportExplicit : Finset ℕ :=
  ([11207] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block071Part005 : ℚ :=
  (60825753163 : ℚ) / 212379107328000000

def SurrogateDiagonalTailChunk000Sub001Block071Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11207
    = surrogateDiagTailX0RatChunk000Sub001Block071Part005

theorem surrogateDiagonalTailChunk000Sub001Block071Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block071Part005CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block071Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block071Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block071Part005CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block071Part005SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block071Part005] using hcert

def TailChunk000Sub001Block071Part006SupportExplicit : Finset ℕ :=
  ([11209] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block071Part006 : ℚ :=
  (269604342769 : ℚ) / 1074182226462595200

def SurrogateDiagonalTailChunk000Sub001Block071Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11209
    = surrogateDiagTailX0RatChunk000Sub001Block071Part006

theorem surrogateDiagonalTailChunk000Sub001Block071Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block071Part006CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block071Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block071Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block071Part006CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block071Part006SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block071Part006] using hcert

def TailChunk000Sub001Block071Part007SupportExplicit : Finset ℕ :=
  ([11210] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block071Part007 : ℚ :=
  (230658379025 : ℚ) / 126741128127234048

def SurrogateDiagonalTailChunk000Sub001Block071Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11210
    = surrogateDiagTailX0RatChunk000Sub001Block071Part007

theorem surrogateDiagonalTailChunk000Sub001Block071Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block071Part007CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block071Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block071Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block071Part007CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block071Part007SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block071Part007] using hcert

def TailChunk000Sub001Block071Part008SupportExplicit : Finset ℕ :=
  ([11211] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block071Part008 : ℚ :=
  (18359220131 : ℚ) / 29865811968000000

def SurrogateDiagonalTailChunk000Sub001Block071Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11211
    = surrogateDiagTailX0RatChunk000Sub001Block071Part008

theorem surrogateDiagonalTailChunk000Sub001Block071Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block071Part008CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block071Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block071Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block071Part008CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block071Part008SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block071Part008] using hcert

def TailChunk000Sub001Block071Part009SupportExplicit : Finset ℕ :=
  ([11213] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block071Part009 : ℚ :=
  (1964552640625 : ℚ) / 9878686968322159392

def SurrogateDiagonalTailChunk000Sub001Block071Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11213
    = surrogateDiagTailX0RatChunk000Sub001Block071Part009

theorem surrogateDiagonalTailChunk000Sub001Block071Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block071Part009CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block071Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block071Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block071Part009CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block071Part009SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block071Part009] using hcert

def TailChunk000Sub001Block071Part010SupportExplicit : Finset ℕ :=
  ([11215] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block071Part010 : ℚ :=
  (1885671499275 : ℚ) / 5391231768581380096

def SurrogateDiagonalTailChunk000Sub001Block071Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11215
    = surrogateDiagTailX0RatChunk000Sub001Block071Part010

theorem surrogateDiagonalTailChunk000Sub001Block071Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block071Part010CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block071Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block071Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block071Part010CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block071Part010SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block071Part010] using hcert

def TailChunk000Sub001Block071Part011SupportExplicit : Finset ℕ :=
  ([11217] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block071Part011 : ℚ :=
  (545971840775 : ℚ) / 976369136534030736

def SurrogateDiagonalTailChunk000Sub001Block071Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11217
    = surrogateDiagTailX0RatChunk000Sub001Block071Part011

theorem surrogateDiagonalTailChunk000Sub001Block071Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block071Part011CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block071Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block071Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block071Part011CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block071Part011SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block071Part011] using hcert

def TailChunk000Sub001Block071Part012SupportExplicit : Finset ℕ :=
  ([11218] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block071Part012 : ℚ :=
  (706893413 : ℚ) / 823064111906400

def SurrogateDiagonalTailChunk000Sub001Block071Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11218
    = surrogateDiagTailX0RatChunk000Sub001Block071Part012

theorem surrogateDiagonalTailChunk000Sub001Block071Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block071Part012CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block071Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block071Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block071Part012CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block071Part012SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block071Part012] using hcert

def TailChunk000Sub001Block071Part013SupportExplicit : Finset ℕ :=
  ([11219] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block071Part013 : ℚ :=
  (6924270538675 : ℚ) / 28627334088875624448

def SurrogateDiagonalTailChunk000Sub001Block071Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11219
    = surrogateDiagTailX0RatChunk000Sub001Block071Part013

theorem surrogateDiagonalTailChunk000Sub001Block071Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block071Part013CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block071Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block071Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block071Part013CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block071Part013SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block071Part013] using hcert

def TailChunk000Sub001Block071Part014SupportExplicit : Finset ℕ :=
  ([11222] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block071Part014 : ℚ :=
  (37736985701 : ℚ) / 42523783056000000

def SurrogateDiagonalTailChunk000Sub001Block071Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11222
    = surrogateDiagTailX0RatChunk000Sub001Block071Part014

theorem surrogateDiagonalTailChunk000Sub001Block071Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block071Part014CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block071Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block071Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block071Part014CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block071Part014SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block071Part014] using hcert

def TailChunk000Sub001Block071Part015SupportExplicit : Finset ℕ :=
  ([11226] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block071Part015 : ℚ :=
  (8753000309 : ℚ) / 9784604217537600

def SurrogateDiagonalTailChunk000Sub001Block071Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11226
    = surrogateDiagTailX0RatChunk000Sub001Block071Part015

theorem surrogateDiagonalTailChunk000Sub001Block071Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block071Part015CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block071Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block071Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block071Part015CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block071Part015SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block071Part015] using hcert

def TailChunk000Sub001Block071Part016SupportExplicit : Finset ℕ :=
  ([11227] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block071Part016 : ℚ :=
  (64758549925 : ℚ) / 36823288275741984768

def SurrogateDiagonalTailChunk000Sub001Block071Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11227
    = surrogateDiagTailX0RatChunk000Sub001Block071Part016

theorem surrogateDiagonalTailChunk000Sub001Block071Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block071Part016CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block071Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block071Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block071Part016CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block071Part016SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block071Part016] using hcert

def TailChunk000Sub001Block071Part017SupportExplicit : Finset ℕ :=
  ([11229] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block071Part017 : ℚ :=
  (904434704725 : ℚ) / 6198136657161781248

def SurrogateDiagonalTailChunk000Sub001Block071Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11229
    = surrogateDiagTailX0RatChunk000Sub001Block071Part017

theorem surrogateDiagonalTailChunk000Sub001Block071Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block071Part017CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block071Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block071Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block071Part017CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block071Part017SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block071Part017] using hcert

def TailChunk000Sub001Block071Part018SupportExplicit : Finset ℕ :=
  ([11230] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block071Part018 : ℚ :=
  (157891134575 : ℚ) / 507233882637149184

def SurrogateDiagonalTailChunk000Sub001Block071Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11230
    = surrogateDiagTailX0RatChunk000Sub001Block071Part018

theorem surrogateDiagonalTailChunk000Sub001Block071Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block071Part018CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block071Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block071Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block071Part018CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block071Part018SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block071Part018] using hcert

def TailChunk000Sub001Block071Part019SupportExplicit : Finset ℕ :=
  ([11231] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block071Part019 : ℚ :=
  (12862429 : ℚ) / 1061420241600000

def SurrogateDiagonalTailChunk000Sub001Block071Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11231
    = surrogateDiagTailX0RatChunk000Sub001Block071Part019

theorem surrogateDiagonalTailChunk000Sub001Block071Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block071Part019CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block071Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block071Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block071Part019CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block071Part019SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block071Part019] using hcert

def TailChunk000Sub001Block071Part020SupportExplicit : Finset ℕ :=
  ([11233] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block071Part020 : ℚ :=
  (4041041625 : ℚ) / 1710593112660062848

def SurrogateDiagonalTailChunk000Sub001Block071Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11233
    = surrogateDiagTailX0RatChunk000Sub001Block071Part020

theorem surrogateDiagonalTailChunk000Sub001Block071Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block071Part020CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block071Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block071Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block071Part020CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block071Part020SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block071Part020] using hcert

def TailChunk000Sub001Block071Part021SupportExplicit : Finset ℕ :=
  ([11234] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block071Part021 : ℚ :=
  (732858249 : ℚ) / 29198543906406400

def SurrogateDiagonalTailChunk000Sub001Block071Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11234
    = surrogateDiagTailX0RatChunk000Sub001Block071Part021

theorem surrogateDiagonalTailChunk000Sub001Block071Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block071Part021CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block071Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block071Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block071Part021CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block071Part021SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block071Part021] using hcert

def TailChunk000Sub001Block071Part022SupportExplicit : Finset ℕ :=
  ([11235] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block071Part022 : ℚ :=
  (4442442325 : ℚ) / 7758209773928448

def SurrogateDiagonalTailChunk000Sub001Block071Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11235
    = surrogateDiagTailX0RatChunk000Sub001Block071Part022

theorem surrogateDiagonalTailChunk000Sub001Block071Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block071Part022CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block071Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block071Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block071Part022CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block071Part022SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block071Part022] using hcert

def TailChunk000Sub001Block071Part023SupportExplicit : Finset ℕ :=
  ([11237] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block071Part023 : ℚ :=
  (3906891947 : ℚ) / 621888502077849600

def SurrogateDiagonalTailChunk000Sub001Block071Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11237
    = surrogateDiagTailX0RatChunk000Sub001Block071Part023

theorem surrogateDiagonalTailChunk000Sub001Block071Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block071Part023CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block071Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block071Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block071Part023CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block071Part023SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block071Part023] using hcert

def TailChunk000Sub001Block071Part024SupportExplicit : Finset ℕ :=
  ([11238] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block071Part024 : ℚ :=
  (43825625 : ℚ) / 16374276292608

def SurrogateDiagonalTailChunk000Sub001Block071Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11238
    = surrogateDiagTailX0RatChunk000Sub001Block071Part024

theorem surrogateDiagonalTailChunk000Sub001Block071Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block071Part024CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block071Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block071Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block071Part024CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block071Part024SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block071Part024] using hcert

def surrogateDiagonalTailChunk000Sub001Block071HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block071Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block071Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block071Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block071Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block071Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block071Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block071Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block071Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block071Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block071Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block071Head : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block071Part000
    + surrogateDiagTailX0RatChunk000Sub001Block071Part001
    + surrogateDiagTailX0RatChunk000Sub001Block071Part002
    + surrogateDiagTailX0RatChunk000Sub001Block071Part003
    + surrogateDiagTailX0RatChunk000Sub001Block071Part004
    + surrogateDiagTailX0RatChunk000Sub001Block071Part005
    + surrogateDiagTailX0RatChunk000Sub001Block071Part006
    + surrogateDiagTailX0RatChunk000Sub001Block071Part007
    + surrogateDiagTailX0RatChunk000Sub001Block071Part008
    + surrogateDiagTailX0RatChunk000Sub001Block071Part009

def surrogateDiagonalTailChunk000Sub001Block071MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block071Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block071Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block071Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block071Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block071Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block071Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block071Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block071Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block071Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block071Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block071Mid : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block071Part010
    + surrogateDiagTailX0RatChunk000Sub001Block071Part011
    + surrogateDiagTailX0RatChunk000Sub001Block071Part012
    + surrogateDiagTailX0RatChunk000Sub001Block071Part013
    + surrogateDiagTailX0RatChunk000Sub001Block071Part014
    + surrogateDiagTailX0RatChunk000Sub001Block071Part015
    + surrogateDiagTailX0RatChunk000Sub001Block071Part016
    + surrogateDiagTailX0RatChunk000Sub001Block071Part017
    + surrogateDiagTailX0RatChunk000Sub001Block071Part018
    + surrogateDiagTailX0RatChunk000Sub001Block071Part019

def surrogateDiagonalTailChunk000Sub001Block071TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block071Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block071Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block071Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block071Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block071Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block071Tail : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block071Part020
    + surrogateDiagTailX0RatChunk000Sub001Block071Part021
    + surrogateDiagTailX0RatChunk000Sub001Block071Part022
    + surrogateDiagTailX0RatChunk000Sub001Block071Part023
    + surrogateDiagTailX0RatChunk000Sub001Block071Part024

def surrogateDiagonalTailChunk000Sub001Block071Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub001Block071HeadSum X0
    + surrogateDiagonalTailChunk000Sub001Block071MidSum X0
    + surrogateDiagonalTailChunk000Sub001Block071TailSum X0

def surrogateDiagTailX0RatChunk000Sub001Block071 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block071Part000
    + surrogateDiagTailX0RatChunk000Sub001Block071Part001
    + surrogateDiagTailX0RatChunk000Sub001Block071Part002
    + surrogateDiagTailX0RatChunk000Sub001Block071Part003
    + surrogateDiagTailX0RatChunk000Sub001Block071Part004
    + surrogateDiagTailX0RatChunk000Sub001Block071Part005
    + surrogateDiagTailX0RatChunk000Sub001Block071Part006
    + surrogateDiagTailX0RatChunk000Sub001Block071Part007
    + surrogateDiagTailX0RatChunk000Sub001Block071Part008
    + surrogateDiagTailX0RatChunk000Sub001Block071Part009
    + surrogateDiagTailX0RatChunk000Sub001Block071Part010
    + surrogateDiagTailX0RatChunk000Sub001Block071Part011
    + surrogateDiagTailX0RatChunk000Sub001Block071Part012
    + surrogateDiagTailX0RatChunk000Sub001Block071Part013
    + surrogateDiagTailX0RatChunk000Sub001Block071Part014
    + surrogateDiagTailX0RatChunk000Sub001Block071Part015
    + surrogateDiagTailX0RatChunk000Sub001Block071Part016
    + surrogateDiagTailX0RatChunk000Sub001Block071Part017
    + surrogateDiagTailX0RatChunk000Sub001Block071Part018
    + surrogateDiagTailX0RatChunk000Sub001Block071Part019
    + surrogateDiagTailX0RatChunk000Sub001Block071Part020
    + surrogateDiagTailX0RatChunk000Sub001Block071Part021
    + surrogateDiagTailX0RatChunk000Sub001Block071Part022
    + surrogateDiagTailX0RatChunk000Sub001Block071Part023
    + surrogateDiagTailX0RatChunk000Sub001Block071Part024

theorem surrogateDiagTailX0RatChunk000Sub001Block071_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk000Sub001Block071Head + surrogateDiagTailX0RatChunk000Sub001Block071Mid + surrogateDiagTailX0RatChunk000Sub001Block071Tail =
      surrogateDiagTailX0RatChunk000Sub001Block071 := by
  unfold surrogateDiagTailX0RatChunk000Sub001Block071Head surrogateDiagTailX0RatChunk000Sub001Block071Mid surrogateDiagTailX0RatChunk000Sub001Block071Tail surrogateDiagTailX0RatChunk000Sub001Block071
  ring

def SurrogateDiagonalTailChunk000Sub001Block071HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block071HeadSum X0 = surrogateDiagTailX0RatChunk000Sub001Block071Head

def SurrogateDiagonalTailChunk000Sub001Block071MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block071MidSum X0 = surrogateDiagTailX0RatChunk000Sub001Block071Mid

def SurrogateDiagonalTailChunk000Sub001Block071TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block071TailSum X0 = surrogateDiagTailX0RatChunk000Sub001Block071Tail

theorem surrogateDiagonalTailChunk000Sub001Block071_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk000Sub001Block071HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk000Sub001Block071MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk000Sub001Block071TailCertificateAt X0) :
    surrogateDiagonalTailChunk000Sub001Block071Sum X0 = surrogateDiagTailX0RatChunk000Sub001Block071 := by
  unfold SurrogateDiagonalTailChunk000Sub001Block071HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk000Sub001Block071MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk000Sub001Block071TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk000Sub001Block071Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk000Sub001Block071_eq_head_add_mid_add_tail

/-- Block 072 covers tail-support indices [6800,6825) and q from 11239 to 11282. -/

def TailChunk000Sub001Block072Part000SupportExplicit : Finset ℕ :=
  ([11239] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block072Part000 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block072Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11239
    = surrogateDiagTailX0RatChunk000Sub001Block072Part000

theorem surrogateDiagonalTailChunk000Sub001Block072Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block072Part000CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block072Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block072Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block072Part000CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block072Part000SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block072Part000] using hcert

def TailChunk000Sub001Block072Part001SupportExplicit : Finset ℕ :=
  ([11242] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block072Part001 : ℚ :=
  (9795486403 : ℚ) / 5805913846579200

def SurrogateDiagonalTailChunk000Sub001Block072Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11242
    = surrogateDiagTailX0RatChunk000Sub001Block072Part001

theorem surrogateDiagonalTailChunk000Sub001Block072Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block072Part001CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block072Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block072Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block072Part001CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block072Part001SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block072Part001] using hcert

def TailChunk000Sub001Block072Part002SupportExplicit : Finset ℕ :=
  ([11243] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block072Part002 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block072Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11243
    = surrogateDiagTailX0RatChunk000Sub001Block072Part002

theorem surrogateDiagonalTailChunk000Sub001Block072Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block072Part002CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block072Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block072Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block072Part002CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block072Part002SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block072Part002] using hcert

def TailChunk000Sub001Block072Part003SupportExplicit : Finset ℕ :=
  ([11245] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block072Part003 : ℚ :=
  (736066905025 : ℚ) / 11617310472193179648

def SurrogateDiagonalTailChunk000Sub001Block072Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11245
    = surrogateDiagTailX0RatChunk000Sub001Block072Part003

theorem surrogateDiagonalTailChunk000Sub001Block072Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block072Part003CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block072Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block072Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block072Part003CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block072Part003SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block072Part003] using hcert

def TailChunk000Sub001Block072Part004SupportExplicit : Finset ℕ :=
  ([11246] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block072Part004 : ℚ :=
  (494033265625 : ℚ) / 624496822007933682

def SurrogateDiagonalTailChunk000Sub001Block072Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11246
    = surrogateDiagTailX0RatChunk000Sub001Block072Part004

theorem surrogateDiagonalTailChunk000Sub001Block072Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block072Part004CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block072Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block072Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block072Part004CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block072Part004SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block072Part004] using hcert

def TailChunk000Sub001Block072Part005SupportExplicit : Finset ℕ :=
  ([11247] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block072Part005 : ℚ :=
  (452990408525 : ℚ) / 3227510228835492864

def SurrogateDiagonalTailChunk000Sub001Block072Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11247
    = surrogateDiagTailX0RatChunk000Sub001Block072Part005

theorem surrogateDiagonalTailChunk000Sub001Block072Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block072Part005CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block072Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block072Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block072Part005CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block072Part005SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block072Part005] using hcert

def TailChunk000Sub001Block072Part006SupportExplicit : Finset ℕ :=
  ([11249] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block072Part006 : ℚ :=
  (26960440675 : ℚ) / 1197681990365653056

def SurrogateDiagonalTailChunk000Sub001Block072Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11249
    = surrogateDiagTailX0RatChunk000Sub001Block072Part006

theorem surrogateDiagonalTailChunk000Sub001Block072Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block072Part006CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block072Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block072Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block072Part006CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block072Part006SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block072Part006] using hcert

def TailChunk000Sub001Block072Part007SupportExplicit : Finset ℕ :=
  ([11251] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block072Part007 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block072Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11251
    = surrogateDiagTailX0RatChunk000Sub001Block072Part007

theorem surrogateDiagonalTailChunk000Sub001Block072Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block072Part007CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block072Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block072Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block072Part007CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block072Part007SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block072Part007] using hcert

def TailChunk000Sub001Block072Part008SupportExplicit : Finset ℕ :=
  ([11254] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block072Part008 : ℚ :=
  (36860636369 : ℚ) / 38868031379865600

def SurrogateDiagonalTailChunk000Sub001Block072Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11254
    = surrogateDiagTailX0RatChunk000Sub001Block072Part008

theorem surrogateDiagonalTailChunk000Sub001Block072Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block072Part008CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block072Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block072Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block072Part008CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block072Part008SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block072Part008] using hcert

def TailChunk000Sub001Block072Part009SupportExplicit : Finset ℕ :=
  ([11255] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block072Part009 : ℚ :=
  (8452485163 : ℚ) / 218743740000000000

def SurrogateDiagonalTailChunk000Sub001Block072Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11255
    = surrogateDiagTailX0RatChunk000Sub001Block072Part009

theorem surrogateDiagonalTailChunk000Sub001Block072Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block072Part009CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block072Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block072Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block072Part009CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block072Part009SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block072Part009] using hcert

def TailChunk000Sub001Block072Part010SupportExplicit : Finset ℕ :=
  ([11257] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block072Part010 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block072Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11257
    = surrogateDiagTailX0RatChunk000Sub001Block072Part010

theorem surrogateDiagonalTailChunk000Sub001Block072Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block072Part010CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block072Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block072Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block072Part010CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block072Part010SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block072Part010] using hcert

def TailChunk000Sub001Block072Part011SupportExplicit : Finset ℕ :=
  ([11258] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block072Part011 : ℚ :=
  (3728444125 : ℚ) / 3715784861810688

def SurrogateDiagonalTailChunk000Sub001Block072Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11258
    = surrogateDiagTailX0RatChunk000Sub001Block072Part011

theorem surrogateDiagonalTailChunk000Sub001Block072Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block072Part011CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block072Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block072Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block072Part011CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block072Part011SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block072Part011] using hcert

def TailChunk000Sub001Block072Part012SupportExplicit : Finset ℕ :=
  ([11261] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block072Part012 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block072Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11261
    = surrogateDiagTailX0RatChunk000Sub001Block072Part012

theorem surrogateDiagonalTailChunk000Sub001Block072Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block072Part012CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block072Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block072Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block072Part012CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block072Part012SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block072Part012] using hcert

def TailChunk000Sub001Block072Part013SupportExplicit : Finset ℕ :=
  ([11262] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block072Part013 : ℚ :=
  (2694675 : ℚ) / 1011102647296

def SurrogateDiagonalTailChunk000Sub001Block072Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11262
    = surrogateDiagTailX0RatChunk000Sub001Block072Part013

theorem surrogateDiagonalTailChunk000Sub001Block072Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block072Part013CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block072Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block072Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block072Part013CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block072Part013SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block072Part013] using hcert

def TailChunk000Sub001Block072Part014SupportExplicit : Finset ℕ :=
  ([11263] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block072Part014 : ℚ :=
  (9009124075 : ℚ) / 401219727153610752

def SurrogateDiagonalTailChunk000Sub001Block072Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11263
    = surrogateDiagTailX0RatChunk000Sub001Block072Part014

theorem surrogateDiagonalTailChunk000Sub001Block072Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block072Part014CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block072Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block072Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block072Part014CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block072Part014SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block072Part014] using hcert

def TailChunk000Sub001Block072Part015SupportExplicit : Finset ℕ :=
  ([11265] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block072Part015 : ℚ :=
  (14562883577 : ℚ) / 43208640000000000

def SurrogateDiagonalTailChunk000Sub001Block072Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11265
    = surrogateDiagTailX0RatChunk000Sub001Block072Part015

theorem surrogateDiagonalTailChunk000Sub001Block072Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block072Part015CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block072Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block072Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block072Part015CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block072Part015SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block072Part015] using hcert

def TailChunk000Sub001Block072Part016SupportExplicit : Finset ℕ :=
  ([11266] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block072Part016 : ℚ :=
  (76631055373 : ℚ) / 88890924085891200

def SurrogateDiagonalTailChunk000Sub001Block072Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11266
    = surrogateDiagTailX0RatChunk000Sub001Block072Part016

theorem surrogateDiagonalTailChunk000Sub001Block072Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block072Part016CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block072Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block072Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block072Part016CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block072Part016SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block072Part016] using hcert

def TailChunk000Sub001Block072Part017SupportExplicit : Finset ℕ :=
  ([11267] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block072Part017 : ℚ :=
  (60202900225 : ℚ) / 10746881284561698816

def SurrogateDiagonalTailChunk000Sub001Block072Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11267
    = surrogateDiagTailX0RatChunk000Sub001Block072Part017

theorem surrogateDiagonalTailChunk000Sub001Block072Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block072Part017CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block072Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block072Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block072Part017CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block072Part017SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block072Part017] using hcert

def TailChunk000Sub001Block072Part018SupportExplicit : Finset ℕ :=
  ([11269] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block072Part018 : ℚ :=
  (204119301 : ℚ) / 98338135375402880

def SurrogateDiagonalTailChunk000Sub001Block072Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11269
    = surrogateDiagTailX0RatChunk000Sub001Block072Part018

theorem surrogateDiagonalTailChunk000Sub001Block072Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block072Part018CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block072Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block072Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block072Part018CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block072Part018SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block072Part018] using hcert

def TailChunk000Sub001Block072Part019SupportExplicit : Finset ℕ :=
  ([11273] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block072Part019 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block072Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11273
    = surrogateDiagTailX0RatChunk000Sub001Block072Part019

theorem surrogateDiagonalTailChunk000Sub001Block072Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block072Part019CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block072Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block072Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block072Part019CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block072Part019SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block072Part019] using hcert

def TailChunk000Sub001Block072Part020SupportExplicit : Finset ℕ :=
  ([11274] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block072Part020 : ℚ :=
  (275738121175 : ℚ) / 124413985316058912

def SurrogateDiagonalTailChunk000Sub001Block072Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11274
    = surrogateDiagTailX0RatChunk000Sub001Block072Part020

theorem surrogateDiagonalTailChunk000Sub001Block072Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block072Part020CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block072Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block072Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block072Part020CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block072Part020SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block072Part020] using hcert

def TailChunk000Sub001Block072Part021SupportExplicit : Finset ℕ :=
  ([11278] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block072Part021 : ℚ :=
  (496848765625 : ℚ) / 631636405931992242

def SurrogateDiagonalTailChunk000Sub001Block072Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11278
    = surrogateDiagTailX0RatChunk000Sub001Block072Part021

theorem surrogateDiagonalTailChunk000Sub001Block072Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block072Part021CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block072Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block072Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block072Part021CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block072Part021SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block072Part021] using hcert

def TailChunk000Sub001Block072Part022SupportExplicit : Finset ℕ :=
  ([11279] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block072Part022 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block072Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11279
    = surrogateDiagTailX0RatChunk000Sub001Block072Part022

theorem surrogateDiagonalTailChunk000Sub001Block072Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block072Part022CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block072Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block072Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block072Part022CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block072Part022SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block072Part022] using hcert

def TailChunk000Sub001Block072Part023SupportExplicit : Finset ℕ :=
  ([11281] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block072Part023 : ℚ :=
  (16344273125 : ℚ) / 4354074940246757376

def SurrogateDiagonalTailChunk000Sub001Block072Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11281
    = surrogateDiagTailX0RatChunk000Sub001Block072Part023

theorem surrogateDiagonalTailChunk000Sub001Block072Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block072Part023CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block072Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block072Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block072Part023CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block072Part023SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block072Part023] using hcert

def TailChunk000Sub001Block072Part024SupportExplicit : Finset ℕ :=
  ([11282] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block072Part024 : ℚ :=
  (795522025 : ℚ) / 1012053022290432

def SurrogateDiagonalTailChunk000Sub001Block072Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11282
    = surrogateDiagTailX0RatChunk000Sub001Block072Part024

theorem surrogateDiagonalTailChunk000Sub001Block072Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block072Part024CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block072Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block072Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block072Part024CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block072Part024SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block072Part024] using hcert

def surrogateDiagonalTailChunk000Sub001Block072HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block072Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block072Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block072Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block072Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block072Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block072Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block072Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block072Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block072Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block072Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block072Head : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block072Part000
    + surrogateDiagTailX0RatChunk000Sub001Block072Part001
    + surrogateDiagTailX0RatChunk000Sub001Block072Part002
    + surrogateDiagTailX0RatChunk000Sub001Block072Part003
    + surrogateDiagTailX0RatChunk000Sub001Block072Part004
    + surrogateDiagTailX0RatChunk000Sub001Block072Part005
    + surrogateDiagTailX0RatChunk000Sub001Block072Part006
    + surrogateDiagTailX0RatChunk000Sub001Block072Part007
    + surrogateDiagTailX0RatChunk000Sub001Block072Part008
    + surrogateDiagTailX0RatChunk000Sub001Block072Part009

def surrogateDiagonalTailChunk000Sub001Block072MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block072Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block072Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block072Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block072Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block072Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block072Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block072Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block072Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block072Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block072Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block072Mid : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block072Part010
    + surrogateDiagTailX0RatChunk000Sub001Block072Part011
    + surrogateDiagTailX0RatChunk000Sub001Block072Part012
    + surrogateDiagTailX0RatChunk000Sub001Block072Part013
    + surrogateDiagTailX0RatChunk000Sub001Block072Part014
    + surrogateDiagTailX0RatChunk000Sub001Block072Part015
    + surrogateDiagTailX0RatChunk000Sub001Block072Part016
    + surrogateDiagTailX0RatChunk000Sub001Block072Part017
    + surrogateDiagTailX0RatChunk000Sub001Block072Part018
    + surrogateDiagTailX0RatChunk000Sub001Block072Part019

def surrogateDiagonalTailChunk000Sub001Block072TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block072Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block072Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block072Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block072Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block072Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block072Tail : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block072Part020
    + surrogateDiagTailX0RatChunk000Sub001Block072Part021
    + surrogateDiagTailX0RatChunk000Sub001Block072Part022
    + surrogateDiagTailX0RatChunk000Sub001Block072Part023
    + surrogateDiagTailX0RatChunk000Sub001Block072Part024

def surrogateDiagonalTailChunk000Sub001Block072Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub001Block072HeadSum X0
    + surrogateDiagonalTailChunk000Sub001Block072MidSum X0
    + surrogateDiagonalTailChunk000Sub001Block072TailSum X0

def surrogateDiagTailX0RatChunk000Sub001Block072 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block072Part000
    + surrogateDiagTailX0RatChunk000Sub001Block072Part001
    + surrogateDiagTailX0RatChunk000Sub001Block072Part002
    + surrogateDiagTailX0RatChunk000Sub001Block072Part003
    + surrogateDiagTailX0RatChunk000Sub001Block072Part004
    + surrogateDiagTailX0RatChunk000Sub001Block072Part005
    + surrogateDiagTailX0RatChunk000Sub001Block072Part006
    + surrogateDiagTailX0RatChunk000Sub001Block072Part007
    + surrogateDiagTailX0RatChunk000Sub001Block072Part008
    + surrogateDiagTailX0RatChunk000Sub001Block072Part009
    + surrogateDiagTailX0RatChunk000Sub001Block072Part010
    + surrogateDiagTailX0RatChunk000Sub001Block072Part011
    + surrogateDiagTailX0RatChunk000Sub001Block072Part012
    + surrogateDiagTailX0RatChunk000Sub001Block072Part013
    + surrogateDiagTailX0RatChunk000Sub001Block072Part014
    + surrogateDiagTailX0RatChunk000Sub001Block072Part015
    + surrogateDiagTailX0RatChunk000Sub001Block072Part016
    + surrogateDiagTailX0RatChunk000Sub001Block072Part017
    + surrogateDiagTailX0RatChunk000Sub001Block072Part018
    + surrogateDiagTailX0RatChunk000Sub001Block072Part019
    + surrogateDiagTailX0RatChunk000Sub001Block072Part020
    + surrogateDiagTailX0RatChunk000Sub001Block072Part021
    + surrogateDiagTailX0RatChunk000Sub001Block072Part022
    + surrogateDiagTailX0RatChunk000Sub001Block072Part023
    + surrogateDiagTailX0RatChunk000Sub001Block072Part024

theorem surrogateDiagTailX0RatChunk000Sub001Block072_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk000Sub001Block072Head + surrogateDiagTailX0RatChunk000Sub001Block072Mid + surrogateDiagTailX0RatChunk000Sub001Block072Tail =
      surrogateDiagTailX0RatChunk000Sub001Block072 := by
  unfold surrogateDiagTailX0RatChunk000Sub001Block072Head surrogateDiagTailX0RatChunk000Sub001Block072Mid surrogateDiagTailX0RatChunk000Sub001Block072Tail surrogateDiagTailX0RatChunk000Sub001Block072
  ring

def SurrogateDiagonalTailChunk000Sub001Block072HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block072HeadSum X0 = surrogateDiagTailX0RatChunk000Sub001Block072Head

def SurrogateDiagonalTailChunk000Sub001Block072MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block072MidSum X0 = surrogateDiagTailX0RatChunk000Sub001Block072Mid

def SurrogateDiagonalTailChunk000Sub001Block072TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block072TailSum X0 = surrogateDiagTailX0RatChunk000Sub001Block072Tail

theorem surrogateDiagonalTailChunk000Sub001Block072_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk000Sub001Block072HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk000Sub001Block072MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk000Sub001Block072TailCertificateAt X0) :
    surrogateDiagonalTailChunk000Sub001Block072Sum X0 = surrogateDiagTailX0RatChunk000Sub001Block072 := by
  unfold SurrogateDiagonalTailChunk000Sub001Block072HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk000Sub001Block072MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk000Sub001Block072TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk000Sub001Block072Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk000Sub001Block072_eq_head_add_mid_add_tail

/-- Block 073 covers tail-support indices [6825,6850) and q from 11283 to 11321. -/

def TailChunk000Sub001Block073Part000SupportExplicit : Finset ℕ :=
  ([11283] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block073Part000 : ℚ :=
  (35349426179 : ℚ) / 159929366485401600

def SurrogateDiagonalTailChunk000Sub001Block073Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11283
    = surrogateDiagTailX0RatChunk000Sub001Block073Part000

theorem surrogateDiagonalTailChunk000Sub001Block073Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block073Part000CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block073Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block073Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block073Part000CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block073Part000SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block073Part000] using hcert

def TailChunk000Sub001Block073Part001SupportExplicit : Finset ℕ :=
  ([11285] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block073Part001 : ℚ :=
  (2799498253 : ℚ) / 55736772927160320

def SurrogateDiagonalTailChunk000Sub001Block073Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11285
    = surrogateDiagTailX0RatChunk000Sub001Block073Part001

theorem surrogateDiagonalTailChunk000Sub001Block073Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block073Part001CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block073Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block073Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block073Part001CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block073Part001SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block073Part001] using hcert

def TailChunk000Sub001Block073Part002SupportExplicit : Finset ℕ :=
  ([11287] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block073Part002 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block073Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11287
    = surrogateDiagTailX0RatChunk000Sub001Block073Part002

theorem surrogateDiagonalTailChunk000Sub001Block073Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block073Part002CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block073Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block073Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block073Part002CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block073Part002SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block073Part002] using hcert

def TailChunk000Sub001Block073Part003SupportExplicit : Finset ℕ :=
  ([11289] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block073Part003 : ℚ :=
  (69213735583 : ℚ) / 280939216864051200

def SurrogateDiagonalTailChunk000Sub001Block073Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11289
    = surrogateDiagTailX0RatChunk000Sub001Block073Part003

theorem surrogateDiagonalTailChunk000Sub001Block073Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block073Part003CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block073Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block073Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block073Part003CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block073Part003SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block073Part003] using hcert

def TailChunk000Sub001Block073Part004SupportExplicit : Finset ℕ :=
  ([11290] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block073Part004 : ℚ :=
  (796024047875 : ℚ) / 518171147412701184

def SurrogateDiagonalTailChunk000Sub001Block073Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11290
    = surrogateDiagTailX0RatChunk000Sub001Block073Part004

theorem surrogateDiagonalTailChunk000Sub001Block073Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block073Part004CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block073Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block073Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block073Part004CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block073Part004SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block073Part004] using hcert

def TailChunk000Sub001Block073Part005SupportExplicit : Finset ℕ :=
  ([11291] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block073Part005 : ℚ :=
  (651120619525 : ℚ) / 21882251755828758528

def SurrogateDiagonalTailChunk000Sub001Block073Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11291
    = surrogateDiagTailX0RatChunk000Sub001Block073Part005

theorem surrogateDiagonalTailChunk000Sub001Block073Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block073Part005CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block073Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block073Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block073Part005CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block073Part005SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block073Part005] using hcert

def TailChunk000Sub001Block073Part006SupportExplicit : Finset ℕ :=
  ([11293] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block073Part006 : ℚ :=
  (895179343 : ℚ) / 192958472985801600

def SurrogateDiagonalTailChunk000Sub001Block073Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11293
    = surrogateDiagTailX0RatChunk000Sub001Block073Part006

theorem surrogateDiagonalTailChunk000Sub001Block073Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block073Part006CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block073Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block073Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block073Part006CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block073Part006SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block073Part006] using hcert

def TailChunk000Sub001Block073Part007SupportExplicit : Finset ℕ :=
  ([11294] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block073Part007 : ℚ :=
  (498259515625 : ℚ) / 635229067511830482

def SurrogateDiagonalTailChunk000Sub001Block073Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11294
    = surrogateDiagTailX0RatChunk000Sub001Block073Part007

theorem surrogateDiagonalTailChunk000Sub001Block073Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block073Part007CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block073Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block073Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block073Part007CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block073Part007SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block073Part007] using hcert

def TailChunk000Sub001Block073Part008SupportExplicit : Finset ℕ :=
  ([11297] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block073Part008 : ℚ :=
  (5589061381 : ℚ) / 191924427514060800

def SurrogateDiagonalTailChunk000Sub001Block073Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11297
    = surrogateDiagTailX0RatChunk000Sub001Block073Part008

theorem surrogateDiagonalTailChunk000Sub001Block073Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block073Part008CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block073Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block073Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block073Part008CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block073Part008SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block073Part008] using hcert

def TailChunk000Sub001Block073Part009SupportExplicit : Finset ℕ :=
  ([11298] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block073Part009 : ℚ :=
  (1112738036275 : ℚ) / 267479818102407168

def SurrogateDiagonalTailChunk000Sub001Block073Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11298
    = surrogateDiagTailX0RatChunk000Sub001Block073Part009

theorem surrogateDiagonalTailChunk000Sub001Block073Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block073Part009CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block073Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block073Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block073Part009CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block073Part009SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block073Part009] using hcert

def TailChunk000Sub001Block073Part010SupportExplicit : Finset ℕ :=
  ([11299] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block073Part010 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block073Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11299
    = surrogateDiagTailX0RatChunk000Sub001Block073Part010

theorem surrogateDiagonalTailChunk000Sub001Block073Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block073Part010CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block073Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block073Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block073Part010CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block073Part010SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block073Part010] using hcert

def TailChunk000Sub001Block073Part011SupportExplicit : Finset ℕ :=
  ([11301] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block073Part011 : ℚ :=
  (886557339725 : ℚ) / 4023815957381742144

def SurrogateDiagonalTailChunk000Sub001Block073Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11301
    = surrogateDiagTailX0RatChunk000Sub001Block073Part011

theorem surrogateDiagonalTailChunk000Sub001Block073Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block073Part011CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block073Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block073Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block073Part011CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block073Part011SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block073Part011] using hcert

def TailChunk000Sub001Block073Part012SupportExplicit : Finset ℕ :=
  ([11302] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block073Part012 : ℚ :=
  (31933801 : ℚ) / 40769992618050

def SurrogateDiagonalTailChunk000Sub001Block073Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11302
    = surrogateDiagTailX0RatChunk000Sub001Block073Part012

theorem surrogateDiagonalTailChunk000Sub001Block073Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block073Part012CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block073Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block073Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block073Part012CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block073Part012SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block073Part012] using hcert

def TailChunk000Sub001Block073Part013SupportExplicit : Finset ℕ :=
  ([11303] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block073Part013 : ℚ :=
  (3682777675 : ℚ) / 2099748225218789376

def SurrogateDiagonalTailChunk000Sub001Block073Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11303
    = surrogateDiagTailX0RatChunk000Sub001Block073Part013

theorem surrogateDiagonalTailChunk000Sub001Block073Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block073Part013CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block073Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block073Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block073Part013CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block073Part013SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block073Part013] using hcert

def TailChunk000Sub001Block073Part014SupportExplicit : Finset ℕ :=
  ([11305] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block073Part014 : ℚ :=
  (461476622225 : ℚ) / 2853722773870608384

def SurrogateDiagonalTailChunk000Sub001Block073Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11305
    = surrogateDiagTailX0RatChunk000Sub001Block073Part014

theorem surrogateDiagonalTailChunk000Sub001Block073Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block073Part014CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block073Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block073Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block073Part014CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block073Part014SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block073Part014] using hcert

def TailChunk000Sub001Block073Part015SupportExplicit : Finset ℕ :=
  ([11306] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block073Part015 : ℚ :=
  (499318890625 : ℚ) / 637933604690456352

def SurrogateDiagonalTailChunk000Sub001Block073Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11306
    = surrogateDiagTailX0RatChunk000Sub001Block073Part015

theorem surrogateDiagonalTailChunk000Sub001Block073Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block073Part015CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block073Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block073Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block073Part015CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block073Part015SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block073Part015] using hcert

def TailChunk000Sub001Block073Part016SupportExplicit : Finset ℕ :=
  ([11307] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block073Part016 : ℚ :=
  (221997273325 : ℚ) / 2016185219762429952

def SurrogateDiagonalTailChunk000Sub001Block073Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11307
    = surrogateDiagTailX0RatChunk000Sub001Block073Part016

theorem surrogateDiagonalTailChunk000Sub001Block073Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block073Part016CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block073Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block073Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block073Part016CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block073Part016SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block073Part016] using hcert

def TailChunk000Sub001Block073Part017SupportExplicit : Finset ℕ :=
  ([11309] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block073Part017 : ℚ :=
  (5901320125 : ℚ) / 2291443762553128008

def SurrogateDiagonalTailChunk000Sub001Block073Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11309
    = surrogateDiagTailX0RatChunk000Sub001Block073Part017

theorem surrogateDiagonalTailChunk000Sub001Block073Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block073Part017CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block073Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block073Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block073Part017CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block073Part017SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block073Part017] using hcert

def TailChunk000Sub001Block073Part018SupportExplicit : Finset ℕ :=
  ([11310] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block073Part018 : ℚ :=
  (198901619275 : ℚ) / 32635023148449792

def SurrogateDiagonalTailChunk000Sub001Block073Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11310
    = surrogateDiagTailX0RatChunk000Sub001Block073Part018

theorem surrogateDiagonalTailChunk000Sub001Block073Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block073Part018CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block073Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block073Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block073Part018CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block073Part018SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block073Part018] using hcert

def TailChunk000Sub001Block073Part019SupportExplicit : Finset ℕ :=
  ([11311] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block073Part019 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block073Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11311
    = surrogateDiagTailX0RatChunk000Sub001Block073Part019

theorem surrogateDiagonalTailChunk000Sub001Block073Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block073Part019CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block073Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block073Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block073Part019CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block073Part019SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block073Part019] using hcert

def TailChunk000Sub001Block073Part020SupportExplicit : Finset ℕ :=
  ([11314] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block073Part020 : ℚ :=
  (500025765625 : ℚ) / 639741421070234112

def SurrogateDiagonalTailChunk000Sub001Block073Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11314
    = surrogateDiagTailX0RatChunk000Sub001Block073Part020

theorem surrogateDiagonalTailChunk000Sub001Block073Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block073Part020CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block073Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block073Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block073Part020CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block073Part020SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block073Part020] using hcert

def TailChunk000Sub001Block073Part021SupportExplicit : Finset ℕ :=
  ([11315] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block073Part021 : ℚ :=
  (2002804529 : ℚ) / 27868386463580160

def SurrogateDiagonalTailChunk000Sub001Block073Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11315
    = surrogateDiagTailX0RatChunk000Sub001Block073Part021

theorem surrogateDiagonalTailChunk000Sub001Block073Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block073Part021CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block073Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block073Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block073Part021CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block073Part021SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block073Part021] using hcert

def TailChunk000Sub001Block073Part022SupportExplicit : Finset ℕ :=
  ([11317] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block073Part022 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block073Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11317
    = surrogateDiagTailX0RatChunk000Sub001Block073Part022

theorem surrogateDiagonalTailChunk000Sub001Block073Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block073Part022CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block073Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block073Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block073Part022CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block073Part022SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block073Part022] using hcert

def TailChunk000Sub001Block073Part023SupportExplicit : Finset ℕ :=
  ([11318] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block073Part023 : ℚ :=
  (500379390625 : ℚ) / 640646768773818162

def SurrogateDiagonalTailChunk000Sub001Block073Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11318
    = surrogateDiagTailX0RatChunk000Sub001Block073Part023

theorem surrogateDiagonalTailChunk000Sub001Block073Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block073Part023CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block073Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block073Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block073Part023CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block073Part023SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block073Part023] using hcert

def TailChunk000Sub001Block073Part024SupportExplicit : Finset ℕ :=
  ([11321] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block073Part024 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block073Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11321
    = surrogateDiagTailX0RatChunk000Sub001Block073Part024

theorem surrogateDiagonalTailChunk000Sub001Block073Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block073Part024CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block073Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block073Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block073Part024CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block073Part024SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block073Part024] using hcert

def surrogateDiagonalTailChunk000Sub001Block073HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block073Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block073Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block073Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block073Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block073Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block073Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block073Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block073Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block073Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block073Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block073Head : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block073Part000
    + surrogateDiagTailX0RatChunk000Sub001Block073Part001
    + surrogateDiagTailX0RatChunk000Sub001Block073Part002
    + surrogateDiagTailX0RatChunk000Sub001Block073Part003
    + surrogateDiagTailX0RatChunk000Sub001Block073Part004
    + surrogateDiagTailX0RatChunk000Sub001Block073Part005
    + surrogateDiagTailX0RatChunk000Sub001Block073Part006
    + surrogateDiagTailX0RatChunk000Sub001Block073Part007
    + surrogateDiagTailX0RatChunk000Sub001Block073Part008
    + surrogateDiagTailX0RatChunk000Sub001Block073Part009

def surrogateDiagonalTailChunk000Sub001Block073MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block073Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block073Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block073Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block073Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block073Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block073Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block073Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block073Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block073Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block073Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block073Mid : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block073Part010
    + surrogateDiagTailX0RatChunk000Sub001Block073Part011
    + surrogateDiagTailX0RatChunk000Sub001Block073Part012
    + surrogateDiagTailX0RatChunk000Sub001Block073Part013
    + surrogateDiagTailX0RatChunk000Sub001Block073Part014
    + surrogateDiagTailX0RatChunk000Sub001Block073Part015
    + surrogateDiagTailX0RatChunk000Sub001Block073Part016
    + surrogateDiagTailX0RatChunk000Sub001Block073Part017
    + surrogateDiagTailX0RatChunk000Sub001Block073Part018
    + surrogateDiagTailX0RatChunk000Sub001Block073Part019

def surrogateDiagonalTailChunk000Sub001Block073TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block073Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block073Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block073Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block073Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block073Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block073Tail : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block073Part020
    + surrogateDiagTailX0RatChunk000Sub001Block073Part021
    + surrogateDiagTailX0RatChunk000Sub001Block073Part022
    + surrogateDiagTailX0RatChunk000Sub001Block073Part023
    + surrogateDiagTailX0RatChunk000Sub001Block073Part024

def surrogateDiagonalTailChunk000Sub001Block073Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub001Block073HeadSum X0
    + surrogateDiagonalTailChunk000Sub001Block073MidSum X0
    + surrogateDiagonalTailChunk000Sub001Block073TailSum X0

def surrogateDiagTailX0RatChunk000Sub001Block073 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block073Part000
    + surrogateDiagTailX0RatChunk000Sub001Block073Part001
    + surrogateDiagTailX0RatChunk000Sub001Block073Part002
    + surrogateDiagTailX0RatChunk000Sub001Block073Part003
    + surrogateDiagTailX0RatChunk000Sub001Block073Part004
    + surrogateDiagTailX0RatChunk000Sub001Block073Part005
    + surrogateDiagTailX0RatChunk000Sub001Block073Part006
    + surrogateDiagTailX0RatChunk000Sub001Block073Part007
    + surrogateDiagTailX0RatChunk000Sub001Block073Part008
    + surrogateDiagTailX0RatChunk000Sub001Block073Part009
    + surrogateDiagTailX0RatChunk000Sub001Block073Part010
    + surrogateDiagTailX0RatChunk000Sub001Block073Part011
    + surrogateDiagTailX0RatChunk000Sub001Block073Part012
    + surrogateDiagTailX0RatChunk000Sub001Block073Part013
    + surrogateDiagTailX0RatChunk000Sub001Block073Part014
    + surrogateDiagTailX0RatChunk000Sub001Block073Part015
    + surrogateDiagTailX0RatChunk000Sub001Block073Part016
    + surrogateDiagTailX0RatChunk000Sub001Block073Part017
    + surrogateDiagTailX0RatChunk000Sub001Block073Part018
    + surrogateDiagTailX0RatChunk000Sub001Block073Part019
    + surrogateDiagTailX0RatChunk000Sub001Block073Part020
    + surrogateDiagTailX0RatChunk000Sub001Block073Part021
    + surrogateDiagTailX0RatChunk000Sub001Block073Part022
    + surrogateDiagTailX0RatChunk000Sub001Block073Part023
    + surrogateDiagTailX0RatChunk000Sub001Block073Part024

theorem surrogateDiagTailX0RatChunk000Sub001Block073_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk000Sub001Block073Head + surrogateDiagTailX0RatChunk000Sub001Block073Mid + surrogateDiagTailX0RatChunk000Sub001Block073Tail =
      surrogateDiagTailX0RatChunk000Sub001Block073 := by
  unfold surrogateDiagTailX0RatChunk000Sub001Block073Head surrogateDiagTailX0RatChunk000Sub001Block073Mid surrogateDiagTailX0RatChunk000Sub001Block073Tail surrogateDiagTailX0RatChunk000Sub001Block073
  ring

def SurrogateDiagonalTailChunk000Sub001Block073HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block073HeadSum X0 = surrogateDiagTailX0RatChunk000Sub001Block073Head

def SurrogateDiagonalTailChunk000Sub001Block073MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block073MidSum X0 = surrogateDiagTailX0RatChunk000Sub001Block073Mid

def SurrogateDiagonalTailChunk000Sub001Block073TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block073TailSum X0 = surrogateDiagTailX0RatChunk000Sub001Block073Tail

theorem surrogateDiagonalTailChunk000Sub001Block073_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk000Sub001Block073HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk000Sub001Block073MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk000Sub001Block073TailCertificateAt X0) :
    surrogateDiagonalTailChunk000Sub001Block073Sum X0 = surrogateDiagTailX0RatChunk000Sub001Block073 := by
  unfold SurrogateDiagonalTailChunk000Sub001Block073HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk000Sub001Block073MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk000Sub001Block073TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk000Sub001Block073Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk000Sub001Block073_eq_head_add_mid_add_tail

/-- Block 074 covers tail-support indices [6850,6875) and q from 11326 to 11363. -/

def TailChunk000Sub001Block074Part000SupportExplicit : Finset ℕ :=
  ([11326] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block074Part000 : ℚ :=
  (1675162600375 : ℚ) / 1381265942035857408

def SurrogateDiagonalTailChunk000Sub001Block074Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11326
    = surrogateDiagTailX0RatChunk000Sub001Block074Part000

theorem surrogateDiagonalTailChunk000Sub001Block074Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block074Part000CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block074Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block074Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block074Part000CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block074Part000SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block074Part000] using hcert

def TailChunk000Sub001Block074Part001SupportExplicit : Finset ℕ :=
  ([11327] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block074Part001 : ℚ :=
  (3584933503 : ℚ) / 1485809544344371200

def SurrogateDiagonalTailChunk000Sub001Block074Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11327
    = surrogateDiagTailX0RatChunk000Sub001Block074Part001

theorem surrogateDiagonalTailChunk000Sub001Block074Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block074Part001CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block074Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block074Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block074Part001CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block074Part001SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block074Part001] using hcert

def TailChunk000Sub001Block074Part002SupportExplicit : Finset ℕ :=
  ([11329] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block074Part002 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block074Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11329
    = surrogateDiagTailX0RatChunk000Sub001Block074Part002

theorem surrogateDiagonalTailChunk000Sub001Block074Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block074Part002CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block074Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block074Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block074Part002CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block074Part002SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block074Part002] using hcert

def TailChunk000Sub001Block074Part003SupportExplicit : Finset ℕ :=
  ([11330] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block074Part003 : ℚ :=
  (852821299 : ℚ) / 433059458572800

def SurrogateDiagonalTailChunk000Sub001Block074Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11330
    = surrogateDiagTailX0RatChunk000Sub001Block074Part003

theorem surrogateDiagonalTailChunk000Sub001Block074Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block074Part003CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block074Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block074Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block074Part003CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block074Part003SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block074Part003] using hcert

def TailChunk000Sub001Block074Part004SupportExplicit : Finset ℕ :=
  ([11333] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block074Part004 : ℚ :=
  (27363279475 : ℚ) / 1233881419498191936

def SurrogateDiagonalTailChunk000Sub001Block074Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11333
    = surrogateDiagTailX0RatChunk000Sub001Block074Part004

theorem surrogateDiagonalTailChunk000Sub001Block074Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block074Part004CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block074Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block074Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block074Part004CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block074Part004SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block074Part004] using hcert

def TailChunk000Sub001Block074Part005SupportExplicit : Finset ℕ :=
  ([11334] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block074Part005 : ℚ :=
  (133732875 : ℚ) / 50823895711744

def SurrogateDiagonalTailChunk000Sub001Block074Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11334
    = surrogateDiagTailX0RatChunk000Sub001Block074Part005

theorem surrogateDiagonalTailChunk000Sub001Block074Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block074Part005CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block074Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block074Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block074Part005CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block074Part005SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block074Part005] using hcert

def TailChunk000Sub001Block074Part006SupportExplicit : Finset ℕ :=
  ([11335] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block074Part006 : ℚ :=
  (642966576025 : ℚ) / 16877435086958020608

def SurrogateDiagonalTailChunk000Sub001Block074Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11335
    = surrogateDiagTailX0RatChunk000Sub001Block074Part006

theorem surrogateDiagonalTailChunk000Sub001Block074Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block074Part006CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block074Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block074Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block074Part006CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block074Part006SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block074Part006] using hcert

def TailChunk000Sub001Block074Part007SupportExplicit : Finset ℕ :=
  ([11337] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block074Part007 : ℚ :=
  (446352671525 : ℚ) / 4075347629437698624

def SurrogateDiagonalTailChunk000Sub001Block074Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11337
    = surrogateDiagTailX0RatChunk000Sub001Block074Part007

theorem surrogateDiagonalTailChunk000Sub001Block074Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block074Part007CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block074Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block074Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block074Part007CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block074Part007SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block074Part007] using hcert

def TailChunk000Sub001Block074Part008SupportExplicit : Finset ℕ :=
  ([11338] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block074Part008 : ℚ :=
  (502149390625 : ℚ) / 645187929594922272

def SurrogateDiagonalTailChunk000Sub001Block074Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11338
    = surrogateDiagTailX0RatChunk000Sub001Block074Part008

theorem surrogateDiagonalTailChunk000Sub001Block074Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block074Part008CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block074Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block074Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block074Part008CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block074Part008SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block074Part008] using hcert

def TailChunk000Sub001Block074Part009SupportExplicit : Finset ℕ :=
  ([11339] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block074Part009 : ℚ :=
  (72274788825 : ℚ) / 3932587439641591808

def SurrogateDiagonalTailChunk000Sub001Block074Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11339
    = surrogateDiagTailX0RatChunk000Sub001Block074Part009

theorem surrogateDiagonalTailChunk000Sub001Block074Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block074Part009CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block074Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block074Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block074Part009CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block074Part009SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block074Part009] using hcert

def TailChunk000Sub001Block074Part010SupportExplicit : Finset ℕ :=
  ([11341] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block074Part010 : ℚ :=
  (1337572213 : ℚ) / 112573391176200000

def SurrogateDiagonalTailChunk000Sub001Block074Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11341
    = surrogateDiagTailX0RatChunk000Sub001Block074Part010

theorem surrogateDiagonalTailChunk000Sub001Block074Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block074Part010CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block074Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block074Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block074Part010CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block074Part010SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block074Part010] using hcert

def TailChunk000Sub001Block074Part011SupportExplicit : Finset ℕ :=
  ([11342] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block074Part011 : ℚ :=
  (973881052325 : ℚ) / 1154074111214429184

def SurrogateDiagonalTailChunk000Sub001Block074Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11342
    = surrogateDiagTailX0RatChunk000Sub001Block074Part011

theorem surrogateDiagonalTailChunk000Sub001Block074Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block074Part011CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block074Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block074Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block074Part011CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block074Part011SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block074Part011] using hcert

def TailChunk000Sub001Block074Part012SupportExplicit : Finset ℕ :=
  ([11343] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block074Part012 : ℚ :=
  (922756144225 : ℚ) / 6455020457670985728

def SurrogateDiagonalTailChunk000Sub001Block074Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11343
    = surrogateDiagTailX0RatChunk000Sub001Block074Part012

theorem surrogateDiagonalTailChunk000Sub001Block074Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block074Part012CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block074Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block074Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block074Part012CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block074Part012SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block074Part012] using hcert

def TailChunk000Sub001Block074Part013SupportExplicit : Finset ℕ :=
  ([11345] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block074Part013 : ℚ :=
  (214699949575 : ℚ) / 5645699653982846976

def SurrogateDiagonalTailChunk000Sub001Block074Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11345
    = surrogateDiagTailX0RatChunk000Sub001Block074Part013

theorem surrogateDiagonalTailChunk000Sub001Block074Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block074Part013CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block074Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block074Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block074Part013CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block074Part013SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block074Part013] using hcert

def TailChunk000Sub001Block074Part014SupportExplicit : Finset ℕ :=
  ([11346] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block074Part014 : ℚ :=
  (5640022729 : ℚ) / 1866613248000000

def SurrogateDiagonalTailChunk000Sub001Block074Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11346
    = surrogateDiagTailX0RatChunk000Sub001Block074Part014

theorem surrogateDiagonalTailChunk000Sub001Block074Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block074Part014CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block074Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block074Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block074Part014CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block074Part014SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block074Part014] using hcert

def TailChunk000Sub001Block074Part015SupportExplicit : Finset ℕ :=
  ([11347] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block074Part015 : ℚ :=
  (365742811 : ℚ) / 16533246852172800

def SurrogateDiagonalTailChunk000Sub001Block074Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11347
    = surrogateDiagTailX0RatChunk000Sub001Block074Part015

theorem surrogateDiagonalTailChunk000Sub001Block074Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block074Part015CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block074Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block074Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block074Part015CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block074Part015SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block074Part015] using hcert

def TailChunk000Sub001Block074Part016SupportExplicit : Finset ℕ :=
  ([11351] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block074Part016 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block074Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11351
    = surrogateDiagTailX0RatChunk000Sub001Block074Part016

theorem surrogateDiagonalTailChunk000Sub001Block074Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block074Part016CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block074Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block074Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block074Part016CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block074Part016SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block074Part016] using hcert

def TailChunk000Sub001Block074Part017SupportExplicit : Finset ℕ :=
  ([11353] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block074Part017 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block074Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11353
    = surrogateDiagTailX0RatChunk000Sub001Block074Part017

theorem surrogateDiagonalTailChunk000Sub001Block074Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block074Part017CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block074Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block074Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block074Part017CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block074Part017SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block074Part017] using hcert

def TailChunk000Sub001Block074Part018SupportExplicit : Finset ℕ :=
  ([11354] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block074Part018 : ℚ :=
  (3821999 : ℚ) / 21527665172100

def SurrogateDiagonalTailChunk000Sub001Block074Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11354
    = surrogateDiagTailX0RatChunk000Sub001Block074Part018

theorem surrogateDiagonalTailChunk000Sub001Block074Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block074Part018CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block074Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block074Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block074Part018CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block074Part018SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block074Part018] using hcert

def TailChunk000Sub001Block074Part019SupportExplicit : Finset ℕ :=
  ([11355] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block074Part019 : ℚ :=
  (334257686075 : ℚ) / 1115199931650932736

def SurrogateDiagonalTailChunk000Sub001Block074Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11355
    = surrogateDiagTailX0RatChunk000Sub001Block074Part019

theorem surrogateDiagonalTailChunk000Sub001Block074Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block074Part019CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block074Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block074Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block074Part019CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block074Part019SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block074Part019] using hcert

def TailChunk000Sub001Block074Part020SupportExplicit : Finset ℕ :=
  ([11357] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block074Part020 : ℚ :=
  (391642303 : ℚ) / 148580954434437120

def SurrogateDiagonalTailChunk000Sub001Block074Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11357
    = surrogateDiagTailX0RatChunk000Sub001Block074Part020

theorem surrogateDiagonalTailChunk000Sub001Block074Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block074Part020CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block074Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block074Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block074Part020CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block074Part020SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block074Part020] using hcert

def TailChunk000Sub001Block074Part021SupportExplicit : Finset ℕ :=
  ([11359] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block074Part021 : ℚ :=
  (104594239375 : ℚ) / 36823288275741984768

def SurrogateDiagonalTailChunk000Sub001Block074Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11359
    = surrogateDiagTailX0RatChunk000Sub001Block074Part021

theorem surrogateDiagonalTailChunk000Sub001Block074Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block074Part021CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block074Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block074Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block074Part021CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block074Part021SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block074Part021] using hcert

def TailChunk000Sub001Block074Part022SupportExplicit : Finset ℕ :=
  ([11361] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block074Part022 : ℚ :=
  (1939370459 : ℚ) / 8817731654492160

def SurrogateDiagonalTailChunk000Sub001Block074Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11361
    = surrogateDiagTailX0RatChunk000Sub001Block074Part022

theorem surrogateDiagonalTailChunk000Sub001Block074Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block074Part022CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block074Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block074Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block074Part022CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block074Part022SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block074Part022] using hcert

def TailChunk000Sub001Block074Part023SupportExplicit : Finset ℕ :=
  ([11362] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block074Part023 : ℚ :=
  (83155780325 : ℚ) / 425021923138830336

def SurrogateDiagonalTailChunk000Sub001Block074Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11362
    = surrogateDiagTailX0RatChunk000Sub001Block074Part023

theorem surrogateDiagonalTailChunk000Sub001Block074Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block074Part023CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block074Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block074Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block074Part023CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block074Part023SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block074Part023] using hcert

def TailChunk000Sub001Block074Part024SupportExplicit : Finset ℕ :=
  ([11363] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block074Part024 : ℚ :=
  (10768946821 : ℚ) / 1134502975800115200

def SurrogateDiagonalTailChunk000Sub001Block074Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11363
    = surrogateDiagTailX0RatChunk000Sub001Block074Part024

theorem surrogateDiagonalTailChunk000Sub001Block074Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block074Part024CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block074Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block074Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block074Part024CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block074Part024SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block074Part024] using hcert

def surrogateDiagonalTailChunk000Sub001Block074HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block074Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block074Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block074Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block074Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block074Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block074Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block074Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block074Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block074Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block074Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block074Head : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block074Part000
    + surrogateDiagTailX0RatChunk000Sub001Block074Part001
    + surrogateDiagTailX0RatChunk000Sub001Block074Part002
    + surrogateDiagTailX0RatChunk000Sub001Block074Part003
    + surrogateDiagTailX0RatChunk000Sub001Block074Part004
    + surrogateDiagTailX0RatChunk000Sub001Block074Part005
    + surrogateDiagTailX0RatChunk000Sub001Block074Part006
    + surrogateDiagTailX0RatChunk000Sub001Block074Part007
    + surrogateDiagTailX0RatChunk000Sub001Block074Part008
    + surrogateDiagTailX0RatChunk000Sub001Block074Part009

def surrogateDiagonalTailChunk000Sub001Block074MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block074Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block074Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block074Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block074Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block074Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block074Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block074Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block074Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block074Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block074Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block074Mid : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block074Part010
    + surrogateDiagTailX0RatChunk000Sub001Block074Part011
    + surrogateDiagTailX0RatChunk000Sub001Block074Part012
    + surrogateDiagTailX0RatChunk000Sub001Block074Part013
    + surrogateDiagTailX0RatChunk000Sub001Block074Part014
    + surrogateDiagTailX0RatChunk000Sub001Block074Part015
    + surrogateDiagTailX0RatChunk000Sub001Block074Part016
    + surrogateDiagTailX0RatChunk000Sub001Block074Part017
    + surrogateDiagTailX0RatChunk000Sub001Block074Part018
    + surrogateDiagTailX0RatChunk000Sub001Block074Part019

def surrogateDiagonalTailChunk000Sub001Block074TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block074Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block074Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block074Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block074Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block074Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block074Tail : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block074Part020
    + surrogateDiagTailX0RatChunk000Sub001Block074Part021
    + surrogateDiagTailX0RatChunk000Sub001Block074Part022
    + surrogateDiagTailX0RatChunk000Sub001Block074Part023
    + surrogateDiagTailX0RatChunk000Sub001Block074Part024

def surrogateDiagonalTailChunk000Sub001Block074Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub001Block074HeadSum X0
    + surrogateDiagonalTailChunk000Sub001Block074MidSum X0
    + surrogateDiagonalTailChunk000Sub001Block074TailSum X0

def surrogateDiagTailX0RatChunk000Sub001Block074 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block074Part000
    + surrogateDiagTailX0RatChunk000Sub001Block074Part001
    + surrogateDiagTailX0RatChunk000Sub001Block074Part002
    + surrogateDiagTailX0RatChunk000Sub001Block074Part003
    + surrogateDiagTailX0RatChunk000Sub001Block074Part004
    + surrogateDiagTailX0RatChunk000Sub001Block074Part005
    + surrogateDiagTailX0RatChunk000Sub001Block074Part006
    + surrogateDiagTailX0RatChunk000Sub001Block074Part007
    + surrogateDiagTailX0RatChunk000Sub001Block074Part008
    + surrogateDiagTailX0RatChunk000Sub001Block074Part009
    + surrogateDiagTailX0RatChunk000Sub001Block074Part010
    + surrogateDiagTailX0RatChunk000Sub001Block074Part011
    + surrogateDiagTailX0RatChunk000Sub001Block074Part012
    + surrogateDiagTailX0RatChunk000Sub001Block074Part013
    + surrogateDiagTailX0RatChunk000Sub001Block074Part014
    + surrogateDiagTailX0RatChunk000Sub001Block074Part015
    + surrogateDiagTailX0RatChunk000Sub001Block074Part016
    + surrogateDiagTailX0RatChunk000Sub001Block074Part017
    + surrogateDiagTailX0RatChunk000Sub001Block074Part018
    + surrogateDiagTailX0RatChunk000Sub001Block074Part019
    + surrogateDiagTailX0RatChunk000Sub001Block074Part020
    + surrogateDiagTailX0RatChunk000Sub001Block074Part021
    + surrogateDiagTailX0RatChunk000Sub001Block074Part022
    + surrogateDiagTailX0RatChunk000Sub001Block074Part023
    + surrogateDiagTailX0RatChunk000Sub001Block074Part024

theorem surrogateDiagTailX0RatChunk000Sub001Block074_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk000Sub001Block074Head + surrogateDiagTailX0RatChunk000Sub001Block074Mid + surrogateDiagTailX0RatChunk000Sub001Block074Tail =
      surrogateDiagTailX0RatChunk000Sub001Block074 := by
  unfold surrogateDiagTailX0RatChunk000Sub001Block074Head surrogateDiagTailX0RatChunk000Sub001Block074Mid surrogateDiagTailX0RatChunk000Sub001Block074Tail surrogateDiagTailX0RatChunk000Sub001Block074
  ring

def SurrogateDiagonalTailChunk000Sub001Block074HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block074HeadSum X0 = surrogateDiagTailX0RatChunk000Sub001Block074Head

def SurrogateDiagonalTailChunk000Sub001Block074MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block074MidSum X0 = surrogateDiagTailX0RatChunk000Sub001Block074Mid

def SurrogateDiagonalTailChunk000Sub001Block074TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block074TailSum X0 = surrogateDiagTailX0RatChunk000Sub001Block074Tail

theorem surrogateDiagonalTailChunk000Sub001Block074_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk000Sub001Block074HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk000Sub001Block074MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk000Sub001Block074TailCertificateAt X0) :
    surrogateDiagonalTailChunk000Sub001Block074Sum X0 = surrogateDiagTailX0RatChunk000Sub001Block074 := by
  unfold SurrogateDiagonalTailChunk000Sub001Block074HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk000Sub001Block074MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk000Sub001Block074TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk000Sub001Block074Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk000Sub001Block074_eq_head_add_mid_add_tail

/-- Block 075 covers tail-support indices [6875,6900) and q from 11365 to 11405. -/

def TailChunk000Sub001Block075Part000SupportExplicit : Finset ℕ :=
  ([11365] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block075Part000 : ℚ :=
  (1936461899775 : ℚ) / 5685633713497440256

def SurrogateDiagonalTailChunk000Sub001Block075Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11365
    = surrogateDiagTailX0RatChunk000Sub001Block075Part000

theorem surrogateDiagonalTailChunk000Sub001Block075Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block075Part000CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block075Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block075Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block075Part000CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block075Part000SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block075Part000] using hcert

def TailChunk000Sub001Block075Part001SupportExplicit : Finset ℕ :=
  ([11366] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block075Part001 : ℚ :=
  (504632640625 : ℚ) / 651586060963571922

def SurrogateDiagonalTailChunk000Sub001Block075Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11366
    = surrogateDiagTailX0RatChunk000Sub001Block075Part001

theorem surrogateDiagonalTailChunk000Sub001Block075Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block075Part001CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block075Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block075Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block075Part001CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block075Part001SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block075Part001] using hcert

def TailChunk000Sub001Block075Part002SupportExplicit : Finset ℕ :=
  ([11369] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block075Part002 : ℚ :=
  (2019596265625 : ℚ) / 10440063188285993472

def SurrogateDiagonalTailChunk000Sub001Block075Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11369
    = surrogateDiagTailX0RatChunk000Sub001Block075Part002

theorem surrogateDiagonalTailChunk000Sub001Block075Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block075Part002CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block075Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block075Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block075Part002CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block075Part002SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block075Part002] using hcert

def TailChunk000Sub001Block075Part003SupportExplicit : Finset ℕ :=
  ([11370] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block075Part003 : ℚ :=
  (75461893475 : ℚ) / 14935713370324992

def SurrogateDiagonalTailChunk000Sub001Block075Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11370
    = surrogateDiagTailX0RatChunk000Sub001Block075Part003

theorem surrogateDiagonalTailChunk000Sub001Block075Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block075Part003CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block075Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block075Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block075Part003CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block075Part003SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block075Part003] using hcert

def TailChunk000Sub001Block075Part004SupportExplicit : Finset ℕ :=
  ([11371] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block075Part004 : ℚ :=
  (95618652325 : ℚ) / 471654572946898944

def SurrogateDiagonalTailChunk000Sub001Block075Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11371
    = surrogateDiagTailX0RatChunk000Sub001Block075Part004

theorem surrogateDiagonalTailChunk000Sub001Block075Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block075Part004CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block075Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block075Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block075Part004CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block075Part004SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block075Part004] using hcert

def TailChunk000Sub001Block075Part005SupportExplicit : Finset ℕ :=
  ([11373] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block075Part005 : ℚ :=
  (678382672375 : ℚ) / 1061420373783871488

def SurrogateDiagonalTailChunk000Sub001Block075Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11373
    = surrogateDiagTailX0RatChunk000Sub001Block075Part005

theorem surrogateDiagonalTailChunk000Sub001Block075Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block075Part005CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block075Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block075Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block075Part005CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block075Part005SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block075Part005] using hcert

def TailChunk000Sub001Block075Part006SupportExplicit : Finset ℕ :=
  ([11377] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block075Part006 : ℚ :=
  (34018704203 : ℚ) / 161530189001884800

def SurrogateDiagonalTailChunk000Sub001Block075Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11377
    = surrogateDiagTailX0RatChunk000Sub001Block075Part006

theorem surrogateDiagonalTailChunk000Sub001Block075Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block075Part006CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block075Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block075Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block075Part006CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block075Part006SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block075Part006] using hcert

def TailChunk000Sub001Block075Part007SupportExplicit : Finset ℕ :=
  ([11378] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block075Part007 : ℚ :=
  (505698765625 : ℚ) / 654342634847457792

def SurrogateDiagonalTailChunk000Sub001Block075Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11378
    = surrogateDiagTailX0RatChunk000Sub001Block075Part007

theorem surrogateDiagonalTailChunk000Sub001Block075Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block075Part007CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block075Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block075Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block075Part007CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block075Part007SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block075Part007] using hcert

def TailChunk000Sub001Block075Part008SupportExplicit : Finset ℕ :=
  ([11379] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block075Part008 : ℚ :=
  (2247431902925 : ℚ) / 4136091716566646784

def SurrogateDiagonalTailChunk000Sub001Block075Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11379
    = surrogateDiagTailX0RatChunk000Sub001Block075Part008

theorem surrogateDiagonalTailChunk000Sub001Block075Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block075Part008CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block075Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block075Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block075Part008CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block075Part008SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block075Part008] using hcert

def TailChunk000Sub001Block075Part009SupportExplicit : Finset ℕ :=
  ([11381] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block075Part009 : ℚ :=
  (2475640067125 : ℚ) / 11189234108325476736

def SurrogateDiagonalTailChunk000Sub001Block075Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11381
    = surrogateDiagTailX0RatChunk000Sub001Block075Part009

theorem surrogateDiagonalTailChunk000Sub001Block075Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block075Part009CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block075Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block075Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block075Part009CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block075Part009SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block075Part009] using hcert

def TailChunk000Sub001Block075Part010SupportExplicit : Finset ℕ :=
  ([11382] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block075Part010 : ℚ :=
  (374857 : ℚ) / 91833004800

def SurrogateDiagonalTailChunk000Sub001Block075Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11382
    = surrogateDiagTailX0RatChunk000Sub001Block075Part010

theorem surrogateDiagonalTailChunk000Sub001Block075Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block075Part010CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block075Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block075Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block075Part010CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block075Part010SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block075Part010] using hcert

def TailChunk000Sub001Block075Part011SupportExplicit : Finset ℕ :=
  ([11383] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block075Part011 : ℚ :=
  (2024573265625 : ℚ) / 10491587153104660722

def SurrogateDiagonalTailChunk000Sub001Block075Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11383
    = surrogateDiagTailX0RatChunk000Sub001Block075Part011

theorem surrogateDiagonalTailChunk000Sub001Block075Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block075Part011CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block075Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block075Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block075Part011CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block075Part011SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block075Part011] using hcert

def TailChunk000Sub001Block075Part012SupportExplicit : Finset ℕ :=
  ([11386] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block075Part012 : ℚ :=
  (506410140625 : ℚ) / 656185203605121312

def SurrogateDiagonalTailChunk000Sub001Block075Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11386
    = surrogateDiagTailX0RatChunk000Sub001Block075Part012

theorem surrogateDiagonalTailChunk000Sub001Block075Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block075Part012CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block075Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block075Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block075Part012CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block075Part012SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block075Part012] using hcert

def TailChunk000Sub001Block075Part013SupportExplicit : Finset ℕ :=
  ([11387] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block075Part013 : ℚ :=
  (269906314025 : ℚ) / 1326006796447383552

def SurrogateDiagonalTailChunk000Sub001Block075Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11387
    = surrogateDiagTailX0RatChunk000Sub001Block075Part013

theorem surrogateDiagonalTailChunk000Sub001Block075Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block075Part013CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block075Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block075Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block075Part013CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block075Part013SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block075Part013] using hcert

def TailChunk000Sub001Block075Part014SupportExplicit : Finset ℕ :=
  ([11389] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block075Part014 : ℚ :=
  (98153185375 : ℚ) / 353943589921481682

def SurrogateDiagonalTailChunk000Sub001Block075Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11389
    = surrogateDiagTailX0RatChunk000Sub001Block075Part014

theorem surrogateDiagonalTailChunk000Sub001Block075Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block075Part014CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block075Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block075Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block075Part014CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block075Part014SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block075Part014] using hcert

def TailChunk000Sub001Block075Part015SupportExplicit : Finset ℕ :=
  ([11390] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block075Part015 : ℚ :=
  (745075890575 : ℚ) / 398008641329823744

def SurrogateDiagonalTailChunk000Sub001Block075Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11390
    = surrogateDiagTailX0RatChunk000Sub001Block075Part015

theorem surrogateDiagonalTailChunk000Sub001Block075Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block075Part015CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block075Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block075Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block075Part015CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block075Part015SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block075Part015] using hcert

def TailChunk000Sub001Block075Part016SupportExplicit : Finset ℕ :=
  ([11391] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block075Part016 : ℚ :=
  (3603028620325 : ℚ) / 8307142426964379648

def SurrogateDiagonalTailChunk000Sub001Block075Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11391
    = surrogateDiagTailX0RatChunk000Sub001Block075Part016

theorem surrogateDiagonalTailChunk000Sub001Block075Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block075Part016CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block075Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block075Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block075Part016CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block075Part016SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block075Part016] using hcert

def TailChunk000Sub001Block075Part017SupportExplicit : Finset ℕ :=
  ([11393] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block075Part017 : ℚ :=
  (2028132015625 : ℚ) / 10528506576069722112

def SurrogateDiagonalTailChunk000Sub001Block075Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11393
    = surrogateDiagTailX0RatChunk000Sub001Block075Part017

theorem surrogateDiagonalTailChunk000Sub001Block075Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block075Part017CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block075Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block075Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block075Part017CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block075Part017SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block075Part017] using hcert

def TailChunk000Sub001Block075Part018SupportExplicit : Finset ℕ :=
  ([11395] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block075Part018 : ℚ :=
  (191852437475 : ℚ) / 539403296378978304

def SurrogateDiagonalTailChunk000Sub001Block075Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11395
    = surrogateDiagTailX0RatChunk000Sub001Block075Part018

theorem surrogateDiagonalTailChunk000Sub001Block075Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block075Part018CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block075Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block075Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block075Part018CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block075Part018SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block075Part018] using hcert

def TailChunk000Sub001Block075Part019SupportExplicit : Finset ℕ :=
  ([11397] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block075Part019 : ℚ :=
  (5236077797 : ℚ) / 10805354494771200

def SurrogateDiagonalTailChunk000Sub001Block075Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11397
    = surrogateDiagTailX0RatChunk000Sub001Block075Part019

theorem surrogateDiagonalTailChunk000Sub001Block075Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block075Part019CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block075Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block075Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block075Part019CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block075Part019SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block075Part019] using hcert

def TailChunk000Sub001Block075Part020SupportExplicit : Finset ℕ :=
  ([11398] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block075Part020 : ℚ :=
  (39176943437 : ℚ) / 46431548260761600

def SurrogateDiagonalTailChunk000Sub001Block075Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11398
    = surrogateDiagTailX0RatChunk000Sub001Block075Part020

theorem surrogateDiagonalTailChunk000Sub001Block075Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block075Part020CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block075Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block075Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block075Part020CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block075Part020SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block075Part020] using hcert

def TailChunk000Sub001Block075Part021SupportExplicit : Finset ℕ :=
  ([11399] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block075Part021 : ℚ :=
  (2030268765625 : ℚ) / 10550704948217844402

def SurrogateDiagonalTailChunk000Sub001Block075Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11399
    = surrogateDiagTailX0RatChunk000Sub001Block075Part021

theorem surrogateDiagonalTailChunk000Sub001Block075Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block075Part021CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block075Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block075Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block075Part021CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block075Part021SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block075Part021] using hcert

def TailChunk000Sub001Block075Part022SupportExplicit : Finset ℕ :=
  ([11401] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block075Part022 : ℚ :=
  (3551389021325 : ℚ) / 15266457466703069184

def SurrogateDiagonalTailChunk000Sub001Block075Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11401
    = surrogateDiagTailX0RatChunk000Sub001Block075Part022

theorem surrogateDiagonalTailChunk000Sub001Block075Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block075Part022CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block075Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block075Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block075Part022CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block075Part022SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block075Part022] using hcert

def TailChunk000Sub001Block075Part023SupportExplicit : Finset ℕ :=
  ([11402] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block075Part023 : ℚ :=
  (32501401 : ℚ) / 42232448800800

def SurrogateDiagonalTailChunk000Sub001Block075Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11402
    = surrogateDiagTailX0RatChunk000Sub001Block075Part023

theorem surrogateDiagonalTailChunk000Sub001Block075Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block075Part023CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block075Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block075Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block075Part023CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block075Part023SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block075Part023] using hcert

def TailChunk000Sub001Block075Part024SupportExplicit : Finset ℕ :=
  ([11405] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block075Part024 : ℚ :=
  (221002807939 : ℚ) / 691936441152307200

def SurrogateDiagonalTailChunk000Sub001Block075Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11405
    = surrogateDiagTailX0RatChunk000Sub001Block075Part024

theorem surrogateDiagonalTailChunk000Sub001Block075Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block075Part024CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block075Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block075Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block075Part024CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block075Part024SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block075Part024] using hcert

def surrogateDiagonalTailChunk000Sub001Block075HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block075Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block075Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block075Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block075Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block075Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block075Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block075Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block075Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block075Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block075Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block075Head : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block075Part000
    + surrogateDiagTailX0RatChunk000Sub001Block075Part001
    + surrogateDiagTailX0RatChunk000Sub001Block075Part002
    + surrogateDiagTailX0RatChunk000Sub001Block075Part003
    + surrogateDiagTailX0RatChunk000Sub001Block075Part004
    + surrogateDiagTailX0RatChunk000Sub001Block075Part005
    + surrogateDiagTailX0RatChunk000Sub001Block075Part006
    + surrogateDiagTailX0RatChunk000Sub001Block075Part007
    + surrogateDiagTailX0RatChunk000Sub001Block075Part008
    + surrogateDiagTailX0RatChunk000Sub001Block075Part009

def surrogateDiagonalTailChunk000Sub001Block075MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block075Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block075Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block075Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block075Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block075Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block075Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block075Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block075Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block075Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block075Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block075Mid : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block075Part010
    + surrogateDiagTailX0RatChunk000Sub001Block075Part011
    + surrogateDiagTailX0RatChunk000Sub001Block075Part012
    + surrogateDiagTailX0RatChunk000Sub001Block075Part013
    + surrogateDiagTailX0RatChunk000Sub001Block075Part014
    + surrogateDiagTailX0RatChunk000Sub001Block075Part015
    + surrogateDiagTailX0RatChunk000Sub001Block075Part016
    + surrogateDiagTailX0RatChunk000Sub001Block075Part017
    + surrogateDiagTailX0RatChunk000Sub001Block075Part018
    + surrogateDiagTailX0RatChunk000Sub001Block075Part019

def surrogateDiagonalTailChunk000Sub001Block075TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block075Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block075Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block075Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block075Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block075Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block075Tail : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block075Part020
    + surrogateDiagTailX0RatChunk000Sub001Block075Part021
    + surrogateDiagTailX0RatChunk000Sub001Block075Part022
    + surrogateDiagTailX0RatChunk000Sub001Block075Part023
    + surrogateDiagTailX0RatChunk000Sub001Block075Part024

def surrogateDiagonalTailChunk000Sub001Block075Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub001Block075HeadSum X0
    + surrogateDiagonalTailChunk000Sub001Block075MidSum X0
    + surrogateDiagonalTailChunk000Sub001Block075TailSum X0

def surrogateDiagTailX0RatChunk000Sub001Block075 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block075Part000
    + surrogateDiagTailX0RatChunk000Sub001Block075Part001
    + surrogateDiagTailX0RatChunk000Sub001Block075Part002
    + surrogateDiagTailX0RatChunk000Sub001Block075Part003
    + surrogateDiagTailX0RatChunk000Sub001Block075Part004
    + surrogateDiagTailX0RatChunk000Sub001Block075Part005
    + surrogateDiagTailX0RatChunk000Sub001Block075Part006
    + surrogateDiagTailX0RatChunk000Sub001Block075Part007
    + surrogateDiagTailX0RatChunk000Sub001Block075Part008
    + surrogateDiagTailX0RatChunk000Sub001Block075Part009
    + surrogateDiagTailX0RatChunk000Sub001Block075Part010
    + surrogateDiagTailX0RatChunk000Sub001Block075Part011
    + surrogateDiagTailX0RatChunk000Sub001Block075Part012
    + surrogateDiagTailX0RatChunk000Sub001Block075Part013
    + surrogateDiagTailX0RatChunk000Sub001Block075Part014
    + surrogateDiagTailX0RatChunk000Sub001Block075Part015
    + surrogateDiagTailX0RatChunk000Sub001Block075Part016
    + surrogateDiagTailX0RatChunk000Sub001Block075Part017
    + surrogateDiagTailX0RatChunk000Sub001Block075Part018
    + surrogateDiagTailX0RatChunk000Sub001Block075Part019
    + surrogateDiagTailX0RatChunk000Sub001Block075Part020
    + surrogateDiagTailX0RatChunk000Sub001Block075Part021
    + surrogateDiagTailX0RatChunk000Sub001Block075Part022
    + surrogateDiagTailX0RatChunk000Sub001Block075Part023
    + surrogateDiagTailX0RatChunk000Sub001Block075Part024

theorem surrogateDiagTailX0RatChunk000Sub001Block075_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk000Sub001Block075Head + surrogateDiagTailX0RatChunk000Sub001Block075Mid + surrogateDiagTailX0RatChunk000Sub001Block075Tail =
      surrogateDiagTailX0RatChunk000Sub001Block075 := by
  unfold surrogateDiagTailX0RatChunk000Sub001Block075Head surrogateDiagTailX0RatChunk000Sub001Block075Mid surrogateDiagTailX0RatChunk000Sub001Block075Tail surrogateDiagTailX0RatChunk000Sub001Block075
  ring

def SurrogateDiagonalTailChunk000Sub001Block075HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block075HeadSum X0 = surrogateDiagTailX0RatChunk000Sub001Block075Head

def SurrogateDiagonalTailChunk000Sub001Block075MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block075MidSum X0 = surrogateDiagTailX0RatChunk000Sub001Block075Mid

def SurrogateDiagonalTailChunk000Sub001Block075TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block075TailSum X0 = surrogateDiagTailX0RatChunk000Sub001Block075Tail

theorem surrogateDiagonalTailChunk000Sub001Block075_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk000Sub001Block075HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk000Sub001Block075MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk000Sub001Block075TailCertificateAt X0) :
    surrogateDiagonalTailChunk000Sub001Block075Sum X0 = surrogateDiagTailX0RatChunk000Sub001Block075 := by
  unfold SurrogateDiagonalTailChunk000Sub001Block075HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk000Sub001Block075MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk000Sub001Block075TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk000Sub001Block075Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk000Sub001Block075_eq_head_add_mid_add_tail

/-- Block 076 covers tail-support indices [6900,6925) and q from 11406 to 11445. -/

def TailChunk000Sub001Block076Part000SupportExplicit : Finset ℕ :=
  ([11406] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block076Part000 : ℚ :=
  (22578607799 : ℚ) / 10427765136000000

def SurrogateDiagonalTailChunk000Sub001Block076Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11406
    = surrogateDiagTailX0RatChunk000Sub001Block076Part000

theorem surrogateDiagonalTailChunk000Sub001Block076Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block076Part000CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block076Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block076Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block076Part000CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block076Part000SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block076Part000] using hcert

def TailChunk000Sub001Block076Part001SupportExplicit : Finset ℕ :=
  ([11407] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block076Part001 : ℚ :=
  (245329786651 : ℚ) / 849516429312000000

def SurrogateDiagonalTailChunk000Sub001Block076Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11407
    = surrogateDiagTailX0RatChunk000Sub001Block076Part001

theorem surrogateDiagonalTailChunk000Sub001Block076Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block076Part001CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block076Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block076Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block076Part001CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block076Part001SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block076Part001] using hcert

def TailChunk000Sub001Block076Part002SupportExplicit : Finset ℕ :=
  ([11409] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block076Part002 : ℚ :=
  (3614425619725 : ℚ) / 8359788530646092928

def SurrogateDiagonalTailChunk000Sub001Block076Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11409
    = surrogateDiagTailX0RatChunk000Sub001Block076Part002

theorem surrogateDiagonalTailChunk000Sub001Block076Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block076Part002CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block076Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block076Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block076Part002CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block076Part002SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block076Part002] using hcert

def TailChunk000Sub001Block076Part003SupportExplicit : Finset ℕ :=
  ([11410] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block076Part003 : ℚ :=
  (1296930618475 : ℚ) / 571389011211091968

def SurrogateDiagonalTailChunk000Sub001Block076Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11410
    = surrogateDiagTailX0RatChunk000Sub001Block076Part003

theorem surrogateDiagonalTailChunk000Sub001Block076Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block076Part003CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block076Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block076Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block076Part003CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block076Part003SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block076Part003] using hcert

def TailChunk000Sub001Block076Part004SupportExplicit : Finset ℕ :=
  ([11411] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block076Part004 : ℚ :=
  (3255273025 : ℚ) / 16952331169886322

def SurrogateDiagonalTailChunk000Sub001Block076Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11411
    = surrogateDiagTailX0RatChunk000Sub001Block076Part004

theorem surrogateDiagonalTailChunk000Sub001Block076Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block076Part004CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block076Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block076Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block076Part004CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block076Part004SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block076Part004] using hcert

def TailChunk000Sub001Block076Part005SupportExplicit : Finset ℕ :=
  ([11413] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block076Part005 : ℚ :=
  (15060030381 : ℚ) / 74944479232000000

def SurrogateDiagonalTailChunk000Sub001Block076Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11413
    = surrogateDiagTailX0RatChunk000Sub001Block076Part005

theorem surrogateDiagonalTailChunk000Sub001Block076Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block076Part005CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block076Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block076Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block076Part005CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block076Part005SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block076Part005] using hcert

def TailChunk000Sub001Block076Part006SupportExplicit : Finset ℕ :=
  ([11414] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block076Part006 : ℚ :=
  (17246320775 : ℚ) / 17669510956832256

def SurrogateDiagonalTailChunk000Sub001Block076Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11414
    = surrogateDiagTailX0RatChunk000Sub001Block076Part006

theorem surrogateDiagonalTailChunk000Sub001Block076Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block076Part006CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block076Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block076Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block076Part006CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block076Part006SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block076Part006] using hcert

def TailChunk000Sub001Block076Part007SupportExplicit : Finset ℕ :=
  ([11415] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block076Part007 : ℚ :=
  (6937307091 : ℚ) / 9111920212705280

def SurrogateDiagonalTailChunk000Sub001Block076Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11415
    = surrogateDiagTailX0RatChunk000Sub001Block076Part007

theorem surrogateDiagonalTailChunk000Sub001Block076Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block076Part007CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block076Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block076Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block076Part007CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block076Part007SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block076Part007] using hcert

def TailChunk000Sub001Block076Part008SupportExplicit : Finset ℕ :=
  ([11418] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block076Part008 : ℚ :=
  (48554417017 : ℚ) / 14006209577779200

def SurrogateDiagonalTailChunk000Sub001Block076Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11418
    = surrogateDiagTailX0RatChunk000Sub001Block076Part008

theorem surrogateDiagonalTailChunk000Sub001Block076Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block076Part008CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block076Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block076Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block076Part008CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block076Part008SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block076Part008] using hcert

def TailChunk000Sub001Block076Part009SupportExplicit : Finset ℕ :=
  ([11419] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block076Part009 : ℚ :=
  (299065765711 : ℚ) / 1360761057792000000

def SurrogateDiagonalTailChunk000Sub001Block076Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11419
    = surrogateDiagTailX0RatChunk000Sub001Block076Part009

theorem surrogateDiagonalTailChunk000Sub001Block076Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block076Part009CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block076Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block076Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block076Part009CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block076Part009SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block076Part009] using hcert

def TailChunk000Sub001Block076Part010SupportExplicit : Finset ℕ :=
  ([11422] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block076Part010 : ℚ :=
  (815388025 : ℚ) / 1063239942277362

def SurrogateDiagonalTailChunk000Sub001Block076Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11422
    = surrogateDiagTailX0RatChunk000Sub001Block076Part010

theorem surrogateDiagonalTailChunk000Sub001Block076Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block076Part010CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block076Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block076Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block076Part010CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block076Part010SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block076Part010] using hcert

def TailChunk000Sub001Block076Part011SupportExplicit : Finset ℕ :=
  ([11423] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block076Part011 : ℚ :=
  (2038827015625 : ℚ) / 10639849645434612882

def SurrogateDiagonalTailChunk000Sub001Block076Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11423
    = surrogateDiagTailX0RatChunk000Sub001Block076Part011

theorem surrogateDiagonalTailChunk000Sub001Block076Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block076Part011CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block076Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block076Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block076Part011CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block076Part011SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block076Part011] using hcert

def TailChunk000Sub001Block076Part012SupportExplicit : Finset ℕ :=
  ([11426] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block076Part012 : ℚ :=
  (46406405475 : ℚ) / 54005001102639104

def SurrogateDiagonalTailChunk000Sub001Block076Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11426
    = surrogateDiagTailX0RatChunk000Sub001Block076Part012

theorem surrogateDiagonalTailChunk000Sub001Block076Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block076Part012CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block076Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block076Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block076Part012CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block076Part012SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block076Part012] using hcert

def TailChunk000Sub001Block076Part013SupportExplicit : Finset ℕ :=
  ([11427] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block076Part013 : ℚ :=
  (1080712826525 : ℚ) / 2010397691088470016

def SurrogateDiagonalTailChunk000Sub001Block076Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11427
    = surrogateDiagTailX0RatChunk000Sub001Block076Part013

theorem surrogateDiagonalTailChunk000Sub001Block076Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block076Part013CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block076Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block076Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block076Part013CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block076Part013SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block076Part013] using hcert

def TailChunk000Sub001Block076Part014SupportExplicit : Finset ℕ :=
  ([11429] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block076Part014 : ℚ :=
  (280296940609 : ℚ) / 1161117750250627200

def SurrogateDiagonalTailChunk000Sub001Block076Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11429
    = surrogateDiagTailX0RatChunk000Sub001Block076Part014

theorem surrogateDiagonalTailChunk000Sub001Block076Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block076Part014CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block076Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block076Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block076Part014CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block076Part014SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block076Part014] using hcert

def TailChunk000Sub001Block076Part015SupportExplicit : Finset ℕ :=
  ([11431] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block076Part015 : ℚ :=
  (231606709921 : ℚ) / 729079244867635200

def SurrogateDiagonalTailChunk000Sub001Block076Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11431
    = surrogateDiagTailX0RatChunk000Sub001Block076Part015

theorem surrogateDiagonalTailChunk000Sub001Block076Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block076Part015CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block076Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block076Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block076Part015CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block076Part015SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block076Part015] using hcert

def TailChunk000Sub001Block076Part016SupportExplicit : Finset ℕ :=
  ([11433] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block076Part016 : ℚ :=
  (1726415943725 : ℚ) / 3636867977851060224

def SurrogateDiagonalTailChunk000Sub001Block076Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11433
    = surrogateDiagTailX0RatChunk000Sub001Block076Part016

theorem surrogateDiagonalTailChunk000Sub001Block076Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block076Part016CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block076Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block076Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block076Part016CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block076Part016SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block076Part016] using hcert

def TailChunk000Sub001Block076Part017SupportExplicit : Finset ℕ :=
  ([11434] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block076Part017 : ℚ :=
  (510688890625 : ℚ) / 667322469115221792

def SurrogateDiagonalTailChunk000Sub001Block076Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11434
    = surrogateDiagTailX0RatChunk000Sub001Block076Part017

theorem surrogateDiagonalTailChunk000Sub001Block076Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block076Part017CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block076Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block076Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block076Part017CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block076Part017SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block076Part017] using hcert

def TailChunk000Sub001Block076Part018SupportExplicit : Finset ℕ :=
  ([11435] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block076Part018 : ℚ :=
  (5554181188525 : ℚ) / 17481219598324942848

def SurrogateDiagonalTailChunk000Sub001Block076Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11435
    = surrogateDiagTailX0RatChunk000Sub001Block076Part018

theorem surrogateDiagonalTailChunk000Sub001Block076Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block076Part018CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block076Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block076Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block076Part018CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block076Part018SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block076Part018] using hcert

def TailChunk000Sub001Block076Part019SupportExplicit : Finset ℕ :=
  ([11437] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block076Part019 : ℚ :=
  (2043827640625 : ℚ) / 10692110890925029152

def SurrogateDiagonalTailChunk000Sub001Block076Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11437
    = surrogateDiagTailX0RatChunk000Sub001Block076Part019

theorem surrogateDiagonalTailChunk000Sub001Block076Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block076Part019CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block076Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block076Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block076Part019CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block076Part019SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block076Part019] using hcert

def TailChunk000Sub001Block076Part020SupportExplicit : Finset ℕ :=
  ([11438] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block076Part020 : ℚ :=
  (178116292625 : ℚ) / 117618742791309312

def SurrogateDiagonalTailChunk000Sub001Block076Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11438
    = surrogateDiagTailX0RatChunk000Sub001Block076Part020

theorem surrogateDiagonalTailChunk000Sub001Block076Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block076Part020CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block076Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block076Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block076Part020CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block076Part020SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block076Part020] using hcert

def TailChunk000Sub001Block076Part021SupportExplicit : Finset ℕ :=
  ([11441] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block076Part021 : ℚ :=
  (176879054375 : ℚ) / 795672945333633024

def SurrogateDiagonalTailChunk000Sub001Block076Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11441
    = surrogateDiagTailX0RatChunk000Sub001Block076Part021

theorem surrogateDiagonalTailChunk000Sub001Block076Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block076Part021CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block076Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block076Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block076Part021CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block076Part021SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block076Part021] using hcert

def TailChunk000Sub001Block076Part022SupportExplicit : Finset ℕ :=
  ([11442] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block076Part022 : ℚ :=
  (35502118175 : ℚ) / 16500171127970724

def SurrogateDiagonalTailChunk000Sub001Block076Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11442
    = surrogateDiagTailX0RatChunk000Sub001Block076Part022

theorem surrogateDiagonalTailChunk000Sub001Block076Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block076Part022CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block076Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block076Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block076Part022CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block076Part022SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block076Part022] using hcert

def TailChunk000Sub001Block076Part023SupportExplicit : Finset ℕ :=
  ([11443] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block076Part023 : ℚ :=
  (2045972640625 : ℚ) / 10714567403836580562

def SurrogateDiagonalTailChunk000Sub001Block076Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11443
    = surrogateDiagTailX0RatChunk000Sub001Block076Part023

theorem surrogateDiagonalTailChunk000Sub001Block076Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block076Part023CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block076Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block076Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block076Part023CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block076Part023SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block076Part023] using hcert

def TailChunk000Sub001Block076Part024SupportExplicit : Finset ℕ :=
  ([11445] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block076Part024 : ℚ :=
  (88118099575 : ℚ) / 75244643451666432

def SurrogateDiagonalTailChunk000Sub001Block076Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11445
    = surrogateDiagTailX0RatChunk000Sub001Block076Part024

theorem surrogateDiagonalTailChunk000Sub001Block076Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block076Part024CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block076Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block076Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block076Part024CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block076Part024SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block076Part024] using hcert

def surrogateDiagonalTailChunk000Sub001Block076HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block076Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block076Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block076Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block076Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block076Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block076Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block076Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block076Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block076Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block076Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block076Head : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block076Part000
    + surrogateDiagTailX0RatChunk000Sub001Block076Part001
    + surrogateDiagTailX0RatChunk000Sub001Block076Part002
    + surrogateDiagTailX0RatChunk000Sub001Block076Part003
    + surrogateDiagTailX0RatChunk000Sub001Block076Part004
    + surrogateDiagTailX0RatChunk000Sub001Block076Part005
    + surrogateDiagTailX0RatChunk000Sub001Block076Part006
    + surrogateDiagTailX0RatChunk000Sub001Block076Part007
    + surrogateDiagTailX0RatChunk000Sub001Block076Part008
    + surrogateDiagTailX0RatChunk000Sub001Block076Part009

def surrogateDiagonalTailChunk000Sub001Block076MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block076Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block076Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block076Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block076Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block076Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block076Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block076Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block076Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block076Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block076Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block076Mid : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block076Part010
    + surrogateDiagTailX0RatChunk000Sub001Block076Part011
    + surrogateDiagTailX0RatChunk000Sub001Block076Part012
    + surrogateDiagTailX0RatChunk000Sub001Block076Part013
    + surrogateDiagTailX0RatChunk000Sub001Block076Part014
    + surrogateDiagTailX0RatChunk000Sub001Block076Part015
    + surrogateDiagTailX0RatChunk000Sub001Block076Part016
    + surrogateDiagTailX0RatChunk000Sub001Block076Part017
    + surrogateDiagTailX0RatChunk000Sub001Block076Part018
    + surrogateDiagTailX0RatChunk000Sub001Block076Part019

def surrogateDiagonalTailChunk000Sub001Block076TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block076Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block076Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block076Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block076Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block076Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block076Tail : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block076Part020
    + surrogateDiagTailX0RatChunk000Sub001Block076Part021
    + surrogateDiagTailX0RatChunk000Sub001Block076Part022
    + surrogateDiagTailX0RatChunk000Sub001Block076Part023
    + surrogateDiagTailX0RatChunk000Sub001Block076Part024

def surrogateDiagonalTailChunk000Sub001Block076Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub001Block076HeadSum X0
    + surrogateDiagonalTailChunk000Sub001Block076MidSum X0
    + surrogateDiagonalTailChunk000Sub001Block076TailSum X0

def surrogateDiagTailX0RatChunk000Sub001Block076 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block076Part000
    + surrogateDiagTailX0RatChunk000Sub001Block076Part001
    + surrogateDiagTailX0RatChunk000Sub001Block076Part002
    + surrogateDiagTailX0RatChunk000Sub001Block076Part003
    + surrogateDiagTailX0RatChunk000Sub001Block076Part004
    + surrogateDiagTailX0RatChunk000Sub001Block076Part005
    + surrogateDiagTailX0RatChunk000Sub001Block076Part006
    + surrogateDiagTailX0RatChunk000Sub001Block076Part007
    + surrogateDiagTailX0RatChunk000Sub001Block076Part008
    + surrogateDiagTailX0RatChunk000Sub001Block076Part009
    + surrogateDiagTailX0RatChunk000Sub001Block076Part010
    + surrogateDiagTailX0RatChunk000Sub001Block076Part011
    + surrogateDiagTailX0RatChunk000Sub001Block076Part012
    + surrogateDiagTailX0RatChunk000Sub001Block076Part013
    + surrogateDiagTailX0RatChunk000Sub001Block076Part014
    + surrogateDiagTailX0RatChunk000Sub001Block076Part015
    + surrogateDiagTailX0RatChunk000Sub001Block076Part016
    + surrogateDiagTailX0RatChunk000Sub001Block076Part017
    + surrogateDiagTailX0RatChunk000Sub001Block076Part018
    + surrogateDiagTailX0RatChunk000Sub001Block076Part019
    + surrogateDiagTailX0RatChunk000Sub001Block076Part020
    + surrogateDiagTailX0RatChunk000Sub001Block076Part021
    + surrogateDiagTailX0RatChunk000Sub001Block076Part022
    + surrogateDiagTailX0RatChunk000Sub001Block076Part023
    + surrogateDiagTailX0RatChunk000Sub001Block076Part024

theorem surrogateDiagTailX0RatChunk000Sub001Block076_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk000Sub001Block076Head + surrogateDiagTailX0RatChunk000Sub001Block076Mid + surrogateDiagTailX0RatChunk000Sub001Block076Tail =
      surrogateDiagTailX0RatChunk000Sub001Block076 := by
  unfold surrogateDiagTailX0RatChunk000Sub001Block076Head surrogateDiagTailX0RatChunk000Sub001Block076Mid surrogateDiagTailX0RatChunk000Sub001Block076Tail surrogateDiagTailX0RatChunk000Sub001Block076
  ring

def SurrogateDiagonalTailChunk000Sub001Block076HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block076HeadSum X0 = surrogateDiagTailX0RatChunk000Sub001Block076Head

def SurrogateDiagonalTailChunk000Sub001Block076MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block076MidSum X0 = surrogateDiagTailX0RatChunk000Sub001Block076Mid

def SurrogateDiagonalTailChunk000Sub001Block076TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block076TailSum X0 = surrogateDiagTailX0RatChunk000Sub001Block076Tail

theorem surrogateDiagonalTailChunk000Sub001Block076_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk000Sub001Block076HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk000Sub001Block076MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk000Sub001Block076TailCertificateAt X0) :
    surrogateDiagonalTailChunk000Sub001Block076Sum X0 = surrogateDiagTailX0RatChunk000Sub001Block076 := by
  unfold SurrogateDiagonalTailChunk000Sub001Block076HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk000Sub001Block076MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk000Sub001Block076TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk000Sub001Block076Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk000Sub001Block076_eq_head_add_mid_add_tail

/-- Block 077 covers tail-support indices [6925,6950) and q from 11446 to 11485. -/

def TailChunk000Sub001Block077Part000SupportExplicit : Finset ℕ :=
  ([11446] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block077Part000 : ℚ :=
  (496349133925 : ℚ) / 600846829640220672

def SurrogateDiagonalTailChunk000Sub001Block077Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11446
    = surrogateDiagTailX0RatChunk000Sub001Block077Part000

theorem surrogateDiagonalTailChunk000Sub001Block077Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block077Part000CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block077Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block077Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block077Part000CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block077Part000SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block077Part000] using hcert

def TailChunk000Sub001Block077Part001SupportExplicit : Finset ℕ :=
  ([11447] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block077Part001 : ℚ :=
  (2047403265625 : ℚ) / 10729558051988304882

def SurrogateDiagonalTailChunk000Sub001Block077Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11447
    = surrogateDiagTailX0RatChunk000Sub001Block077Part001

theorem surrogateDiagonalTailChunk000Sub001Block077Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block077Part001CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block077Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block077Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block077Part001CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block077Part001SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block077Part001] using hcert

def TailChunk000Sub001Block077Part002SupportExplicit : Finset ℕ :=
  ([11451] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block077Part002 : ℚ :=
  (31480129493 : ℚ) / 45871318528419840

def SurrogateDiagonalTailChunk000Sub001Block077Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11451
    = surrogateDiagTailX0RatChunk000Sub001Block077Part002

theorem surrogateDiagonalTailChunk000Sub001Block077Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block077Part002CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block077Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block077Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block077Part002CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block077Part002SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block077Part002] using hcert

def TailChunk000Sub001Block077Part003SupportExplicit : Finset ℕ :=
  ([11453] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block077Part003 : ℚ :=
  (288652498969 : ℚ) / 1243777004155699200

def SurrogateDiagonalTailChunk000Sub001Block077Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11453
    = surrogateDiagTailX0RatChunk000Sub001Block077Part003

theorem surrogateDiagonalTailChunk000Sub001Block077Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block077Part003CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block077Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block077Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block077Part003CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block077Part003SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block077Part003] using hcert

def TailChunk000Sub001Block077Part004SupportExplicit : Finset ℕ :=
  ([11454] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block077Part004 : ℚ :=
  (1282078545325 : ℚ) / 423733669830248448

def SurrogateDiagonalTailChunk000Sub001Block077Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11454
    = surrogateDiagTailX0RatChunk000Sub001Block077Part004

theorem surrogateDiagonalTailChunk000Sub001Block077Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block077Part004CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block077Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block077Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block077Part004CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block077Part004SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block077Part004] using hcert

def TailChunk000Sub001Block077Part005SupportExplicit : Finset ℕ :=
  ([11455] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block077Part005 : ℚ :=
  (9017109625 : ℚ) / 25284529517764608

def SurrogateDiagonalTailChunk000Sub001Block077Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11455
    = surrogateDiagTailX0RatChunk000Sub001Block077Part005

theorem surrogateDiagonalTailChunk000Sub001Block077Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block077Part005CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block077Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block077Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block077Part005CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block077Part005SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block077Part005] using hcert

def TailChunk000Sub001Block077Part006SupportExplicit : Finset ℕ :=
  ([11458] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block077Part006 : ℚ :=
  (2784952775 : ℚ) / 3044666882654208

def SurrogateDiagonalTailChunk000Sub001Block077Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11458
    = surrogateDiagTailX0RatChunk000Sub001Block077Part006

theorem surrogateDiagonalTailChunk000Sub001Block077Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block077Part006CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block077Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block077Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block077Part006CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block077Part006SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block077Part006] using hcert

def TailChunk000Sub001Block077Part007SupportExplicit : Finset ℕ :=
  ([11459] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block077Part007 : ℚ :=
  (1589821331875 : ℚ) / 5803701486988718592

def SurrogateDiagonalTailChunk000Sub001Block077Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11459
    = surrogateDiagTailX0RatChunk000Sub001Block077Part007

theorem surrogateDiagonalTailChunk000Sub001Block077Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block077Part007CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block077Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block077Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block077Part007CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block077Part007SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block077Part007] using hcert

def TailChunk000Sub001Block077Part008SupportExplicit : Finset ℕ :=
  ([11461] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block077Part008 : ℚ :=
  (294633195275 : ℚ) / 1473979603307986944

def SurrogateDiagonalTailChunk000Sub001Block077Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11461
    = surrogateDiagTailX0RatChunk000Sub001Block077Part008

theorem surrogateDiagonalTailChunk000Sub001Block077Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block077Part008CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block077Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block077Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block077Part008CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block077Part008SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block077Part008] using hcert

def TailChunk000Sub001Block077Part009SupportExplicit : Finset ℕ :=
  ([11462] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block077Part009 : ℚ :=
  (2306983457 : ℚ) / 2285336976000000

def SurrogateDiagonalTailChunk000Sub001Block077Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11462
    = surrogateDiagTailX0RatChunk000Sub001Block077Part009

theorem surrogateDiagonalTailChunk000Sub001Block077Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block077Part009CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block077Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block077Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block077Part009CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block077Part009SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block077Part009] using hcert

def TailChunk000Sub001Block077Part010SupportExplicit : Finset ℕ :=
  ([11463] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block077Part010 : ℚ :=
  (91229589239 : ℚ) / 170384580310041600

def SurrogateDiagonalTailChunk000Sub001Block077Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11463
    = surrogateDiagTailX0RatChunk000Sub001Block077Part010

theorem surrogateDiagonalTailChunk000Sub001Block077Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block077Part010CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block077Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block077Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block077Part010CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block077Part010SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block077Part010] using hcert

def TailChunk000Sub001Block077Part011SupportExplicit : Finset ℕ :=
  ([11465] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block077Part011 : ℚ :=
  (5583368685775 : ℚ) / 17665473286545113088

def SurrogateDiagonalTailChunk000Sub001Block077Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11465
    = surrogateDiagTailX0RatChunk000Sub001Block077Part011

theorem surrogateDiagonalTailChunk000Sub001Block077Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block077Part011CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block077Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block077Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block077Part011CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block077Part011SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block077Part011] using hcert

def TailChunk000Sub001Block077Part012SupportExplicit : Finset ℕ :=
  ([11467] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block077Part012 : ℚ :=
  (2054563890625 : ℚ) / 10804747379467629042

def SurrogateDiagonalTailChunk000Sub001Block077Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11467
    = surrogateDiagTailX0RatChunk000Sub001Block077Part012

theorem surrogateDiagonalTailChunk000Sub001Block077Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block077Part012CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block077Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block077Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block077Part012CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block077Part012SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block077Part012] using hcert

def TailChunk000Sub001Block077Part013SupportExplicit : Finset ℕ :=
  ([11469] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block077Part013 : ℚ :=
  (1141564119025 : ℚ) / 2134271087302247712

def SurrogateDiagonalTailChunk000Sub001Block077Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11469
    = surrogateDiagTailX0RatChunk000Sub001Block077Part013

theorem surrogateDiagonalTailChunk000Sub001Block077Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block077Part013CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block077Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block077Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block077Part013CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block077Part013SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block077Part013] using hcert

def TailChunk000Sub001Block077Part014SupportExplicit : Finset ℕ :=
  ([11470] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block077Part014 : ℚ :=
  (341639941 : ℚ) / 193530461552640

def SurrogateDiagonalTailChunk000Sub001Block077Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11470
    = surrogateDiagTailX0RatChunk000Sub001Block077Part014

theorem surrogateDiagonalTailChunk000Sub001Block077Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block077Part014CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block077Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block077Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block077Part014CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block077Part014SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block077Part014] using hcert

def TailChunk000Sub001Block077Part015SupportExplicit : Finset ℕ :=
  ([11471] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block077Part015 : ℚ :=
  (3289596025 : ℚ) / 17311732062891762

def SurrogateDiagonalTailChunk000Sub001Block077Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11471
    = surrogateDiagTailX0RatChunk000Sub001Block077Part015

theorem surrogateDiagonalTailChunk000Sub001Block077Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block077Part015CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block077Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block077Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block077Part015CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block077Part015SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block077Part015] using hcert

def TailChunk000Sub001Block077Part016SupportExplicit : Finset ℕ :=
  ([11473] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block077Part016 : ℚ :=
  (218215817929 : ℚ) / 621926000263987200

def SurrogateDiagonalTailChunk000Sub001Block077Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11473
    = surrogateDiagTailX0RatChunk000Sub001Block077Part016

theorem surrogateDiagonalTailChunk000Sub001Block077Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block077Part016CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block077Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block077Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block077Part016CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block077Part016SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block077Part016] using hcert

def TailChunk000Sub001Block077Part017SupportExplicit : Finset ℕ :=
  ([11474] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block077Part017 : ℚ :=
  (514268265625 : ℚ) / 676711314997719552

def SurrogateDiagonalTailChunk000Sub001Block077Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11474
    = surrogateDiagTailX0RatChunk000Sub001Block077Part017

theorem surrogateDiagonalTailChunk000Sub001Block077Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block077Part017CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block077Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block077Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block077Part017CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block077Part017SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block077Part017] using hcert

def TailChunk000Sub001Block077Part018SupportExplicit : Finset ℕ :=
  ([11477] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block077Part018 : ℚ :=
  (7649457741025 : ℚ) / 36027568552026066048

def SurrogateDiagonalTailChunk000Sub001Block077Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11477
    = surrogateDiagTailX0RatChunk000Sub001Block077Part018

theorem surrogateDiagonalTailChunk000Sub001Block077Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block077Part018CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block077Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block077Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block077Part018CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block077Part018SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block077Part018] using hcert

def TailChunk000Sub001Block077Part019SupportExplicit : Finset ℕ :=
  ([11478] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block077Part019 : ℚ :=
  (228750770075 : ℚ) / 267342741727494144

def SurrogateDiagonalTailChunk000Sub001Block077Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11478
    = surrogateDiagTailX0RatChunk000Sub001Block077Part019

theorem surrogateDiagonalTailChunk000Sub001Block077Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block077Part019CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block077Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block077Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block077Part019CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block077Part019SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block077Part019] using hcert

def TailChunk000Sub001Block077Part020SupportExplicit : Finset ℕ :=
  ([11479] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block077Part020 : ℚ :=
  (27406634875 : ℚ) / 3486451869653501952

def SurrogateDiagonalTailChunk000Sub001Block077Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11479
    = surrogateDiagTailX0RatChunk000Sub001Block077Part020

theorem surrogateDiagonalTailChunk000Sub001Block077Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block077Part020CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block077Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block077Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block077Part020CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block077Part020SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block077Part020] using hcert

def TailChunk000Sub001Block077Part021SupportExplicit : Finset ℕ :=
  ([11481] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block077Part021 : ℚ :=
  (934763565325 : ℚ) / 7465771467444584448

def SurrogateDiagonalTailChunk000Sub001Block077Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11481
    = surrogateDiagTailX0RatChunk000Sub001Block077Part021

theorem surrogateDiagonalTailChunk000Sub001Block077Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block077Part021CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block077Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block077Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block077Part021CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block077Part021SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block077Part021] using hcert

def TailChunk000Sub001Block077Part022SupportExplicit : Finset ℕ :=
  ([11482] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block077Part022 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block077Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11482
    = surrogateDiagTailX0RatChunk000Sub001Block077Part022

theorem surrogateDiagonalTailChunk000Sub001Block077Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block077Part022CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block077Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block077Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block077Part022CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block077Part022SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block077Part022] using hcert

def TailChunk000Sub001Block077Part023SupportExplicit : Finset ℕ :=
  ([11483] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block077Part023 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block077Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11483
    = surrogateDiagTailX0RatChunk000Sub001Block077Part023

theorem surrogateDiagonalTailChunk000Sub001Block077Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block077Part023CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block077Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block077Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block077Part023CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block077Part023SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block077Part023] using hcert

def TailChunk000Sub001Block077Part024SupportExplicit : Finset ℕ :=
  ([11485] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block077Part024 : ℚ :=
  (660070645525 : ℚ) / 17789115672644026368

def SurrogateDiagonalTailChunk000Sub001Block077Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11485
    = surrogateDiagTailX0RatChunk000Sub001Block077Part024

theorem surrogateDiagonalTailChunk000Sub001Block077Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block077Part024CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block077Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block077Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block077Part024CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block077Part024SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block077Part024] using hcert

def surrogateDiagonalTailChunk000Sub001Block077HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block077Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block077Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block077Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block077Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block077Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block077Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block077Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block077Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block077Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block077Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block077Head : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block077Part000
    + surrogateDiagTailX0RatChunk000Sub001Block077Part001
    + surrogateDiagTailX0RatChunk000Sub001Block077Part002
    + surrogateDiagTailX0RatChunk000Sub001Block077Part003
    + surrogateDiagTailX0RatChunk000Sub001Block077Part004
    + surrogateDiagTailX0RatChunk000Sub001Block077Part005
    + surrogateDiagTailX0RatChunk000Sub001Block077Part006
    + surrogateDiagTailX0RatChunk000Sub001Block077Part007
    + surrogateDiagTailX0RatChunk000Sub001Block077Part008
    + surrogateDiagTailX0RatChunk000Sub001Block077Part009

def surrogateDiagonalTailChunk000Sub001Block077MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block077Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block077Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block077Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block077Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block077Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block077Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block077Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block077Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block077Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block077Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block077Mid : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block077Part010
    + surrogateDiagTailX0RatChunk000Sub001Block077Part011
    + surrogateDiagTailX0RatChunk000Sub001Block077Part012
    + surrogateDiagTailX0RatChunk000Sub001Block077Part013
    + surrogateDiagTailX0RatChunk000Sub001Block077Part014
    + surrogateDiagTailX0RatChunk000Sub001Block077Part015
    + surrogateDiagTailX0RatChunk000Sub001Block077Part016
    + surrogateDiagTailX0RatChunk000Sub001Block077Part017
    + surrogateDiagTailX0RatChunk000Sub001Block077Part018
    + surrogateDiagTailX0RatChunk000Sub001Block077Part019

def surrogateDiagonalTailChunk000Sub001Block077TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block077Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block077Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block077Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block077Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block077Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block077Tail : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block077Part020
    + surrogateDiagTailX0RatChunk000Sub001Block077Part021
    + surrogateDiagTailX0RatChunk000Sub001Block077Part022
    + surrogateDiagTailX0RatChunk000Sub001Block077Part023
    + surrogateDiagTailX0RatChunk000Sub001Block077Part024

def surrogateDiagonalTailChunk000Sub001Block077Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub001Block077HeadSum X0
    + surrogateDiagonalTailChunk000Sub001Block077MidSum X0
    + surrogateDiagonalTailChunk000Sub001Block077TailSum X0

def surrogateDiagTailX0RatChunk000Sub001Block077 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block077Part000
    + surrogateDiagTailX0RatChunk000Sub001Block077Part001
    + surrogateDiagTailX0RatChunk000Sub001Block077Part002
    + surrogateDiagTailX0RatChunk000Sub001Block077Part003
    + surrogateDiagTailX0RatChunk000Sub001Block077Part004
    + surrogateDiagTailX0RatChunk000Sub001Block077Part005
    + surrogateDiagTailX0RatChunk000Sub001Block077Part006
    + surrogateDiagTailX0RatChunk000Sub001Block077Part007
    + surrogateDiagTailX0RatChunk000Sub001Block077Part008
    + surrogateDiagTailX0RatChunk000Sub001Block077Part009
    + surrogateDiagTailX0RatChunk000Sub001Block077Part010
    + surrogateDiagTailX0RatChunk000Sub001Block077Part011
    + surrogateDiagTailX0RatChunk000Sub001Block077Part012
    + surrogateDiagTailX0RatChunk000Sub001Block077Part013
    + surrogateDiagTailX0RatChunk000Sub001Block077Part014
    + surrogateDiagTailX0RatChunk000Sub001Block077Part015
    + surrogateDiagTailX0RatChunk000Sub001Block077Part016
    + surrogateDiagTailX0RatChunk000Sub001Block077Part017
    + surrogateDiagTailX0RatChunk000Sub001Block077Part018
    + surrogateDiagTailX0RatChunk000Sub001Block077Part019
    + surrogateDiagTailX0RatChunk000Sub001Block077Part020
    + surrogateDiagTailX0RatChunk000Sub001Block077Part021
    + surrogateDiagTailX0RatChunk000Sub001Block077Part022
    + surrogateDiagTailX0RatChunk000Sub001Block077Part023
    + surrogateDiagTailX0RatChunk000Sub001Block077Part024

theorem surrogateDiagTailX0RatChunk000Sub001Block077_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk000Sub001Block077Head + surrogateDiagTailX0RatChunk000Sub001Block077Mid + surrogateDiagTailX0RatChunk000Sub001Block077Tail =
      surrogateDiagTailX0RatChunk000Sub001Block077 := by
  unfold surrogateDiagTailX0RatChunk000Sub001Block077Head surrogateDiagTailX0RatChunk000Sub001Block077Mid surrogateDiagTailX0RatChunk000Sub001Block077Tail surrogateDiagTailX0RatChunk000Sub001Block077
  ring

def SurrogateDiagonalTailChunk000Sub001Block077HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block077HeadSum X0 = surrogateDiagTailX0RatChunk000Sub001Block077Head

def SurrogateDiagonalTailChunk000Sub001Block077MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block077MidSum X0 = surrogateDiagTailX0RatChunk000Sub001Block077Mid

def SurrogateDiagonalTailChunk000Sub001Block077TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block077TailSum X0 = surrogateDiagTailX0RatChunk000Sub001Block077Tail

theorem surrogateDiagonalTailChunk000Sub001Block077_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk000Sub001Block077HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk000Sub001Block077MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk000Sub001Block077TailCertificateAt X0) :
    surrogateDiagonalTailChunk000Sub001Block077Sum X0 = surrogateDiagTailX0RatChunk000Sub001Block077 := by
  unfold SurrogateDiagonalTailChunk000Sub001Block077HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk000Sub001Block077MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk000Sub001Block077TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk000Sub001Block077Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk000Sub001Block077_eq_head_add_mid_add_tail

/-- Block 078 covers tail-support indices [6950,6975) and q from 11486 to 11526. -/

def TailChunk000Sub001Block078Part000SupportExplicit : Finset ℕ :=
  ([11486] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block078Part000 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block078Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11486
    = surrogateDiagTailX0RatChunk000Sub001Block078Part000

theorem surrogateDiagonalTailChunk000Sub001Block078Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block078Part000CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block078Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block078Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block078Part000CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block078Part000SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block078Part000] using hcert

def TailChunk000Sub001Block078Part001SupportExplicit : Finset ℕ :=
  ([11487] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block078Part001 : ℚ :=
  (495634898975 : ℚ) / 2304052752306299904

def SurrogateDiagonalTailChunk000Sub001Block078Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11487
    = surrogateDiagTailX0RatChunk000Sub001Block078Part001

theorem surrogateDiagonalTailChunk000Sub001Block078Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block078Part001CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block078Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block078Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block078Part001CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block078Part001SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block078Part001] using hcert

def TailChunk000Sub001Block078Part002SupportExplicit : Finset ℕ :=
  ([11489] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block078Part002 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block078Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11489
    = surrogateDiagTailX0RatChunk000Sub001Block078Part002

theorem surrogateDiagonalTailChunk000Sub001Block078Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block078Part002CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block078Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block078Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block078Part002CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block078Part002SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block078Part002] using hcert

def TailChunk000Sub001Block078Part003SupportExplicit : Finset ℕ :=
  ([11490] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block078Part003 : ℚ :=
  (504063597475 : ℚ) / 218092262796853248

def SurrogateDiagonalTailChunk000Sub001Block078Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11490
    = surrogateDiagTailX0RatChunk000Sub001Block078Part003

theorem surrogateDiagonalTailChunk000Sub001Block078Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block078Part003CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block078Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block078Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block078Part003CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block078Part003SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block078Part003] using hcert

def TailChunk000Sub001Block078Part004SupportExplicit : Finset ℕ :=
  ([11491] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block078Part004 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block078Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11491
    = surrogateDiagTailX0RatChunk000Sub001Block078Part004

theorem surrogateDiagonalTailChunk000Sub001Block078Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block078Part004CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block078Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block078Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block078Part004CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block078Part004SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block078Part004] using hcert

def TailChunk000Sub001Block078Part005SupportExplicit : Finset ℕ :=
  ([11494] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block078Part005 : ℚ :=
  (140984399 : ℚ) / 813981931833600

def SurrogateDiagonalTailChunk000Sub001Block078Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11494
    = surrogateDiagTailX0RatChunk000Sub001Block078Part005

theorem surrogateDiagonalTailChunk000Sub001Block078Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block078Part005CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block078Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block078Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block078Part005CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block078Part005SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block078Part005] using hcert

def TailChunk000Sub001Block078Part006SupportExplicit : Finset ℕ :=
  ([11497] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block078Part006 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block078Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11497
    = surrogateDiagTailX0RatChunk000Sub001Block078Part006

theorem surrogateDiagonalTailChunk000Sub001Block078Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block078Part006CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block078Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block078Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block078Part006CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block078Part006SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block078Part006] using hcert

def TailChunk000Sub001Block078Part007SupportExplicit : Finset ℕ :=
  ([11498] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block078Part007 : ℚ :=
  (516421890625 : ℚ) / 682391966456830752

def SurrogateDiagonalTailChunk000Sub001Block078Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11498
    = surrogateDiagTailX0RatChunk000Sub001Block078Part007

theorem surrogateDiagonalTailChunk000Sub001Block078Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block078Part007CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block078Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block078Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block078Part007CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block078Part007SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block078Part007] using hcert

def TailChunk000Sub001Block078Part008SupportExplicit : Finset ℕ :=
  ([11499] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block078Part008 : ℚ :=
  (229597272925 : ℚ) / 2156695597690724352

def SurrogateDiagonalTailChunk000Sub001Block078Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11499
    = surrogateDiagTailX0RatChunk000Sub001Block078Part008

theorem surrogateDiagonalTailChunk000Sub001Block078Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block078Part008CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block078Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block078Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block078Part008CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block078Part008SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block078Part008] using hcert

def TailChunk000Sub001Block078Part009SupportExplicit : Finset ℕ :=
  ([11501] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block078Part009 : ℚ :=
  (542580071 : ℚ) / 17059949112360960

def SurrogateDiagonalTailChunk000Sub001Block078Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11501
    = surrogateDiagTailX0RatChunk000Sub001Block078Part009

theorem surrogateDiagonalTailChunk000Sub001Block078Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block078Part009CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block078Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block078Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block078Part009CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block078Part009SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block078Part009] using hcert

def TailChunk000Sub001Block078Part010SupportExplicit : Finset ℕ :=
  ([11503] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block078Part010 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block078Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11503
    = surrogateDiagTailX0RatChunk000Sub001Block078Part010

theorem surrogateDiagonalTailChunk000Sub001Block078Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block078Part010CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block078Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block078Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block078Part010CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block078Part010SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block078Part010] using hcert

def TailChunk000Sub001Block078Part011SupportExplicit : Finset ℕ :=
  ([11505] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block078Part011 : ℚ :=
  (169653746725 : ℚ) / 400564553093480448

def SurrogateDiagonalTailChunk000Sub001Block078Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11505
    = surrogateDiagTailX0RatChunk000Sub001Block078Part011

theorem surrogateDiagonalTailChunk000Sub001Block078Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block078Part011CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block078Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block078Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block078Part011CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block078Part011SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block078Part011] using hcert

def TailChunk000Sub001Block078Part012SupportExplicit : Finset ℕ :=
  ([11506] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block078Part012 : ℚ :=
  (73709721223 : ℚ) / 74262379762051200

def SurrogateDiagonalTailChunk000Sub001Block078Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11506
    = surrogateDiagTailX0RatChunk000Sub001Block078Part012

theorem surrogateDiagonalTailChunk000Sub001Block078Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block078Part012CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block078Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block078Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block078Part012CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block078Part012SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block078Part012] using hcert

def TailChunk000Sub001Block078Part013SupportExplicit : Finset ℕ :=
  ([11507] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block078Part013 : ℚ :=
  (27626021 : ℚ) / 10009489548810240

def SurrogateDiagonalTailChunk000Sub001Block078Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11507
    = surrogateDiagTailX0RatChunk000Sub001Block078Part013

theorem surrogateDiagonalTailChunk000Sub001Block078Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block078Part013CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block078Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block078Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block078Part013CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block078Part013SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block078Part013] using hcert

def TailChunk000Sub001Block078Part014SupportExplicit : Finset ℕ :=
  ([11509] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block078Part014 : ℚ :=
  (102342681875 : ℚ) / 17110534552691933184

def SurrogateDiagonalTailChunk000Sub001Block078Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11509
    = surrogateDiagTailX0RatChunk000Sub001Block078Part014

theorem surrogateDiagonalTailChunk000Sub001Block078Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block078Part014CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block078Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block078Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block078Part014CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block078Part014SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block078Part014] using hcert

def TailChunk000Sub001Block078Part015SupportExplicit : Finset ℕ :=
  ([11510] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block078Part015 : ℚ :=
  (15720164611 : ℚ) / 11195878728000000

def SurrogateDiagonalTailChunk000Sub001Block078Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11510
    = surrogateDiagTailX0RatChunk000Sub001Block078Part015

theorem surrogateDiagonalTailChunk000Sub001Block078Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block078Part015CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block078Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block078Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block078Part015CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block078Part015SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block078Part015] using hcert

def TailChunk000Sub001Block078Part016SupportExplicit : Finset ℕ :=
  ([11513] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block078Part016 : ℚ :=
  (5659914775 : ℚ) / 1574811168914092032

def SurrogateDiagonalTailChunk000Sub001Block078Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11513
    = surrogateDiagTailX0RatChunk000Sub001Block078Part016

theorem surrogateDiagonalTailChunk000Sub001Block078Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block078Part016CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block078Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block078Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block078Part016CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block078Part016SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block078Part016] using hcert

def TailChunk000Sub001Block078Part017SupportExplicit : Finset ℕ :=
  ([11514] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block078Part017 : ℚ :=
  (17118573283 : ℚ) / 5599839744000000

def SurrogateDiagonalTailChunk000Sub001Block078Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11514
    = surrogateDiagTailX0RatChunk000Sub001Block078Part017

theorem surrogateDiagonalTailChunk000Sub001Block078Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block078Part017CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block078Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block078Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block078Part017CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block078Part017SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block078Part017] using hcert

def TailChunk000Sub001Block078Part018SupportExplicit : Finset ℕ :=
  ([11517] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block078Part018 : ℚ :=
  (39002422387 : ℚ) / 234705792828211200

def SurrogateDiagonalTailChunk000Sub001Block078Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11517
    = surrogateDiagTailX0RatChunk000Sub001Block078Part018

theorem surrogateDiagonalTailChunk000Sub001Block078Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block078Part018CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block078Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block078Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block078Part018CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block078Part018SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block078Part018] using hcert

def TailChunk000Sub001Block078Part019SupportExplicit : Finset ℕ :=
  ([11518] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block078Part019 : ℚ :=
  (628163158475 : ℚ) / 659659263802546176

def SurrogateDiagonalTailChunk000Sub001Block078Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11518
    = surrogateDiagTailX0RatChunk000Sub001Block078Part019

theorem surrogateDiagonalTailChunk000Sub001Block078Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block078Part019CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block078Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block078Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block078Part019CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block078Part019SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block078Part019] using hcert

def TailChunk000Sub001Block078Part020SupportExplicit : Finset ℕ :=
  ([11519] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block078Part020 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block078Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11519
    = surrogateDiagTailX0RatChunk000Sub001Block078Part020

theorem surrogateDiagonalTailChunk000Sub001Block078Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block078Part020CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block078Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block078Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block078Part020CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block078Part020SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block078Part020] using hcert

def TailChunk000Sub001Block078Part021SupportExplicit : Finset ℕ :=
  ([11521] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block078Part021 : ℚ :=
  (401616139 : ℚ) / 157383406387200000

def SurrogateDiagonalTailChunk000Sub001Block078Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11521
    = surrogateDiagTailX0RatChunk000Sub001Block078Part021

theorem surrogateDiagonalTailChunk000Sub001Block078Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block078Part021CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block078Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block078Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block078Part021CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block078Part021SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block078Part021] using hcert

def TailChunk000Sub001Block078Part022SupportExplicit : Finset ℕ :=
  ([11522] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block078Part022 : ℚ :=
  (1733650258975 : ℚ) / 1479514175519810688

def SurrogateDiagonalTailChunk000Sub001Block078Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11522
    = surrogateDiagTailX0RatChunk000Sub001Block078Part022

theorem surrogateDiagonalTailChunk000Sub001Block078Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block078Part022CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block078Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block078Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block078Part022CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block078Part022SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block078Part022] using hcert

def TailChunk000Sub001Block078Part023SupportExplicit : Finset ℕ :=
  ([11523] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block078Part023 : ℚ :=
  (941992037875 : ℚ) / 7116556751017494528

def SurrogateDiagonalTailChunk000Sub001Block078Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11523
    = surrogateDiagTailX0RatChunk000Sub001Block078Part023

theorem surrogateDiagonalTailChunk000Sub001Block078Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block078Part023CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block078Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block078Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block078Part023CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block078Part023SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block078Part023] using hcert

def TailChunk000Sub001Block078Part024SupportExplicit : Finset ℕ :=
  ([11526] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block078Part024 : ℚ :=
  (270060237175 : ℚ) / 103142789209915392

def SurrogateDiagonalTailChunk000Sub001Block078Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11526
    = surrogateDiagTailX0RatChunk000Sub001Block078Part024

theorem surrogateDiagonalTailChunk000Sub001Block078Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block078Part024CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block078Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block078Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block078Part024CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block078Part024SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block078Part024] using hcert

def surrogateDiagonalTailChunk000Sub001Block078HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block078Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block078Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block078Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block078Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block078Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block078Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block078Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block078Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block078Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block078Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block078Head : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block078Part000
    + surrogateDiagTailX0RatChunk000Sub001Block078Part001
    + surrogateDiagTailX0RatChunk000Sub001Block078Part002
    + surrogateDiagTailX0RatChunk000Sub001Block078Part003
    + surrogateDiagTailX0RatChunk000Sub001Block078Part004
    + surrogateDiagTailX0RatChunk000Sub001Block078Part005
    + surrogateDiagTailX0RatChunk000Sub001Block078Part006
    + surrogateDiagTailX0RatChunk000Sub001Block078Part007
    + surrogateDiagTailX0RatChunk000Sub001Block078Part008
    + surrogateDiagTailX0RatChunk000Sub001Block078Part009

def surrogateDiagonalTailChunk000Sub001Block078MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block078Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block078Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block078Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block078Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block078Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block078Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block078Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block078Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block078Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block078Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block078Mid : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block078Part010
    + surrogateDiagTailX0RatChunk000Sub001Block078Part011
    + surrogateDiagTailX0RatChunk000Sub001Block078Part012
    + surrogateDiagTailX0RatChunk000Sub001Block078Part013
    + surrogateDiagTailX0RatChunk000Sub001Block078Part014
    + surrogateDiagTailX0RatChunk000Sub001Block078Part015
    + surrogateDiagTailX0RatChunk000Sub001Block078Part016
    + surrogateDiagTailX0RatChunk000Sub001Block078Part017
    + surrogateDiagTailX0RatChunk000Sub001Block078Part018
    + surrogateDiagTailX0RatChunk000Sub001Block078Part019

def surrogateDiagonalTailChunk000Sub001Block078TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block078Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block078Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block078Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block078Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block078Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block078Tail : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block078Part020
    + surrogateDiagTailX0RatChunk000Sub001Block078Part021
    + surrogateDiagTailX0RatChunk000Sub001Block078Part022
    + surrogateDiagTailX0RatChunk000Sub001Block078Part023
    + surrogateDiagTailX0RatChunk000Sub001Block078Part024

def surrogateDiagonalTailChunk000Sub001Block078Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub001Block078HeadSum X0
    + surrogateDiagonalTailChunk000Sub001Block078MidSum X0
    + surrogateDiagonalTailChunk000Sub001Block078TailSum X0

def surrogateDiagTailX0RatChunk000Sub001Block078 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block078Part000
    + surrogateDiagTailX0RatChunk000Sub001Block078Part001
    + surrogateDiagTailX0RatChunk000Sub001Block078Part002
    + surrogateDiagTailX0RatChunk000Sub001Block078Part003
    + surrogateDiagTailX0RatChunk000Sub001Block078Part004
    + surrogateDiagTailX0RatChunk000Sub001Block078Part005
    + surrogateDiagTailX0RatChunk000Sub001Block078Part006
    + surrogateDiagTailX0RatChunk000Sub001Block078Part007
    + surrogateDiagTailX0RatChunk000Sub001Block078Part008
    + surrogateDiagTailX0RatChunk000Sub001Block078Part009
    + surrogateDiagTailX0RatChunk000Sub001Block078Part010
    + surrogateDiagTailX0RatChunk000Sub001Block078Part011
    + surrogateDiagTailX0RatChunk000Sub001Block078Part012
    + surrogateDiagTailX0RatChunk000Sub001Block078Part013
    + surrogateDiagTailX0RatChunk000Sub001Block078Part014
    + surrogateDiagTailX0RatChunk000Sub001Block078Part015
    + surrogateDiagTailX0RatChunk000Sub001Block078Part016
    + surrogateDiagTailX0RatChunk000Sub001Block078Part017
    + surrogateDiagTailX0RatChunk000Sub001Block078Part018
    + surrogateDiagTailX0RatChunk000Sub001Block078Part019
    + surrogateDiagTailX0RatChunk000Sub001Block078Part020
    + surrogateDiagTailX0RatChunk000Sub001Block078Part021
    + surrogateDiagTailX0RatChunk000Sub001Block078Part022
    + surrogateDiagTailX0RatChunk000Sub001Block078Part023
    + surrogateDiagTailX0RatChunk000Sub001Block078Part024

theorem surrogateDiagTailX0RatChunk000Sub001Block078_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk000Sub001Block078Head + surrogateDiagTailX0RatChunk000Sub001Block078Mid + surrogateDiagTailX0RatChunk000Sub001Block078Tail =
      surrogateDiagTailX0RatChunk000Sub001Block078 := by
  unfold surrogateDiagTailX0RatChunk000Sub001Block078Head surrogateDiagTailX0RatChunk000Sub001Block078Mid surrogateDiagTailX0RatChunk000Sub001Block078Tail surrogateDiagTailX0RatChunk000Sub001Block078
  ring

def SurrogateDiagonalTailChunk000Sub001Block078HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block078HeadSum X0 = surrogateDiagTailX0RatChunk000Sub001Block078Head

def SurrogateDiagonalTailChunk000Sub001Block078MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block078MidSum X0 = surrogateDiagTailX0RatChunk000Sub001Block078Mid

def SurrogateDiagonalTailChunk000Sub001Block078TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block078TailSum X0 = surrogateDiagTailX0RatChunk000Sub001Block078Tail

theorem surrogateDiagonalTailChunk000Sub001Block078_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk000Sub001Block078HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk000Sub001Block078MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk000Sub001Block078TailCertificateAt X0) :
    surrogateDiagonalTailChunk000Sub001Block078Sum X0 = surrogateDiagTailX0RatChunk000Sub001Block078 := by
  unfold SurrogateDiagonalTailChunk000Sub001Block078HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk000Sub001Block078MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk000Sub001Block078TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk000Sub001Block078Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk000Sub001Block078_eq_head_add_mid_add_tail

/-- Block 079 covers tail-support indices [6975,7000) and q from 11527 to 11566. -/

def TailChunk000Sub001Block079Part000SupportExplicit : Finset ℕ :=
  ([11527] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block079Part000 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block079Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11527
    = surrogateDiagTailX0RatChunk000Sub001Block079Part000

theorem surrogateDiagonalTailChunk000Sub001Block079Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block079Part000CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block079Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block079Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block079Part000CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block079Part000SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block079Part000] using hcert

def TailChunk000Sub001Block079Part001SupportExplicit : Finset ℕ :=
  ([11530] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block079Part001 : ℚ :=
  (262914124525 : ℚ) / 187899441900945408

def SurrogateDiagonalTailChunk000Sub001Block079Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11530
    = surrogateDiagTailX0RatChunk000Sub001Block079Part001

theorem surrogateDiagonalTailChunk000Sub001Block079Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block079Part001CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block079Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block079Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block079Part001CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block079Part001SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block079Part001] using hcert

def TailChunk000Sub001Block079Part002SupportExplicit : Finset ℕ :=
  ([11531] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block079Part002 : ℚ :=
  (297831671875 : ℚ) / 31951167401318565888

def SurrogateDiagonalTailChunk000Sub001Block079Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11531
    = surrogateDiagTailX0RatChunk000Sub001Block079Part002

theorem surrogateDiagonalTailChunk000Sub001Block079Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block079Part002CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block079Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block079Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block079Part002CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block079Part002SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block079Part002] using hcert

def TailChunk000Sub001Block079Part003SupportExplicit : Finset ℕ :=
  ([11533] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block079Part003 : ℚ :=
  (188982949075 : ℚ) / 35400335334754923648

def SurrogateDiagonalTailChunk000Sub001Block079Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11533
    = surrogateDiagTailX0RatChunk000Sub001Block079Part003

theorem surrogateDiagonalTailChunk000Sub001Block079Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block079Part003CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block079Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block079Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block079Part003CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block079Part003SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block079Part003] using hcert

def TailChunk000Sub001Block079Part004SupportExplicit : Finset ℕ :=
  ([11534] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block079Part004 : ℚ :=
  (2017198749175 : ℚ) / 2487340580582227968

def SurrogateDiagonalTailChunk000Sub001Block079Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11534
    = surrogateDiagTailX0RatChunk000Sub001Block079Part004

theorem surrogateDiagonalTailChunk000Sub001Block079Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block079Part004CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block079Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block079Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block079Part004CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block079Part004SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block079Part004] using hcert

def TailChunk000Sub001Block079Part005SupportExplicit : Finset ℕ :=
  ([11535] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block079Part005 : ℚ :=
  (997842162475 : ℚ) / 3563130157529038848

def SurrogateDiagonalTailChunk000Sub001Block079Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11535
    = surrogateDiagTailX0RatChunk000Sub001Block079Part005

theorem surrogateDiagonalTailChunk000Sub001Block079Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block079Part005CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block079Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block079Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block079Part005CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block079Part005SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block079Part005] using hcert

def TailChunk000Sub001Block079Part006SupportExplicit : Finset ℕ :=
  ([11537] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block079Part006 : ℚ :=
  (1281125 : ℚ) / 771631157812488

def SurrogateDiagonalTailChunk000Sub001Block079Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11537
    = surrogateDiagTailX0RatChunk000Sub001Block079Part006

theorem surrogateDiagonalTailChunk000Sub001Block079Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block079Part006CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block079Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block079Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block079Part006CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block079Part006SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block079Part006] using hcert

def TailChunk000Sub001Block079Part007SupportExplicit : Finset ℕ :=
  ([11539] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block079Part007 : ℚ :=
  (21629527 : ℚ) / 1885176454298880

def SurrogateDiagonalTailChunk000Sub001Block079Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11539
    = surrogateDiagTailX0RatChunk000Sub001Block079Part007

theorem surrogateDiagonalTailChunk000Sub001Block079Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block079Part007CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block079Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block079Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block079Part007CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block079Part007SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block079Part007] using hcert

def TailChunk000Sub001Block079Part008SupportExplicit : Finset ℕ :=
  ([11541] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block079Part008 : ℚ :=
  (924609723725 : ℚ) / 4376772423942018624

def SurrogateDiagonalTailChunk000Sub001Block079Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11541
    = surrogateDiagTailX0RatChunk000Sub001Block079Part008

theorem surrogateDiagonalTailChunk000Sub001Block079Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block079Part008CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block079Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block079Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block079Part008CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block079Part008SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block079Part008] using hcert

def TailChunk000Sub001Block079Part009SupportExplicit : Finset ℕ :=
  ([11542] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block079Part009 : ℚ :=
  (994435413875 : ℚ) / 1181108376685569024

def SurrogateDiagonalTailChunk000Sub001Block079Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11542
    = surrogateDiagTailX0RatChunk000Sub001Block079Part009

theorem surrogateDiagonalTailChunk000Sub001Block079Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block079Part009CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block079Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block079Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block079Part009CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block079Part009SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block079Part009] using hcert

def TailChunk000Sub001Block079Part010SupportExplicit : Finset ℕ :=
  ([11543] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block079Part010 : ℚ :=
  (35638378375 : ℚ) / 1002130356805042176

def SurrogateDiagonalTailChunk000Sub001Block079Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11543
    = surrogateDiagTailX0RatChunk000Sub001Block079Part010

theorem surrogateDiagonalTailChunk000Sub001Block079Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block079Part010CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block079Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block079Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block079Part010CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block079Part010SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block079Part010] using hcert

def TailChunk000Sub001Block079Part011SupportExplicit : Finset ℕ :=
  ([11545] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block079Part011 : ℚ :=
  (666975260725 : ℚ) / 18163939309126975488

def SurrogateDiagonalTailChunk000Sub001Block079Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11545
    = surrogateDiagTailX0RatChunk000Sub001Block079Part011

theorem surrogateDiagonalTailChunk000Sub001Block079Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block079Part011CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block079Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block079Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block079Part011CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block079Part011SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block079Part011] using hcert

def TailChunk000Sub001Block079Part012SupportExplicit : Finset ℕ :=
  ([11546] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block079Part012 : ℚ :=
  (26242001019 : ℚ) / 30508183750000000

def SurrogateDiagonalTailChunk000Sub001Block079Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11546
    = surrogateDiagTailX0RatChunk000Sub001Block079Part012

theorem surrogateDiagonalTailChunk000Sub001Block079Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block079Part012CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block079Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block079Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block079Part012CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block079Part012SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block079Part012] using hcert

def TailChunk000Sub001Block079Part013SupportExplicit : Finset ℕ :=
  ([11549] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block079Part013 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block079Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11549
    = surrogateDiagTailX0RatChunk000Sub001Block079Part013

theorem surrogateDiagonalTailChunk000Sub001Block079Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block079Part013CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block079Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block079Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block079Part013CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block079Part013SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block079Part013] using hcert

def TailChunk000Sub001Block079Part014SupportExplicit : Finset ℕ :=
  ([11551] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block079Part014 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block079Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11551
    = surrogateDiagTailX0RatChunk000Sub001Block079Part014

theorem surrogateDiagonalTailChunk000Sub001Block079Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block079Part014CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block079Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block079Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block079Part014CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block079Part014SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block079Part014] using hcert

def TailChunk000Sub001Block079Part015SupportExplicit : Finset ℕ :=
  ([11553] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block079Part015 : ℚ :=
  (37061333549 : ℚ) / 175800358041000000

def SurrogateDiagonalTailChunk000Sub001Block079Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11553
    = surrogateDiagTailX0RatChunk000Sub001Block079Part015

theorem surrogateDiagonalTailChunk000Sub001Block079Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block079Part015CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block079Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block079Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block079Part015CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block079Part015SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block079Part015] using hcert

def TailChunk000Sub001Block079Part016SupportExplicit : Finset ℕ :=
  ([11554] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block079Part016 : ℚ :=
  (336768035275 : ℚ) / 414556763430371328

def SurrogateDiagonalTailChunk000Sub001Block079Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11554
    = surrogateDiagTailX0RatChunk000Sub001Block079Part016

theorem surrogateDiagonalTailChunk000Sub001Block079Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block079Part016CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block079Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block079Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block079Part016CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block079Part016SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block079Part016] using hcert

def TailChunk000Sub001Block079Part017SupportExplicit : Finset ℕ :=
  ([11555] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block079Part017 : ℚ :=
  (8908393723 : ℚ) / 243026414955878400

def SurrogateDiagonalTailChunk000Sub001Block079Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11555
    = surrogateDiagTailX0RatChunk000Sub001Block079Part017

theorem surrogateDiagonalTailChunk000Sub001Block079Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block079Part017CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block079Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block079Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block079Part017CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block079Part017SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block079Part017] using hcert

def TailChunk000Sub001Block079Part018SupportExplicit : Finset ℕ :=
  ([11557] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block079Part018 : ℚ :=
  (77222909725 : ℚ) / 1881899884660948992

def SurrogateDiagonalTailChunk000Sub001Block079Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11557
    = surrogateDiagTailX0RatChunk000Sub001Block079Part018

theorem surrogateDiagonalTailChunk000Sub001Block079Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block079Part018CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block079Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block079Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block079Part018CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block079Part018SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block079Part018] using hcert

def TailChunk000Sub001Block079Part019SupportExplicit : Finset ℕ :=
  ([11558] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block079Part019 : ℚ :=
  (521825640625 : ℚ) / 696750064498880082

def SurrogateDiagonalTailChunk000Sub001Block079Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11558
    = surrogateDiagTailX0RatChunk000Sub001Block079Part019

theorem surrogateDiagonalTailChunk000Sub001Block079Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block079Part019CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block079Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block079Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block079Part019CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block079Part019SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block079Part019] using hcert

def TailChunk000Sub001Block079Part020SupportExplicit : Finset ℕ :=
  ([11559] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block079Part020 : ℚ :=
  (927495896075 : ℚ) / 4404148555844772864

def SurrogateDiagonalTailChunk000Sub001Block079Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11559
    = surrogateDiagTailX0RatChunk000Sub001Block079Part020

theorem surrogateDiagonalTailChunk000Sub001Block079Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block079Part020CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block079Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block079Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block079Part020CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block079Part020SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block079Part020] using hcert

def TailChunk000Sub001Block079Part021SupportExplicit : Finset ℕ :=
  ([11561] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block079Part021 : ℚ :=
  (463176841 : ℚ) / 40524978375000000

def SurrogateDiagonalTailChunk000Sub001Block079Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11561
    = surrogateDiagTailX0RatChunk000Sub001Block079Part021

theorem surrogateDiagonalTailChunk000Sub001Block079Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block079Part021CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block079Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block079Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block079Part021CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block079Part021SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block079Part021] using hcert

def TailChunk000Sub001Block079Part022SupportExplicit : Finset ℕ :=
  ([11562] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block079Part022 : ℚ :=
  (17615632149 : ℚ) / 6114442569318400

def SurrogateDiagonalTailChunk000Sub001Block079Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11562
    = surrogateDiagTailX0RatChunk000Sub001Block079Part022

theorem surrogateDiagonalTailChunk000Sub001Block079Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block079Part022CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block079Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block079Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block079Part022CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block079Part022SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block079Part022] using hcert

def TailChunk000Sub001Block079Part023SupportExplicit : Finset ℕ :=
  ([11563] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block079Part023 : ℚ :=
  (540118211 : ℚ) / 172385653340620800

def SurrogateDiagonalTailChunk000Sub001Block079Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11563
    = surrogateDiagTailX0RatChunk000Sub001Block079Part023

theorem surrogateDiagonalTailChunk000Sub001Block079Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block079Part023CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block079Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block079Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block079Part023CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block079Part023SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block079Part023] using hcert

def TailChunk000Sub001Block079Part024SupportExplicit : Finset ℕ :=
  ([11566] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block079Part024 : ℚ :=
  (522548265625 : ℚ) / 698681456451230322

def SurrogateDiagonalTailChunk000Sub001Block079Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11566
    = surrogateDiagTailX0RatChunk000Sub001Block079Part024

theorem surrogateDiagonalTailChunk000Sub001Block079Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block079Part024CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block079Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block079Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block079Part024CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block079Part024SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block079Part024] using hcert

def surrogateDiagonalTailChunk000Sub001Block079HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block079Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block079Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block079Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block079Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block079Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block079Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block079Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block079Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block079Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block079Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block079Head : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block079Part000
    + surrogateDiagTailX0RatChunk000Sub001Block079Part001
    + surrogateDiagTailX0RatChunk000Sub001Block079Part002
    + surrogateDiagTailX0RatChunk000Sub001Block079Part003
    + surrogateDiagTailX0RatChunk000Sub001Block079Part004
    + surrogateDiagTailX0RatChunk000Sub001Block079Part005
    + surrogateDiagTailX0RatChunk000Sub001Block079Part006
    + surrogateDiagTailX0RatChunk000Sub001Block079Part007
    + surrogateDiagTailX0RatChunk000Sub001Block079Part008
    + surrogateDiagTailX0RatChunk000Sub001Block079Part009

def surrogateDiagonalTailChunk000Sub001Block079MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block079Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block079Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block079Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block079Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block079Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block079Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block079Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block079Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block079Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block079Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block079Mid : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block079Part010
    + surrogateDiagTailX0RatChunk000Sub001Block079Part011
    + surrogateDiagTailX0RatChunk000Sub001Block079Part012
    + surrogateDiagTailX0RatChunk000Sub001Block079Part013
    + surrogateDiagTailX0RatChunk000Sub001Block079Part014
    + surrogateDiagTailX0RatChunk000Sub001Block079Part015
    + surrogateDiagTailX0RatChunk000Sub001Block079Part016
    + surrogateDiagTailX0RatChunk000Sub001Block079Part017
    + surrogateDiagTailX0RatChunk000Sub001Block079Part018
    + surrogateDiagTailX0RatChunk000Sub001Block079Part019

def surrogateDiagonalTailChunk000Sub001Block079TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block079Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block079Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block079Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block079Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block079Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block079Tail : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block079Part020
    + surrogateDiagTailX0RatChunk000Sub001Block079Part021
    + surrogateDiagTailX0RatChunk000Sub001Block079Part022
    + surrogateDiagTailX0RatChunk000Sub001Block079Part023
    + surrogateDiagTailX0RatChunk000Sub001Block079Part024

def surrogateDiagonalTailChunk000Sub001Block079Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub001Block079HeadSum X0
    + surrogateDiagonalTailChunk000Sub001Block079MidSum X0
    + surrogateDiagonalTailChunk000Sub001Block079TailSum X0

def surrogateDiagTailX0RatChunk000Sub001Block079 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block079Part000
    + surrogateDiagTailX0RatChunk000Sub001Block079Part001
    + surrogateDiagTailX0RatChunk000Sub001Block079Part002
    + surrogateDiagTailX0RatChunk000Sub001Block079Part003
    + surrogateDiagTailX0RatChunk000Sub001Block079Part004
    + surrogateDiagTailX0RatChunk000Sub001Block079Part005
    + surrogateDiagTailX0RatChunk000Sub001Block079Part006
    + surrogateDiagTailX0RatChunk000Sub001Block079Part007
    + surrogateDiagTailX0RatChunk000Sub001Block079Part008
    + surrogateDiagTailX0RatChunk000Sub001Block079Part009
    + surrogateDiagTailX0RatChunk000Sub001Block079Part010
    + surrogateDiagTailX0RatChunk000Sub001Block079Part011
    + surrogateDiagTailX0RatChunk000Sub001Block079Part012
    + surrogateDiagTailX0RatChunk000Sub001Block079Part013
    + surrogateDiagTailX0RatChunk000Sub001Block079Part014
    + surrogateDiagTailX0RatChunk000Sub001Block079Part015
    + surrogateDiagTailX0RatChunk000Sub001Block079Part016
    + surrogateDiagTailX0RatChunk000Sub001Block079Part017
    + surrogateDiagTailX0RatChunk000Sub001Block079Part018
    + surrogateDiagTailX0RatChunk000Sub001Block079Part019
    + surrogateDiagTailX0RatChunk000Sub001Block079Part020
    + surrogateDiagTailX0RatChunk000Sub001Block079Part021
    + surrogateDiagTailX0RatChunk000Sub001Block079Part022
    + surrogateDiagTailX0RatChunk000Sub001Block079Part023
    + surrogateDiagTailX0RatChunk000Sub001Block079Part024

theorem surrogateDiagTailX0RatChunk000Sub001Block079_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk000Sub001Block079Head + surrogateDiagTailX0RatChunk000Sub001Block079Mid + surrogateDiagTailX0RatChunk000Sub001Block079Tail =
      surrogateDiagTailX0RatChunk000Sub001Block079 := by
  unfold surrogateDiagTailX0RatChunk000Sub001Block079Head surrogateDiagTailX0RatChunk000Sub001Block079Mid surrogateDiagTailX0RatChunk000Sub001Block079Tail surrogateDiagTailX0RatChunk000Sub001Block079
  ring

def SurrogateDiagonalTailChunk000Sub001Block079HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block079HeadSum X0 = surrogateDiagTailX0RatChunk000Sub001Block079Head

def SurrogateDiagonalTailChunk000Sub001Block079MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block079MidSum X0 = surrogateDiagTailX0RatChunk000Sub001Block079Mid

def SurrogateDiagonalTailChunk000Sub001Block079TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block079TailSum X0 = surrogateDiagTailX0RatChunk000Sub001Block079Tail

theorem surrogateDiagonalTailChunk000Sub001Block079_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk000Sub001Block079HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk000Sub001Block079MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk000Sub001Block079TailCertificateAt X0) :
    surrogateDiagonalTailChunk000Sub001Block079Sum X0 = surrogateDiagTailX0RatChunk000Sub001Block079 := by
  unfold SurrogateDiagonalTailChunk000Sub001Block079HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk000Sub001Block079MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk000Sub001Block079TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk000Sub001Block079Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk000Sub001Block079_eq_head_add_mid_add_tail

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

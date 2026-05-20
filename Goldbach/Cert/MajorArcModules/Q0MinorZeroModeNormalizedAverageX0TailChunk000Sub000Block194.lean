import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0TailPilot25

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

open scoped BigOperators

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

/- Generated direct-term certificate blocks for tail chunk 000, subchunk 000, blocks [194,195). -/

/-- Block 194 covers tail-support indices [4850,4875) and q from 8027 to 8065. -/

def TailChunk000Sub000Block194Part000SupportExplicit : Finset ℕ :=
  ([8027] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block194Part000 : ℚ :=
  (112553748475 : ℚ) / 8590818781994600448

def SurrogateDiagonalTailChunk000Sub000Block194Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8027
    = surrogateDiagTailX0RatChunk000Sub000Block194Part000

theorem surrogateDiagonalTailChunk000Sub000Block194Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block194Part000CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block194Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block194Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block194Part000CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block194Part000SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block194Part000] using hcert

def TailChunk000Sub000Block194Part001SupportExplicit : Finset ℕ :=
  ([8029] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block194Part001 : ℚ :=
  (717646751 : ℚ) / 6531653077401600

def SurrogateDiagonalTailChunk000Sub000Block194Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8029
    = surrogateDiagTailX0RatChunk000Sub000Block194Part001

theorem surrogateDiagonalTailChunk000Sub000Block194Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block194Part001CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block194Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block194Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block194Part001CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block194Part001SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block194Part001] using hcert

def TailChunk000Sub000Block194Part002SupportExplicit : Finset ℕ :=
  ([8030] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block194Part002 : ℚ :=
  (10349026417 : ℚ) / 2293694359142400

def SurrogateDiagonalTailChunk000Sub000Block194Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8030
    = surrogateDiagTailX0RatChunk000Sub000Block194Part002

theorem surrogateDiagonalTailChunk000Sub000Block194Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block194Part002CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block194Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block194Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block194Part002CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block194Part002SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block194Part002] using hcert

def TailChunk000Sub000Block194Part003SupportExplicit : Finset ℕ :=
  ([8031] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block194Part003 : ℚ :=
  (447783916475 : ℚ) / 1025796663760610304

def SurrogateDiagonalTailChunk000Sub000Block194Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8031
    = surrogateDiagTailX0RatChunk000Sub000Block194Part003

theorem surrogateDiagonalTailChunk000Sub000Block194Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block194Part003CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block194Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block194Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block194Part003CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block194Part003SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block194Part003] using hcert

def TailChunk000Sub000Block194Part004SupportExplicit : Finset ℕ :=
  ([8033] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block194Part004 : ℚ :=
  (13448062675 : ℚ) / 1274081684275298304

def SurrogateDiagonalTailChunk000Sub000Block194Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8033
    = surrogateDiagTailX0RatChunk000Sub000Block194Part004

theorem surrogateDiagonalTailChunk000Sub000Block194Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block194Part004CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block194Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block194Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block194Part004CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block194Part004SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block194Part004] using hcert

def TailChunk000Sub000Block194Part005SupportExplicit : Finset ℕ :=
  ([8034] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block194Part005 : ℚ :=
  (20024331175 : ℚ) / 2494422481379328

def SurrogateDiagonalTailChunk000Sub000Block194Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8034
    = surrogateDiagTailX0RatChunk000Sub000Block194Part005

theorem surrogateDiagonalTailChunk000Sub000Block194Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block194Part005CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block194Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block194Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block194Part005CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block194Part005SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block194Part005] using hcert

def TailChunk000Sub000Block194Part006SupportExplicit : Finset ℕ :=
  ([8035] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block194Part006 : ℚ :=
  (60582940775 : ℚ) / 532303106829179136

def SurrogateDiagonalTailChunk000Sub000Block194Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8035
    = surrogateDiagTailX0RatChunk000Sub000Block194Part006

theorem surrogateDiagonalTailChunk000Sub000Block194Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block194Part006CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block194Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block194Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block194Part006CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block194Part006SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block194Part006] using hcert

def TailChunk000Sub000Block194Part007SupportExplicit : Finset ℕ :=
  ([8038] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block194Part007 : ℚ :=
  (252380640625 : ℚ) / 162932078285287122

def SurrogateDiagonalTailChunk000Sub000Block194Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8038
    = surrogateDiagTailX0RatChunk000Sub000Block194Part007

theorem surrogateDiagonalTailChunk000Sub000Block194Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block194Part007CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block194Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block194Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block194Part007CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block194Part007SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block194Part007] using hcert

def TailChunk000Sub000Block194Part008SupportExplicit : Finset ℕ :=
  ([8039] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block194Part008 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub000Block194Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8039
    = surrogateDiagTailX0RatChunk000Sub000Block194Part008

theorem surrogateDiagonalTailChunk000Sub000Block194Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block194Part008CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block194Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block194Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block194Part008CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block194Part008SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block194Part008] using hcert

def TailChunk000Sub000Block194Part009SupportExplicit : Finset ℕ :=
  ([8041] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block194Part009 : ℚ :=
  (234193583 : ℚ) / 3237601502822400

def SurrogateDiagonalTailChunk000Sub000Block194Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8041
    = surrogateDiagTailX0RatChunk000Sub000Block194Part009

theorem surrogateDiagonalTailChunk000Sub000Block194Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block194Part009CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block194Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block194Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block194Part009CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block194Part009SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block194Part009] using hcert

def TailChunk000Sub000Block194Part010SupportExplicit : Finset ℕ :=
  ([8042] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block194Part010 : ℚ :=
  (404211025 : ℚ) / 261210759865632

def SurrogateDiagonalTailChunk000Sub000Block194Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8042
    = surrogateDiagTailX0RatChunk000Sub000Block194Part010

theorem surrogateDiagonalTailChunk000Sub000Block194Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block194Part010CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block194Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block194Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block194Part010CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block194Part010SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block194Part010] using hcert

def TailChunk000Sub000Block194Part011SupportExplicit : Finset ℕ :=
  ([8043] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block194Part011 : ℚ :=
  (870030840325 : ℚ) / 1104092080409069568

def SurrogateDiagonalTailChunk000Sub000Block194Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8043
    = surrogateDiagTailX0RatChunk000Sub000Block194Part011

theorem surrogateDiagonalTailChunk000Sub000Block194Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block194Part011CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block194Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block194Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block194Part011CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block194Part011SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block194Part011] using hcert

def TailChunk000Sub000Block194Part012SupportExplicit : Finset ℕ :=
  ([8045] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block194Part012 : ℚ :=
  (242934146525 : ℚ) / 2139838544819257344

def SurrogateDiagonalTailChunk000Sub000Block194Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8045
    = surrogateDiagTailX0RatChunk000Sub000Block194Part012

theorem surrogateDiagonalTailChunk000Sub000Block194Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block194Part012CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block194Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block194Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block194Part012CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block194Part012SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block194Part012] using hcert

def TailChunk000Sub000Block194Part013SupportExplicit : Finset ℕ :=
  ([8047] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block194Part013 : ℚ :=
  (1350325825 : ℚ) / 52522241387167872

def SurrogateDiagonalTailChunk000Sub000Block194Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8047
    = surrogateDiagTailX0RatChunk000Sub000Block194Part013

theorem surrogateDiagonalTailChunk000Sub000Block194Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block194Part013CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block194Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block194Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block194Part013CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block194Part013SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block194Part013] using hcert

def TailChunk000Sub000Block194Part014SupportExplicit : Finset ℕ :=
  ([8049] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block194Part014 : ℚ :=
  (449792764325 : ℚ) / 1035027621719037504

def SurrogateDiagonalTailChunk000Sub000Block194Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8049
    = surrogateDiagTailX0RatChunk000Sub000Block194Part014

theorem surrogateDiagonalTailChunk000Sub000Block194Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block194Part014CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block194Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block194Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block194Part014CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block194Part014SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block194Part014] using hcert

def TailChunk000Sub000Block194Part015SupportExplicit : Finset ℕ :=
  ([8051] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block194Part015 : ℚ :=
  (6896034425 : ℚ) / 1200265197404553216

def SurrogateDiagonalTailChunk000Sub000Block194Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8051
    = surrogateDiagTailX0RatChunk000Sub000Block194Part015

theorem surrogateDiagonalTailChunk000Sub000Block194Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block194Part015CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block194Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block194Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block194Part015CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block194Part015SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block194Part015] using hcert

def TailChunk000Sub000Block194Part016SupportExplicit : Finset ℕ :=
  ([8053] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block194Part016 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub000Block194Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8053
    = surrogateDiagTailX0RatChunk000Sub000Block194Part016

theorem surrogateDiagonalTailChunk000Sub000Block194Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block194Part016CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block194Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block194Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block194Part016CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block194Part016SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block194Part016] using hcert

def TailChunk000Sub000Block194Part017SupportExplicit : Finset ℕ :=
  ([8054] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block194Part017 : ℚ :=
  (253386390625 : ℚ) / 164233576192819122

def SurrogateDiagonalTailChunk000Sub000Block194Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8054
    = surrogateDiagTailX0RatChunk000Sub000Block194Part017

theorem surrogateDiagonalTailChunk000Sub000Block194Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block194Part017CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block194Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block194Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block194Part017CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block194Part017SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block194Part017] using hcert

def TailChunk000Sub000Block194Part018SupportExplicit : Finset ℕ :=
  ([8057] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block194Part018 : ℚ :=
  (13292042893 : ℚ) / 226716544242000000

def SurrogateDiagonalTailChunk000Sub000Block194Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8057
    = surrogateDiagTailX0RatChunk000Sub000Block194Part018

theorem surrogateDiagonalTailChunk000Sub000Block194Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block194Part018CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block194Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block194Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block194Part018CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block194Part018SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block194Part018] using hcert

def TailChunk000Sub000Block194Part019SupportExplicit : Finset ℕ :=
  ([8058] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block194Part019 : ℚ :=
  (736659448825 : ℚ) / 97052154950320128

def SurrogateDiagonalTailChunk000Sub000Block194Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8058
    = surrogateDiagTailX0RatChunk000Sub000Block194Part019

theorem surrogateDiagonalTailChunk000Sub000Block194Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block194Part019CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block194Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block194Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block194Part019CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block194Part019SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block194Part019] using hcert

def TailChunk000Sub000Block194Part020SupportExplicit : Finset ℕ :=
  ([8059] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block194Part020 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub000Block194Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8059
    = surrogateDiagTailX0RatChunk000Sub000Block194Part020

theorem surrogateDiagonalTailChunk000Sub000Block194Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block194Part020CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block194Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block194Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block194Part020CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block194Part020SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block194Part020] using hcert

def TailChunk000Sub000Block194Part021SupportExplicit : Finset ℕ :=
  ([8061] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block194Part021 : ℚ :=
  (225768685175 : ℚ) / 1041216110446092864

def SurrogateDiagonalTailChunk000Sub000Block194Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8061
    = surrogateDiagTailX0RatChunk000Sub000Block194Part021

theorem surrogateDiagonalTailChunk000Sub000Block194Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block194Part021CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block194Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block194Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block194Part021CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block194Part021SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block194Part021] using hcert

def TailChunk000Sub000Block194Part022SupportExplicit : Finset ℕ :=
  ([8062] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block194Part022 : ℚ :=
  (12144179675 : ℚ) / 6881614035437568

def SurrogateDiagonalTailChunk000Sub000Block194Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8062
    = surrogateDiagTailX0RatChunk000Sub000Block194Part022

theorem surrogateDiagonalTailChunk000Sub000Block194Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block194Part022CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block194Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block194Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block194Part022CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block194Part022SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block194Part022] using hcert

def TailChunk000Sub000Block194Part023SupportExplicit : Finset ℕ :=
  ([8063] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block194Part023 : ℚ :=
  (815440369 : ℚ) / 28716478044779520

def SurrogateDiagonalTailChunk000Sub000Block194Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8063
    = surrogateDiagTailX0RatChunk000Sub000Block194Part023

theorem surrogateDiagonalTailChunk000Sub000Block194Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block194Part023CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block194Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block194Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block194Part023CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block194Part023SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block194Part023] using hcert

def TailChunk000Sub000Block194Part024SupportExplicit : Finset ℕ :=
  ([8065] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block194Part024 : ℚ :=
  (1543802927825 : ℚ) / 2161210049958395904

def SurrogateDiagonalTailChunk000Sub000Block194Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8065
    = surrogateDiagTailX0RatChunk000Sub000Block194Part024

theorem surrogateDiagonalTailChunk000Sub000Block194Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block194Part024CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block194Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block194Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block194Part024CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block194Part024SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block194Part024] using hcert

def surrogateDiagonalTailChunk000Sub000Block194HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block194Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block194Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block194Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block194Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block194Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block194Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block194Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block194Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block194Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block194Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block194Head : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block194Part000
    + surrogateDiagTailX0RatChunk000Sub000Block194Part001
    + surrogateDiagTailX0RatChunk000Sub000Block194Part002
    + surrogateDiagTailX0RatChunk000Sub000Block194Part003
    + surrogateDiagTailX0RatChunk000Sub000Block194Part004
    + surrogateDiagTailX0RatChunk000Sub000Block194Part005
    + surrogateDiagTailX0RatChunk000Sub000Block194Part006
    + surrogateDiagTailX0RatChunk000Sub000Block194Part007
    + surrogateDiagTailX0RatChunk000Sub000Block194Part008
    + surrogateDiagTailX0RatChunk000Sub000Block194Part009

def surrogateDiagonalTailChunk000Sub000Block194MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block194Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block194Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block194Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block194Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block194Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block194Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block194Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block194Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block194Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block194Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block194Mid : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block194Part010
    + surrogateDiagTailX0RatChunk000Sub000Block194Part011
    + surrogateDiagTailX0RatChunk000Sub000Block194Part012
    + surrogateDiagTailX0RatChunk000Sub000Block194Part013
    + surrogateDiagTailX0RatChunk000Sub000Block194Part014
    + surrogateDiagTailX0RatChunk000Sub000Block194Part015
    + surrogateDiagTailX0RatChunk000Sub000Block194Part016
    + surrogateDiagTailX0RatChunk000Sub000Block194Part017
    + surrogateDiagTailX0RatChunk000Sub000Block194Part018
    + surrogateDiagTailX0RatChunk000Sub000Block194Part019

def surrogateDiagonalTailChunk000Sub000Block194TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block194Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block194Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block194Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block194Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block194Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block194Tail : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block194Part020
    + surrogateDiagTailX0RatChunk000Sub000Block194Part021
    + surrogateDiagTailX0RatChunk000Sub000Block194Part022
    + surrogateDiagTailX0RatChunk000Sub000Block194Part023
    + surrogateDiagTailX0RatChunk000Sub000Block194Part024

def surrogateDiagonalTailChunk000Sub000Block194Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub000Block194HeadSum X0
    + surrogateDiagonalTailChunk000Sub000Block194MidSum X0
    + surrogateDiagonalTailChunk000Sub000Block194TailSum X0

def surrogateDiagTailX0RatChunk000Sub000Block194 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block194Part000
    + surrogateDiagTailX0RatChunk000Sub000Block194Part001
    + surrogateDiagTailX0RatChunk000Sub000Block194Part002
    + surrogateDiagTailX0RatChunk000Sub000Block194Part003
    + surrogateDiagTailX0RatChunk000Sub000Block194Part004
    + surrogateDiagTailX0RatChunk000Sub000Block194Part005
    + surrogateDiagTailX0RatChunk000Sub000Block194Part006
    + surrogateDiagTailX0RatChunk000Sub000Block194Part007
    + surrogateDiagTailX0RatChunk000Sub000Block194Part008
    + surrogateDiagTailX0RatChunk000Sub000Block194Part009
    + surrogateDiagTailX0RatChunk000Sub000Block194Part010
    + surrogateDiagTailX0RatChunk000Sub000Block194Part011
    + surrogateDiagTailX0RatChunk000Sub000Block194Part012
    + surrogateDiagTailX0RatChunk000Sub000Block194Part013
    + surrogateDiagTailX0RatChunk000Sub000Block194Part014
    + surrogateDiagTailX0RatChunk000Sub000Block194Part015
    + surrogateDiagTailX0RatChunk000Sub000Block194Part016
    + surrogateDiagTailX0RatChunk000Sub000Block194Part017
    + surrogateDiagTailX0RatChunk000Sub000Block194Part018
    + surrogateDiagTailX0RatChunk000Sub000Block194Part019
    + surrogateDiagTailX0RatChunk000Sub000Block194Part020
    + surrogateDiagTailX0RatChunk000Sub000Block194Part021
    + surrogateDiagTailX0RatChunk000Sub000Block194Part022
    + surrogateDiagTailX0RatChunk000Sub000Block194Part023
    + surrogateDiagTailX0RatChunk000Sub000Block194Part024

theorem surrogateDiagTailX0RatChunk000Sub000Block194_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk000Sub000Block194Head + surrogateDiagTailX0RatChunk000Sub000Block194Mid + surrogateDiagTailX0RatChunk000Sub000Block194Tail =
      surrogateDiagTailX0RatChunk000Sub000Block194 := by
  unfold surrogateDiagTailX0RatChunk000Sub000Block194Head surrogateDiagTailX0RatChunk000Sub000Block194Mid surrogateDiagTailX0RatChunk000Sub000Block194Tail surrogateDiagTailX0RatChunk000Sub000Block194
  ring

def SurrogateDiagonalTailChunk000Sub000Block194HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block194HeadSum X0 = surrogateDiagTailX0RatChunk000Sub000Block194Head

def SurrogateDiagonalTailChunk000Sub000Block194MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block194MidSum X0 = surrogateDiagTailX0RatChunk000Sub000Block194Mid

def SurrogateDiagonalTailChunk000Sub000Block194TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block194TailSum X0 = surrogateDiagTailX0RatChunk000Sub000Block194Tail

theorem surrogateDiagonalTailChunk000Sub000Block194_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk000Sub000Block194HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk000Sub000Block194MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk000Sub000Block194TailCertificateAt X0) :
    surrogateDiagonalTailChunk000Sub000Block194Sum X0 = surrogateDiagTailX0RatChunk000Sub000Block194 := by
  unfold SurrogateDiagonalTailChunk000Sub000Block194HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk000Sub000Block194MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk000Sub000Block194TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk000Sub000Block194Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk000Sub000Block194_eq_head_add_mid_add_tail

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

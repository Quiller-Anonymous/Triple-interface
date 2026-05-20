import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0TailPilot25

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

open scoped BigOperators

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

/- Generated direct-term certificate blocks for tail chunk 000, subchunk 000, blocks [114,115). -/

/- Block 114 covers tail-support indices [2850,2875) and q from 4737 to 4777. -/

def TailChunk000Sub000Block114Part000SupportExplicit : Finset ℕ :=
  ([4737] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block114Part000 : ℚ :=
  (31146875 : ℚ) / 8267357769408

def SurrogateDiagonalTailChunk000Sub000Block114Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4737
    = surrogateDiagTailX0RatChunk000Sub000Block114Part000

theorem surrogateDiagonalTailChunk000Sub000Block114Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block114Part000CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block114Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block114Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block114Part000CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block114Part000SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block114Part000] using hcert

def TailChunk000Sub000Block114Part001SupportExplicit : Finset ℕ :=
  ([4738] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block114Part001 : ℚ :=
  (666286125475 : ℚ) / 63404235329643648

def SurrogateDiagonalTailChunk000Sub000Block114Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4738
    = surrogateDiagTailX0RatChunk000Sub000Block114Part001

theorem surrogateDiagonalTailChunk000Sub000Block114Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block114Part001CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block114Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block114Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block114Part001CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block114Part001SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block114Part001] using hcert

def TailChunk000Sub000Block114Part002SupportExplicit : Finset ℕ :=
  ([4739] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block114Part002 : ℚ :=
  (66759672175 : ℚ) / 37596389398004736

def SurrogateDiagonalTailChunk000Sub000Block114Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4739
    = surrogateDiagTailX0RatChunk000Sub000Block114Part002

theorem surrogateDiagonalTailChunk000Sub000Block114Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block114Part002CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block114Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block114Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block114Part002CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block114Part002SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block114Part002] using hcert

def TailChunk000Sub000Block114Part003SupportExplicit : Finset ℕ :=
  ([4741] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block114Part003 : ℚ :=
  (2549126723 : ℚ) / 1709742380100000

def SurrogateDiagonalTailChunk000Sub000Block114Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4741
    = surrogateDiagTailX0RatChunk000Sub000Block114Part003

theorem surrogateDiagonalTailChunk000Sub000Block114Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block114Part003CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block114Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block114Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block114Part003CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block114Part003SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block114Part003] using hcert

def TailChunk000Sub000Block114Part004SupportExplicit : Finset ℕ :=
  ([4742] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block114Part004 : ℚ :=
  (28102583359 : ℚ) / 3155587552312200

def SurrogateDiagonalTailChunk000Sub000Block114Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4742
    = surrogateDiagTailX0RatChunk000Sub000Block114Part004

theorem surrogateDiagonalTailChunk000Sub000Block114Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block114Part004CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block114Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block114Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block114Part004CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block114Part004SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block114Part004] using hcert

def TailChunk000Sub000Block114Part005SupportExplicit : Finset ℕ :=
  ([4745] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block114Part005 : ℚ :=
  (1078054379725 : ℚ) / 356715346733826048

def SurrogateDiagonalTailChunk000Sub000Block114Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4745
    = surrogateDiagTailX0RatChunk000Sub000Block114Part005

theorem surrogateDiagonalTailChunk000Sub000Block114Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block114Part005CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block114Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block114Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block114Part005CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block114Part005SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block114Part005] using hcert

def TailChunk000Sub000Block114Part006SupportExplicit : Finset ℕ :=
  ([4746] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block114Part006 : ℚ :=
  (480425 : ℚ) / 9710862336

def SurrogateDiagonalTailChunk000Sub000Block114Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4746
    = surrogateDiagTailX0RatChunk000Sub000Block114Part006

theorem surrogateDiagonalTailChunk000Sub000Block114Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block114Part006CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block114Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block114Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block114Part006CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block114Part006SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block114Part006] using hcert

def TailChunk000Sub000Block114Part007SupportExplicit : Finset ℕ :=
  ([4747] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block114Part007 : ℚ :=
  (10940692637 : ℚ) / 8956702982400000

def SurrogateDiagonalTailChunk000Sub000Block114Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4747
    = surrogateDiagTailX0RatChunk000Sub000Block114Part007

theorem surrogateDiagonalTailChunk000Sub000Block114Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block114Part007CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block114Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block114Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block114Part007CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block114Part007SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block114Part007] using hcert

def TailChunk000Sub000Block114Part008SupportExplicit : Finset ℕ :=
  ([4749] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block114Part008 : ℚ :=
  (1095754227175 : ℚ) / 250595205826401408

def SurrogateDiagonalTailChunk000Sub000Block114Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4749
    = surrogateDiagTailX0RatChunk000Sub000Block114Part008

theorem surrogateDiagonalTailChunk000Sub000Block114Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block114Part008CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block114Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block114Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block114Part008CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block114Part008SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block114Part008] using hcert

def TailChunk000Sub000Block114Part009SupportExplicit : Finset ℕ :=
  ([4751] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block114Part009 : ℚ :=
  (22572001 : ℚ) / 20366728781250

def SurrogateDiagonalTailChunk000Sub000Block114Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4751
    = surrogateDiagTailX0RatChunk000Sub000Block114Part009

theorem surrogateDiagonalTailChunk000Sub000Block114Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block114Part009CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block114Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block114Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block114Part009CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block114Part009SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block114Part009] using hcert

def TailChunk000Sub000Block114Part010SupportExplicit : Finset ℕ :=
  ([4754] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block114Part010 : ℚ :=
  (706124871775 : ℚ) / 79691610588530688

def SurrogateDiagonalTailChunk000Sub000Block114Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4754
    = surrogateDiagTailX0RatChunk000Sub000Block114Part010

theorem surrogateDiagonalTailChunk000Sub000Block114Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block114Part010CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block114Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block114Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block114Part010CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block114Part010SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block114Part010] using hcert

def TailChunk000Sub000Block114Part011SupportExplicit : Finset ℕ :=
  ([4755] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block114Part011 : ℚ :=
  (258842261025 : ℚ) / 34041907132235776

def SurrogateDiagonalTailChunk000Sub000Block114Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4755
    = surrogateDiagTailX0RatChunk000Sub000Block114Part011

theorem surrogateDiagonalTailChunk000Sub000Block114Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block114Part011CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block114Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block114Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block114Part011CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block114Part011SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block114Part011] using hcert

def TailChunk000Sub000Block114Part012SupportExplicit : Finset ℕ :=
  ([4757] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block114Part012 : ℚ :=
  (3057512737 : ℚ) / 2531525155790400

def SurrogateDiagonalTailChunk000Sub000Block114Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4757
    = surrogateDiagTailX0RatChunk000Sub000Block114Part012

theorem surrogateDiagonalTailChunk000Sub000Block114Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block114Part012CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block114Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block114Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block114Part012CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block114Part012SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block114Part012] using hcert

def TailChunk000Sub000Block114Part013SupportExplicit : Finset ℕ :=
  ([4758] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block114Part013 : ℚ :=
  (17209663507 : ℚ) / 430067692339200

def SurrogateDiagonalTailChunk000Sub000Block114Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4758
    = surrogateDiagTailX0RatChunk000Sub000Block114Part013

theorem surrogateDiagonalTailChunk000Sub000Block114Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block114Part013CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block114Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block114Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block114Part013CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block114Part013SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block114Part013] using hcert

def TailChunk000Sub000Block114Part014SupportExplicit : Finset ℕ :=
  ([4759] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block114Part014 : ℚ :=
  (353876265625 : ℚ) / 320379425561307762

def SurrogateDiagonalTailChunk000Sub000Block114Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4759
    = surrogateDiagTailX0RatChunk000Sub000Block114Part014

theorem surrogateDiagonalTailChunk000Sub000Block114Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block114Part014CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block114Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block114Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block114Part014CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block114Part014SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block114Part014] using hcert

def TailChunk000Sub000Block114Part015SupportExplicit : Finset ℕ :=
  ([4762] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block114Part015 : ℚ :=
  (17007483 : ℚ) / 1284187452800

def SurrogateDiagonalTailChunk000Sub000Block114Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4762
    = surrogateDiagTailX0RatChunk000Sub000Block114Part015

theorem surrogateDiagonalTailChunk000Sub000Block114Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block114Part015CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block114Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block114Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block114Part015CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block114Part015SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block114Part015] using hcert

def TailChunk000Sub000Block114Part016SupportExplicit : Finset ℕ :=
  ([4763] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block114Part016 : ℚ :=
  (109013837 : ℚ) / 38706092310528

def SurrogateDiagonalTailChunk000Sub000Block114Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4763
    = surrogateDiagTailX0RatChunk000Sub000Block114Part016

theorem surrogateDiagonalTailChunk000Sub000Block114Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block114Part016CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block114Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block114Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block114Part016CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block114Part016SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block114Part016] using hcert

def TailChunk000Sub000Block114Part017SupportExplicit : Finset ℕ :=
  ([4765] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block114Part017 : ℚ :=
  (567178287875 : ℚ) / 262896389697306624

def SurrogateDiagonalTailChunk000Sub000Block114Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4765
    = surrogateDiagTailX0RatChunk000Sub000Block114Part017

theorem surrogateDiagonalTailChunk000Sub000Block114Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block114Part017CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block114Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block114Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block114Part017CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block114Part017SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block114Part017] using hcert

def TailChunk000Sub000Block114Part018SupportExplicit : Finset ℕ :=
  ([4766] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block114Part018 : ℚ :=
  (709694157775 : ℚ) / 80499630601218888

def SurrogateDiagonalTailChunk000Sub000Block114Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4766
    = surrogateDiagTailX0RatChunk000Sub000Block114Part018

theorem surrogateDiagonalTailChunk000Sub000Block114Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block114Part018CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block114Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block114Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block114Part018CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block114Part018SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block114Part018] using hcert

def TailChunk000Sub000Block114Part019SupportExplicit : Finset ℕ :=
  ([4767] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block114Part019 : ℚ :=
  (405766971425 : ℚ) / 67632525354230784

def SurrogateDiagonalTailChunk000Sub000Block114Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4767
    = surrogateDiagTailX0RatChunk000Sub000Block114Part019

theorem surrogateDiagonalTailChunk000Sub000Block114Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block114Part019CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block114Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block114Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block114Part019CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block114Part019SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block114Part019] using hcert

def TailChunk000Sub000Block114Part020SupportExplicit : Finset ℕ :=
  ([4769] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block114Part020 : ℚ :=
  (6709031537 : ℚ) / 5126806406250000

def SurrogateDiagonalTailChunk000Sub000Block114Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4769
    = surrogateDiagTailX0RatChunk000Sub000Block114Part020

theorem surrogateDiagonalTailChunk000Sub000Block114Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block114Part020CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block114Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block114Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block114Part020CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block114Part020SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block114Part020] using hcert

def TailChunk000Sub000Block114Part021SupportExplicit : Finset ℕ :=
  ([4771] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block114Part021 : ℚ :=
  (1318448854375 : ℚ) / 930413888650856448

def SurrogateDiagonalTailChunk000Sub000Block114Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4771
    = surrogateDiagTailX0RatChunk000Sub000Block114Part021

theorem surrogateDiagonalTailChunk000Sub000Block114Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block114Part021CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block114Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block114Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block114Part021CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block114Part021SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block114Part021] using hcert

def TailChunk000Sub000Block114Part022SupportExplicit : Finset ℕ :=
  ([4773] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block114Part022 : ℚ :=
  (837425 : ℚ) / 193572384768

def SurrogateDiagonalTailChunk000Sub000Block114Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4773
    = surrogateDiagTailX0RatChunk000Sub000Block114Part022

theorem surrogateDiagonalTailChunk000Sub000Block114Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block114Part022CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block114Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block114Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block114Part022CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block114Part022SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block114Part022] using hcert

def TailChunk000Sub000Block114Part023SupportExplicit : Finset ℕ :=
  ([4774] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block114Part023 : ℚ :=
  (480361553 : ℚ) / 23332665600000

def SurrogateDiagonalTailChunk000Sub000Block114Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4774
    = surrogateDiagTailX0RatChunk000Sub000Block114Part023

theorem surrogateDiagonalTailChunk000Sub000Block114Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block114Part023CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block114Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block114Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block114Part023CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block114Part023SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block114Part023] using hcert

def TailChunk000Sub000Block114Part024SupportExplicit : Finset ℕ :=
  ([4777] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block114Part024 : ℚ :=
  (53717947807 : ℚ) / 40290152035123200

def SurrogateDiagonalTailChunk000Sub000Block114Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4777
    = surrogateDiagTailX0RatChunk000Sub000Block114Part024

theorem surrogateDiagonalTailChunk000Sub000Block114Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block114Part024CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block114Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block114Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block114Part024CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block114Part024SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block114Part024] using hcert

def surrogateDiagonalTailChunk000Sub000Block114HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block114Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block114Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block114Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block114Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block114Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block114Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block114Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block114Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block114Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block114Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block114Head : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block114Part000
    + surrogateDiagTailX0RatChunk000Sub000Block114Part001
    + surrogateDiagTailX0RatChunk000Sub000Block114Part002
    + surrogateDiagTailX0RatChunk000Sub000Block114Part003
    + surrogateDiagTailX0RatChunk000Sub000Block114Part004
    + surrogateDiagTailX0RatChunk000Sub000Block114Part005
    + surrogateDiagTailX0RatChunk000Sub000Block114Part006
    + surrogateDiagTailX0RatChunk000Sub000Block114Part007
    + surrogateDiagTailX0RatChunk000Sub000Block114Part008
    + surrogateDiagTailX0RatChunk000Sub000Block114Part009

def surrogateDiagonalTailChunk000Sub000Block114MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block114Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block114Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block114Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block114Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block114Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block114Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block114Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block114Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block114Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block114Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block114Mid : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block114Part010
    + surrogateDiagTailX0RatChunk000Sub000Block114Part011
    + surrogateDiagTailX0RatChunk000Sub000Block114Part012
    + surrogateDiagTailX0RatChunk000Sub000Block114Part013
    + surrogateDiagTailX0RatChunk000Sub000Block114Part014
    + surrogateDiagTailX0RatChunk000Sub000Block114Part015
    + surrogateDiagTailX0RatChunk000Sub000Block114Part016
    + surrogateDiagTailX0RatChunk000Sub000Block114Part017
    + surrogateDiagTailX0RatChunk000Sub000Block114Part018
    + surrogateDiagTailX0RatChunk000Sub000Block114Part019

def surrogateDiagonalTailChunk000Sub000Block114TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block114Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block114Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block114Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block114Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block114Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block114Tail : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block114Part020
    + surrogateDiagTailX0RatChunk000Sub000Block114Part021
    + surrogateDiagTailX0RatChunk000Sub000Block114Part022
    + surrogateDiagTailX0RatChunk000Sub000Block114Part023
    + surrogateDiagTailX0RatChunk000Sub000Block114Part024

def surrogateDiagonalTailChunk000Sub000Block114Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub000Block114HeadSum X0
    + surrogateDiagonalTailChunk000Sub000Block114MidSum X0
    + surrogateDiagonalTailChunk000Sub000Block114TailSum X0

def surrogateDiagTailX0RatChunk000Sub000Block114 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block114Part000
    + surrogateDiagTailX0RatChunk000Sub000Block114Part001
    + surrogateDiagTailX0RatChunk000Sub000Block114Part002
    + surrogateDiagTailX0RatChunk000Sub000Block114Part003
    + surrogateDiagTailX0RatChunk000Sub000Block114Part004
    + surrogateDiagTailX0RatChunk000Sub000Block114Part005
    + surrogateDiagTailX0RatChunk000Sub000Block114Part006
    + surrogateDiagTailX0RatChunk000Sub000Block114Part007
    + surrogateDiagTailX0RatChunk000Sub000Block114Part008
    + surrogateDiagTailX0RatChunk000Sub000Block114Part009
    + surrogateDiagTailX0RatChunk000Sub000Block114Part010
    + surrogateDiagTailX0RatChunk000Sub000Block114Part011
    + surrogateDiagTailX0RatChunk000Sub000Block114Part012
    + surrogateDiagTailX0RatChunk000Sub000Block114Part013
    + surrogateDiagTailX0RatChunk000Sub000Block114Part014
    + surrogateDiagTailX0RatChunk000Sub000Block114Part015
    + surrogateDiagTailX0RatChunk000Sub000Block114Part016
    + surrogateDiagTailX0RatChunk000Sub000Block114Part017
    + surrogateDiagTailX0RatChunk000Sub000Block114Part018
    + surrogateDiagTailX0RatChunk000Sub000Block114Part019
    + surrogateDiagTailX0RatChunk000Sub000Block114Part020
    + surrogateDiagTailX0RatChunk000Sub000Block114Part021
    + surrogateDiagTailX0RatChunk000Sub000Block114Part022
    + surrogateDiagTailX0RatChunk000Sub000Block114Part023
    + surrogateDiagTailX0RatChunk000Sub000Block114Part024

theorem surrogateDiagTailX0RatChunk000Sub000Block114_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk000Sub000Block114Head + surrogateDiagTailX0RatChunk000Sub000Block114Mid + surrogateDiagTailX0RatChunk000Sub000Block114Tail =
      surrogateDiagTailX0RatChunk000Sub000Block114 := by
  unfold surrogateDiagTailX0RatChunk000Sub000Block114Head surrogateDiagTailX0RatChunk000Sub000Block114Mid surrogateDiagTailX0RatChunk000Sub000Block114Tail surrogateDiagTailX0RatChunk000Sub000Block114
  ring

def SurrogateDiagonalTailChunk000Sub000Block114HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block114HeadSum X0 = surrogateDiagTailX0RatChunk000Sub000Block114Head

def SurrogateDiagonalTailChunk000Sub000Block114MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block114MidSum X0 = surrogateDiagTailX0RatChunk000Sub000Block114Mid

def SurrogateDiagonalTailChunk000Sub000Block114TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block114TailSum X0 = surrogateDiagTailX0RatChunk000Sub000Block114Tail

theorem surrogateDiagonalTailChunk000Sub000Block114_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk000Sub000Block114HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk000Sub000Block114MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk000Sub000Block114TailCertificateAt X0) :
    surrogateDiagonalTailChunk000Sub000Block114Sum X0 = surrogateDiagTailX0RatChunk000Sub000Block114 := by
  unfold SurrogateDiagonalTailChunk000Sub000Block114HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk000Sub000Block114MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk000Sub000Block114TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk000Sub000Block114Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk000Sub000Block114_eq_head_add_mid_add_tail

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

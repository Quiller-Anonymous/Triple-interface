import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0TailPilot25

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

open scoped BigOperators

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

/- Generated direct-term certificate blocks for tail chunk 001, subchunk 001, blocks [80,90). -/

/-- Block 080 covers tail-support indices [17000,17025) and q from 28011 to 28055. -/

def TailChunk001Sub001Block080Part000SupportExplicit : Finset ℕ :=
  ([28011] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block080Part000 : ℚ :=
  (21790848066325 : ℚ) / 303941647835244822528

def SurrogateDiagonalTailChunk001Sub001Block080Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28011
    = surrogateDiagTailX0RatChunk001Sub001Block080Part000

theorem surrogateDiagonalTailChunk001Sub001Block080Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block080Part000CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block080Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block080Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block080Part000CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block080Part000SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block080Part000] using hcert

def TailChunk001Sub001Block080Part001SupportExplicit : Finset ℕ :=
  ([28013] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block080Part001 : ℚ :=
  (11971370533375 : ℚ) / 365276515055437873152

def SurrogateDiagonalTailChunk001Sub001Block080Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28013
    = surrogateDiagTailX0RatChunk001Sub001Block080Part001

theorem surrogateDiagonalTailChunk001Sub001Block080Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block080Part001CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block080Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block080Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block080Part001CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block080Part001SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block080Part001] using hcert

def TailChunk001Sub001Block080Part002SupportExplicit : Finset ℕ :=
  ([28014] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block080Part002 : ℚ :=
  (138966612325 : ℚ) / 266634695265878016

def SurrogateDiagonalTailChunk001Sub001Block080Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28014
    = surrogateDiagTailX0RatChunk001Sub001Block080Part002

theorem surrogateDiagonalTailChunk001Sub001Block080Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block080Part002CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block080Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block080Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block080Part002CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block080Part002SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block080Part002] using hcert

def TailChunk001Sub001Block080Part003SupportExplicit : Finset ℕ :=
  ([28015] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block080Part003 : ℚ :=
  (1077129459799 : ℚ) / 18152047612801843200

def SurrogateDiagonalTailChunk001Sub001Block080Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28015
    = surrogateDiagTailX0RatChunk001Sub001Block080Part003

theorem surrogateDiagonalTailChunk001Sub001Block080Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block080Part003CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block080Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block080Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block080Part003CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block080Part003SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block080Part003] using hcert

def TailChunk001Sub001Block080Part004SupportExplicit : Finset ℕ :=
  ([28018] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block080Part004 : ℚ :=
  (3066438765625 : ℚ) / 24069740043334144512

def SurrogateDiagonalTailChunk001Sub001Block080Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28018
    = surrogateDiagTailX0RatChunk001Sub001Block080Part004

theorem surrogateDiagonalTailChunk001Sub001Block080Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block080Part004CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block080Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block080Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block080Part004CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block080Part004SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block080Part004] using hcert

def TailChunk001Sub001Block080Part005SupportExplicit : Finset ℕ :=
  ([28019] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block080Part005 : ℚ :=
  (12266630640625 : ℚ) / 385225822726899271122

def SurrogateDiagonalTailChunk001Sub001Block080Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28019
    = surrogateDiagTailX0RatChunk001Sub001Block080Part005

theorem surrogateDiagonalTailChunk001Sub001Block080Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block080Part005CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block080Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block080Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block080Part005CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block080Part005SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block080Part005] using hcert

def TailChunk001Sub001Block080Part006SupportExplicit : Finset ℕ :=
  ([28021] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block080Part006 : ℚ :=
  (37041280147225 : ℚ) / 831266344599686794368

def SurrogateDiagonalTailChunk001Sub001Block080Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28021
    = surrogateDiagTailX0RatChunk001Sub001Block080Part006

theorem surrogateDiagonalTailChunk001Sub001Block080Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block080Part006CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block080Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block080Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block080Part006CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block080Part006SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block080Part006] using hcert

def TailChunk001Sub001Block080Part007SupportExplicit : Finset ℕ :=
  ([28022] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block080Part007 : ℚ :=
  (4907703025 : ℚ) / 38533582831541202

def SurrogateDiagonalTailChunk001Sub001Block080Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28022
    = surrogateDiagTailX0RatChunk001Sub001Block080Part007

theorem surrogateDiagonalTailChunk001Sub001Block080Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block080Part007CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block080Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block080Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block080Part007CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block080Part007SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block080Part007] using hcert

def TailChunk001Sub001Block080Part008SupportExplicit : Finset ℕ :=
  ([28023] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block080Part008 : ℚ :=
  (872380962637 : ℚ) / 12178515067746355200

def SurrogateDiagonalTailChunk001Sub001Block080Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28023
    = surrogateDiagTailX0RatChunk001Sub001Block080Part008

theorem surrogateDiagonalTailChunk001Sub001Block080Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block080Part008CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block080Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block080Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block080Part008CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block080Part008SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block080Part008] using hcert

def TailChunk001Sub001Block080Part009SupportExplicit : Finset ℕ :=
  ([28027] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block080Part009 : ℚ :=
  (12273636390625 : ℚ) / 385665986444339731122

def SurrogateDiagonalTailChunk001Sub001Block080Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28027
    = surrogateDiagTailX0RatChunk001Sub001Block080Part009

theorem surrogateDiagonalTailChunk001Sub001Block080Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block080Part009CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block080Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block080Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block080Part009CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block080Part009SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block080Part009] using hcert

def TailChunk001Sub001Block080Part010SupportExplicit : Finset ℕ :=
  ([28029] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block080Part010 : ℚ :=
  (21818865065725 : ℚ) / 304723742375774602368

def SurrogateDiagonalTailChunk001Sub001Block080Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28029
    = surrogateDiagTailX0RatChunk001Sub001Block080Part010

theorem surrogateDiagonalTailChunk001Sub001Block080Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block080Part010CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block080Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block080Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block080Part010CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block080Part010SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block080Part010] using hcert

def TailChunk001Sub001Block080Part011SupportExplicit : Finset ℕ :=
  ([28030] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block080Part011 : ℚ :=
  (8343939768025 : ℚ) / 39458388819498190848

def SurrogateDiagonalTailChunk001Sub001Block080Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28030
    = surrogateDiagTailX0RatChunk001Sub001Block080Part011

theorem surrogateDiagonalTailChunk001Sub001Block080Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block080Part011CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block080Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block080Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block080Part011CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block080Part011SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block080Part011] using hcert

def TailChunk001Sub001Block080Part012SupportExplicit : Finset ℕ :=
  ([28031] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block080Part012 : ℚ :=
  (19643424025 : ℚ) / 617417935520134962

def SurrogateDiagonalTailChunk001Sub001Block080Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28031
    = surrogateDiagTailX0RatChunk001Sub001Block080Part012

theorem surrogateDiagonalTailChunk001Sub001Block080Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block080Part012CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block080Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block080Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block080Part012CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block080Part012SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block080Part012] using hcert

def TailChunk001Sub001Block080Part013SupportExplicit : Finset ℕ :=
  ([28034] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block080Part013 : ℚ :=
  (59705450147 : ℚ) / 450810199693136400

def SurrogateDiagonalTailChunk001Sub001Block080Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28034
    = surrogateDiagTailX0RatChunk001Sub001Block080Part013

theorem surrogateDiagonalTailChunk001Sub001Block080Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block080Part013CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block080Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block080Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block080Part013CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block080Part013SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block080Part013] using hcert

def TailChunk001Sub001Block080Part014SupportExplicit : Finset ℕ :=
  ([28038] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block080Part014 : ℚ :=
  (3411418099925 : ℚ) / 9530774239234228224

def SurrogateDiagonalTailChunk001Sub001Block080Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28038
    = surrogateDiagTailX0RatChunk001Sub001Block080Part014

theorem surrogateDiagonalTailChunk001Sub001Block080Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block080Part014CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block080Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block080Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block080Part014CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block080Part014SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block080Part014] using hcert

def TailChunk001Sub001Block080Part015SupportExplicit : Finset ℕ :=
  ([28039] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block080Part015 : ℚ :=
  (10246852849 : ℚ) / 263490257691635520

def SurrogateDiagonalTailChunk001Sub001Block080Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28039
    = surrogateDiagTailX0RatChunk001Sub001Block080Part015

theorem surrogateDiagonalTailChunk001Sub001Block080Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block080Part015CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block080Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block080Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block080Part015CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block080Part015SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block080Part015] using hcert

def TailChunk001Sub001Block080Part016SupportExplicit : Finset ℕ :=
  ([28041] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block080Part016 : ℚ :=
  (9476515588325 : ℚ) / 110240102162268831744

def SurrogateDiagonalTailChunk001Sub001Block080Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28041
    = surrogateDiagTailX0RatChunk001Sub001Block080Part016

theorem surrogateDiagonalTailChunk001Sub001Block080Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block080Part016CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block080Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block080Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block080Part016CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block080Part016SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block080Part016] using hcert

def TailChunk001Sub001Block080Part017SupportExplicit : Finset ℕ :=
  ([28042] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block080Part017 : ℚ :=
  (10627212875 : ℚ) / 58100536586675583

def SurrogateDiagonalTailChunk001Sub001Block080Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28042
    = surrogateDiagTailX0RatChunk001Sub001Block080Part017

theorem surrogateDiagonalTailChunk001Sub001Block080Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block080Part017CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block080Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block080Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block080Part017CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block080Part017SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block080Part017] using hcert

def TailChunk001Sub001Block080Part018SupportExplicit : Finset ℕ :=
  ([28043] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block080Part018 : ℚ :=
  (499663768475 : ℚ) / 14547208469847105024

def SurrogateDiagonalTailChunk001Sub001Block080Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28043
    = surrogateDiagTailX0RatChunk001Sub001Block080Part018

theorem surrogateDiagonalTailChunk001Sub001Block080Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block080Part018CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block080Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block080Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block080Part018CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block080Part018SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block080Part018] using hcert

def TailChunk001Sub001Block080Part019SupportExplicit : Finset ℕ :=
  ([28045] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block080Part019 : ℚ :=
  (1199419196749 : ℚ) / 22756076565988147200

def SurrogateDiagonalTailChunk001Sub001Block080Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28045
    = surrogateDiagTailX0RatChunk001Sub001Block080Part019

theorem surrogateDiagonalTailChunk001Sub001Block080Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block080Part019CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block080Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block080Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block080Part019CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block080Part019SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block080Part019] using hcert

def TailChunk001Sub001Block080Part020SupportExplicit : Finset ℕ :=
  ([28046] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block080Part020 : ℚ :=
  (1299247464425 : ℚ) / 9527118166096054272

def SurrogateDiagonalTailChunk001Sub001Block080Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28046
    = surrogateDiagTailX0RatChunk001Sub001Block080Part020

theorem surrogateDiagonalTailChunk001Sub001Block080Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block080Part020CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block080Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block080Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block080Part020CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block080Part020SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block080Part020] using hcert

def TailChunk001Sub001Block080Part021SupportExplicit : Finset ℕ :=
  ([28047] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block080Part021 : ℚ :=
  (21846900065125 : ℚ) / 305507345294841366528

def SurrogateDiagonalTailChunk001Sub001Block080Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28047
    = surrogateDiagTailX0RatChunk001Sub001Block080Part021

theorem surrogateDiagonalTailChunk001Sub001Block080Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block080Part021CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block080Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block080Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block080Part021CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block080Part021SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block080Part021] using hcert

def TailChunk001Sub001Block080Part022SupportExplicit : Finset ℕ :=
  ([28049] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block080Part022 : ℚ :=
  (37115358948025 : ℚ) / 834594734211367367808

def SurrogateDiagonalTailChunk001Sub001Block080Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28049
    = surrogateDiagTailX0RatChunk001Sub001Block080Part022

theorem surrogateDiagonalTailChunk001Sub001Block080Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block080Part022CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block080Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block080Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block080Part022CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block080Part022SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block080Part022] using hcert

def TailChunk001Sub001Block080Part023SupportExplicit : Finset ℕ :=
  ([28051] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block080Part023 : ℚ :=
  (786858601 : ℚ) / 24767279425642050

def SurrogateDiagonalTailChunk001Sub001Block080Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28051
    = surrogateDiagTailX0RatChunk001Sub001Block080Part023

theorem surrogateDiagonalTailChunk001Sub001Block080Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block080Part023CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block080Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block080Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block080Part023CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block080Part023SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block080Part023] using hcert

def TailChunk001Sub001Block080Part024SupportExplicit : Finset ℕ :=
  ([28055] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block080Part024 : ℚ :=
  (1176144210307 : ℚ) / 21772176924672000000

def SurrogateDiagonalTailChunk001Sub001Block080Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28055
    = surrogateDiagTailX0RatChunk001Sub001Block080Part024

theorem surrogateDiagonalTailChunk001Sub001Block080Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block080Part024CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block080Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block080Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block080Part024CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block080Part024SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block080Part024] using hcert

def surrogateDiagonalTailChunk001Sub001Block080HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub001Block080Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block080Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block080Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block080Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block080Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block080Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block080Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block080Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block080Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block080Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub001Block080Head : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block080Part000
    + surrogateDiagTailX0RatChunk001Sub001Block080Part001
    + surrogateDiagTailX0RatChunk001Sub001Block080Part002
    + surrogateDiagTailX0RatChunk001Sub001Block080Part003
    + surrogateDiagTailX0RatChunk001Sub001Block080Part004
    + surrogateDiagTailX0RatChunk001Sub001Block080Part005
    + surrogateDiagTailX0RatChunk001Sub001Block080Part006
    + surrogateDiagTailX0RatChunk001Sub001Block080Part007
    + surrogateDiagTailX0RatChunk001Sub001Block080Part008
    + surrogateDiagTailX0RatChunk001Sub001Block080Part009

def surrogateDiagonalTailChunk001Sub001Block080MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub001Block080Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block080Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block080Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block080Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block080Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block080Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block080Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block080Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block080Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block080Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub001Block080Mid : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block080Part010
    + surrogateDiagTailX0RatChunk001Sub001Block080Part011
    + surrogateDiagTailX0RatChunk001Sub001Block080Part012
    + surrogateDiagTailX0RatChunk001Sub001Block080Part013
    + surrogateDiagTailX0RatChunk001Sub001Block080Part014
    + surrogateDiagTailX0RatChunk001Sub001Block080Part015
    + surrogateDiagTailX0RatChunk001Sub001Block080Part016
    + surrogateDiagTailX0RatChunk001Sub001Block080Part017
    + surrogateDiagTailX0RatChunk001Sub001Block080Part018
    + surrogateDiagTailX0RatChunk001Sub001Block080Part019

def surrogateDiagonalTailChunk001Sub001Block080TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub001Block080Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block080Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block080Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block080Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block080Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub001Block080Tail : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block080Part020
    + surrogateDiagTailX0RatChunk001Sub001Block080Part021
    + surrogateDiagTailX0RatChunk001Sub001Block080Part022
    + surrogateDiagTailX0RatChunk001Sub001Block080Part023
    + surrogateDiagTailX0RatChunk001Sub001Block080Part024

def surrogateDiagonalTailChunk001Sub001Block080Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk001Sub001Block080HeadSum X0
    + surrogateDiagonalTailChunk001Sub001Block080MidSum X0
    + surrogateDiagonalTailChunk001Sub001Block080TailSum X0

def surrogateDiagTailX0RatChunk001Sub001Block080 : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block080Part000
    + surrogateDiagTailX0RatChunk001Sub001Block080Part001
    + surrogateDiagTailX0RatChunk001Sub001Block080Part002
    + surrogateDiagTailX0RatChunk001Sub001Block080Part003
    + surrogateDiagTailX0RatChunk001Sub001Block080Part004
    + surrogateDiagTailX0RatChunk001Sub001Block080Part005
    + surrogateDiagTailX0RatChunk001Sub001Block080Part006
    + surrogateDiagTailX0RatChunk001Sub001Block080Part007
    + surrogateDiagTailX0RatChunk001Sub001Block080Part008
    + surrogateDiagTailX0RatChunk001Sub001Block080Part009
    + surrogateDiagTailX0RatChunk001Sub001Block080Part010
    + surrogateDiagTailX0RatChunk001Sub001Block080Part011
    + surrogateDiagTailX0RatChunk001Sub001Block080Part012
    + surrogateDiagTailX0RatChunk001Sub001Block080Part013
    + surrogateDiagTailX0RatChunk001Sub001Block080Part014
    + surrogateDiagTailX0RatChunk001Sub001Block080Part015
    + surrogateDiagTailX0RatChunk001Sub001Block080Part016
    + surrogateDiagTailX0RatChunk001Sub001Block080Part017
    + surrogateDiagTailX0RatChunk001Sub001Block080Part018
    + surrogateDiagTailX0RatChunk001Sub001Block080Part019
    + surrogateDiagTailX0RatChunk001Sub001Block080Part020
    + surrogateDiagTailX0RatChunk001Sub001Block080Part021
    + surrogateDiagTailX0RatChunk001Sub001Block080Part022
    + surrogateDiagTailX0RatChunk001Sub001Block080Part023
    + surrogateDiagTailX0RatChunk001Sub001Block080Part024

theorem surrogateDiagTailX0RatChunk001Sub001Block080_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk001Sub001Block080Head + surrogateDiagTailX0RatChunk001Sub001Block080Mid + surrogateDiagTailX0RatChunk001Sub001Block080Tail =
      surrogateDiagTailX0RatChunk001Sub001Block080 := by
  unfold surrogateDiagTailX0RatChunk001Sub001Block080Head surrogateDiagTailX0RatChunk001Sub001Block080Mid surrogateDiagTailX0RatChunk001Sub001Block080Tail surrogateDiagTailX0RatChunk001Sub001Block080
  ring

def SurrogateDiagonalTailChunk001Sub001Block080HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub001Block080HeadSum X0 = surrogateDiagTailX0RatChunk001Sub001Block080Head

def SurrogateDiagonalTailChunk001Sub001Block080MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub001Block080MidSum X0 = surrogateDiagTailX0RatChunk001Sub001Block080Mid

def SurrogateDiagonalTailChunk001Sub001Block080TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub001Block080TailSum X0 = surrogateDiagTailX0RatChunk001Sub001Block080Tail

theorem surrogateDiagonalTailChunk001Sub001Block080_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk001Sub001Block080HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk001Sub001Block080MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk001Sub001Block080TailCertificateAt X0) :
    surrogateDiagonalTailChunk001Sub001Block080Sum X0 = surrogateDiagTailX0RatChunk001Sub001Block080 := by
  unfold SurrogateDiagonalTailChunk001Sub001Block080HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk001Sub001Block080MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk001Sub001Block080TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk001Sub001Block080Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk001Sub001Block080_eq_head_add_mid_add_tail

/-- Block 081 covers tail-support indices [17025,17050) and q from 28057 to 28097. -/

def TailChunk001Sub001Block081Part000SupportExplicit : Finset ℕ :=
  ([28057] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block081Part000 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block081Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28057
    = surrogateDiagTailX0RatChunk001Sub001Block081Part000

theorem surrogateDiagonalTailChunk001Sub001Block081Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block081Part000CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block081Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block081Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block081Part000CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block081Part000SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block081Part000] using hcert

def TailChunk001Sub001Block081Part001SupportExplicit : Finset ℕ :=
  ([28058] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block081Part001 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block081Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28058
    = surrogateDiagTailX0RatChunk001Sub001Block081Part001

theorem surrogateDiagonalTailChunk001Sub001Block081Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block081Part001CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block081Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block081Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block081Part001CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block081Part001SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block081Part001] using hcert

def TailChunk001Sub001Block081Part002SupportExplicit : Finset ℕ :=
  ([28059] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block081Part002 : ℚ :=
  (49534944575 : ℚ) / 91773580241584429056

def SurrogateDiagonalTailChunk001Sub001Block081Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28059
    = surrogateDiagTailX0RatChunk001Sub001Block081Part002

theorem surrogateDiagonalTailChunk001Sub001Block081Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block081Part002CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block081Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block081Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block081Part002CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block081Part002SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block081Part002] using hcert

def TailChunk001Sub001Block081Part003SupportExplicit : Finset ℕ :=
  ([28061] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block081Part003 : ℚ :=
  (24090257 : ℚ) / 62192592281250000

def SurrogateDiagonalTailChunk001Sub001Block081Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28061
    = surrogateDiagTailX0RatChunk001Sub001Block081Part003

theorem surrogateDiagonalTailChunk001Sub001Block081Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block081Part003CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block081Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block081Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block081Part003CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block081Part003SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block081Part003] using hcert

def TailChunk001Sub001Block081Part004SupportExplicit : Finset ℕ :=
  ([28063] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block081Part004 : ℚ :=
  (315862411 : ℚ) / 163359364987929600

def SurrogateDiagonalTailChunk001Sub001Block081Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28063
    = surrogateDiagTailX0RatChunk001Sub001Block081Part004

theorem surrogateDiagonalTailChunk001Sub001Block081Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block081Part004CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block081Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block081Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block081Part004CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block081Part004SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block081Part004] using hcert

def TailChunk001Sub001Block081Part005SupportExplicit : Finset ℕ :=
  ([28065] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block081Part005 : ℚ :=
  (4395244537 : ℚ) / 1252429339844812800

def SurrogateDiagonalTailChunk001Sub001Block081Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28065
    = surrogateDiagTailX0RatChunk001Sub001Block081Part005

theorem surrogateDiagonalTailChunk001Sub001Block081Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block081Part005CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block081Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block081Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block081Part005CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block081Part005SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block081Part005] using hcert

def TailChunk001Sub001Block081Part006SupportExplicit : Finset ℕ :=
  ([28066] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block081Part006 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block081Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28066
    = surrogateDiagTailX0RatChunk001Sub001Block081Part006

theorem surrogateDiagonalTailChunk001Sub001Block081Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block081Part006CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block081Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block081Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block081Part006CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block081Part006SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block081Part006] using hcert

def TailChunk001Sub001Block081Part007SupportExplicit : Finset ℕ :=
  ([28067] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block081Part007 : ℚ :=
  (1031181290875 : ℚ) / 856473547507916341248

def SurrogateDiagonalTailChunk001Sub001Block081Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28067
    = surrogateDiagTailX0RatChunk001Sub001Block081Part007

theorem surrogateDiagonalTailChunk001Sub001Block081Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block081Part007CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block081Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block081Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block081Part007CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block081Part007SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block081Part007] using hcert

def TailChunk001Sub001Block081Part008SupportExplicit : Finset ℕ :=
  ([28069] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block081Part008 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block081Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28069
    = surrogateDiagTailX0RatChunk001Sub001Block081Part008

theorem surrogateDiagonalTailChunk001Sub001Block081Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block081Part008CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block081Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block081Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block081Part008CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block081Part008SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block081Part008] using hcert

def TailChunk001Sub001Block081Part009SupportExplicit : Finset ℕ :=
  ([28070] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block081Part009 : ℚ :=
  (31505016277 : ℚ) / 849516429312000000

def SurrogateDiagonalTailChunk001Sub001Block081Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28070
    = surrogateDiagTailX0RatChunk001Sub001Block081Part009

theorem surrogateDiagonalTailChunk001Sub001Block081Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block081Part009CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block081Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block081Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block081Part009CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block081Part009SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block081Part009] using hcert

def TailChunk001Sub001Block081Part010SupportExplicit : Finset ℕ :=
  ([28073] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block081Part010 : ℚ :=
  (16831132775 : ℚ) / 160940452743631642752

def SurrogateDiagonalTailChunk001Sub001Block081Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28073
    = surrogateDiagTailX0RatChunk001Sub001Block081Part010

theorem surrogateDiagonalTailChunk001Sub001Block081Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block081Part010CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block081Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block081Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block081Part010CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block081Part010SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block081Part010] using hcert

def TailChunk001Sub001Block081Part011SupportExplicit : Finset ℕ :=
  ([28074] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block081Part011 : ℚ :=
  (684177660275 : ℚ) / 9579828090738767424

def SurrogateDiagonalTailChunk001Sub001Block081Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28074
    = surrogateDiagTailX0RatChunk001Sub001Block081Part011

theorem surrogateDiagonalTailChunk001Sub001Block081Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block081Part011CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block081Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block081Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block081Part011CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block081Part011SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block081Part011] using hcert

def TailChunk001Sub001Block081Part012SupportExplicit : Finset ℕ :=
  ([28078] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block081Part012 : ℚ :=
  (592815269 : ℚ) / 725492941574400000

def SurrogateDiagonalTailChunk001Sub001Block081Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28078
    = surrogateDiagTailX0RatChunk001Sub001Block081Part012

theorem surrogateDiagonalTailChunk001Sub001Block081Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block081Part012CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block081Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block081Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block081Part012CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block081Part012SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block081Part012] using hcert

def TailChunk001Sub001Block081Part013SupportExplicit : Finset ℕ :=
  ([28079] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block081Part013 : ℚ :=
  (112728047375 : ℚ) / 703047078277525545984

def SurrogateDiagonalTailChunk001Sub001Block081Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28079
    = surrogateDiagTailX0RatChunk001Sub001Block081Part013

theorem surrogateDiagonalTailChunk001Sub001Block081Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block081Part013CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block081Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block081Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block081Part013CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block081Part013SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block081Part013] using hcert

def TailChunk001Sub001Block081Part014SupportExplicit : Finset ℕ :=
  ([28081] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block081Part014 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block081Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28081
    = surrogateDiagTailX0RatChunk001Sub001Block081Part014

theorem surrogateDiagonalTailChunk001Sub001Block081Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block081Part014CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block081Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block081Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block081Part014CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block081Part014SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block081Part014] using hcert

def TailChunk001Sub001Block081Part015SupportExplicit : Finset ℕ :=
  ([28082] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block081Part015 : ℚ :=
  (9022888375 : ℚ) / 2883889145570534784

def SurrogateDiagonalTailChunk001Sub001Block081Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28082
    = surrogateDiagTailX0RatChunk001Sub001Block081Part015

theorem surrogateDiagonalTailChunk001Sub001Block081Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block081Part015CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block081Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block081Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block081Part015CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block081Part015SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block081Part015] using hcert

def TailChunk001Sub001Block081Part016SupportExplicit : Finset ℕ :=
  ([28083] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block081Part016 : ℚ :=
  (2063256781 : ℚ) / 393538817721139200

def SurrogateDiagonalTailChunk001Sub001Block081Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28083
    = surrogateDiagTailX0RatChunk001Sub001Block081Part016

theorem surrogateDiagonalTailChunk001Sub001Block081Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block081Part016CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block081Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block081Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block081Part016CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block081Part016SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block081Part016] using hcert

def TailChunk001Sub001Block081Part017SupportExplicit : Finset ℕ :=
  ([28085] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block081Part017 : ℚ :=
  (577369807 : ℚ) / 1401530107507507200

def SurrogateDiagonalTailChunk001Sub001Block081Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28085
    = surrogateDiagTailX0RatChunk001Sub001Block081Part017

theorem surrogateDiagonalTailChunk001Sub001Block081Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block081Part017CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block081Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block081Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block081Part017CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block081Part017SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block081Part017] using hcert

def TailChunk001Sub001Block081Part018SupportExplicit : Finset ℕ :=
  ([28086] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block081Part018 : ℚ :=
  (11005937897 : ℚ) / 131246244000000000

def SurrogateDiagonalTailChunk001Sub001Block081Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28086
    = surrogateDiagTailX0RatChunk001Sub001Block081Part018

theorem surrogateDiagonalTailChunk001Sub001Block081Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block081Part018CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block081Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block081Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block081Part018CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block081Part018SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block081Part018] using hcert

def TailChunk001Sub001Block081Part019SupportExplicit : Finset ℕ :=
  ([28087] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block081Part019 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block081Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28087
    = surrogateDiagTailX0RatChunk001Sub001Block081Part019

theorem surrogateDiagonalTailChunk001Sub001Block081Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block081Part019CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block081Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block081Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block081Part019CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block081Part019SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block081Part019] using hcert

def TailChunk001Sub001Block081Part020SupportExplicit : Finset ℕ :=
  ([28091] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block081Part020 : ℚ :=
  (1007883950425 : ℚ) / 839606047038585980928

def SurrogateDiagonalTailChunk001Sub001Block081Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28091
    = surrogateDiagTailX0RatChunk001Sub001Block081Part020

theorem surrogateDiagonalTailChunk001Sub001Block081Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block081Part020CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block081Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block081Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block081Part020CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block081Part020SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block081Part020] using hcert

def TailChunk001Sub001Block081Part021SupportExplicit : Finset ℕ :=
  ([28093] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block081Part021 : ℚ :=
  (289795969 : ℚ) / 557367729271603200

def SurrogateDiagonalTailChunk001Sub001Block081Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28093
    = surrogateDiagTailX0RatChunk001Sub001Block081Part021

theorem surrogateDiagonalTailChunk001Sub001Block081Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block081Part021CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block081Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block081Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block081Part021CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block081Part021SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block081Part021] using hcert

def TailChunk001Sub001Block081Part022SupportExplicit : Finset ℕ :=
  ([28094] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block081Part022 : ℚ :=
  (5465693367 : ℚ) / 883829092797798400

def SurrogateDiagonalTailChunk001Sub001Block081Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28094
    = surrogateDiagTailX0RatChunk001Sub001Block081Part022

theorem surrogateDiagonalTailChunk001Sub001Block081Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block081Part022CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block081Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block081Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block081Part022CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block081Part022SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block081Part022] using hcert

def TailChunk001Sub001Block081Part023SupportExplicit : Finset ℕ :=
  ([28095] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block081Part023 : ℚ :=
  (329226769375 : ℚ) / 31444898203903721472

def SurrogateDiagonalTailChunk001Sub001Block081Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28095
    = surrogateDiagTailX0RatChunk001Sub001Block081Part023

theorem surrogateDiagonalTailChunk001Sub001Block081Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block081Part023CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block081Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block081Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block081Part023CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block081Part023SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block081Part023] using hcert

def TailChunk001Sub001Block081Part024SupportExplicit : Finset ℕ :=
  ([28097] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block081Part024 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block081Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28097
    = surrogateDiagTailX0RatChunk001Sub001Block081Part024

theorem surrogateDiagonalTailChunk001Sub001Block081Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block081Part024CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block081Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block081Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block081Part024CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block081Part024SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block081Part024] using hcert

def surrogateDiagonalTailChunk001Sub001Block081HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub001Block081Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block081Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block081Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block081Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block081Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block081Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block081Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block081Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block081Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block081Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub001Block081Head : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block081Part000
    + surrogateDiagTailX0RatChunk001Sub001Block081Part001
    + surrogateDiagTailX0RatChunk001Sub001Block081Part002
    + surrogateDiagTailX0RatChunk001Sub001Block081Part003
    + surrogateDiagTailX0RatChunk001Sub001Block081Part004
    + surrogateDiagTailX0RatChunk001Sub001Block081Part005
    + surrogateDiagTailX0RatChunk001Sub001Block081Part006
    + surrogateDiagTailX0RatChunk001Sub001Block081Part007
    + surrogateDiagTailX0RatChunk001Sub001Block081Part008
    + surrogateDiagTailX0RatChunk001Sub001Block081Part009

def surrogateDiagonalTailChunk001Sub001Block081MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub001Block081Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block081Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block081Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block081Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block081Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block081Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block081Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block081Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block081Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block081Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub001Block081Mid : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block081Part010
    + surrogateDiagTailX0RatChunk001Sub001Block081Part011
    + surrogateDiagTailX0RatChunk001Sub001Block081Part012
    + surrogateDiagTailX0RatChunk001Sub001Block081Part013
    + surrogateDiagTailX0RatChunk001Sub001Block081Part014
    + surrogateDiagTailX0RatChunk001Sub001Block081Part015
    + surrogateDiagTailX0RatChunk001Sub001Block081Part016
    + surrogateDiagTailX0RatChunk001Sub001Block081Part017
    + surrogateDiagTailX0RatChunk001Sub001Block081Part018
    + surrogateDiagTailX0RatChunk001Sub001Block081Part019

def surrogateDiagonalTailChunk001Sub001Block081TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub001Block081Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block081Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block081Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block081Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block081Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub001Block081Tail : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block081Part020
    + surrogateDiagTailX0RatChunk001Sub001Block081Part021
    + surrogateDiagTailX0RatChunk001Sub001Block081Part022
    + surrogateDiagTailX0RatChunk001Sub001Block081Part023
    + surrogateDiagTailX0RatChunk001Sub001Block081Part024

def surrogateDiagonalTailChunk001Sub001Block081Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk001Sub001Block081HeadSum X0
    + surrogateDiagonalTailChunk001Sub001Block081MidSum X0
    + surrogateDiagonalTailChunk001Sub001Block081TailSum X0

def surrogateDiagTailX0RatChunk001Sub001Block081 : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block081Part000
    + surrogateDiagTailX0RatChunk001Sub001Block081Part001
    + surrogateDiagTailX0RatChunk001Sub001Block081Part002
    + surrogateDiagTailX0RatChunk001Sub001Block081Part003
    + surrogateDiagTailX0RatChunk001Sub001Block081Part004
    + surrogateDiagTailX0RatChunk001Sub001Block081Part005
    + surrogateDiagTailX0RatChunk001Sub001Block081Part006
    + surrogateDiagTailX0RatChunk001Sub001Block081Part007
    + surrogateDiagTailX0RatChunk001Sub001Block081Part008
    + surrogateDiagTailX0RatChunk001Sub001Block081Part009
    + surrogateDiagTailX0RatChunk001Sub001Block081Part010
    + surrogateDiagTailX0RatChunk001Sub001Block081Part011
    + surrogateDiagTailX0RatChunk001Sub001Block081Part012
    + surrogateDiagTailX0RatChunk001Sub001Block081Part013
    + surrogateDiagTailX0RatChunk001Sub001Block081Part014
    + surrogateDiagTailX0RatChunk001Sub001Block081Part015
    + surrogateDiagTailX0RatChunk001Sub001Block081Part016
    + surrogateDiagTailX0RatChunk001Sub001Block081Part017
    + surrogateDiagTailX0RatChunk001Sub001Block081Part018
    + surrogateDiagTailX0RatChunk001Sub001Block081Part019
    + surrogateDiagTailX0RatChunk001Sub001Block081Part020
    + surrogateDiagTailX0RatChunk001Sub001Block081Part021
    + surrogateDiagTailX0RatChunk001Sub001Block081Part022
    + surrogateDiagTailX0RatChunk001Sub001Block081Part023
    + surrogateDiagTailX0RatChunk001Sub001Block081Part024

theorem surrogateDiagTailX0RatChunk001Sub001Block081_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk001Sub001Block081Head + surrogateDiagTailX0RatChunk001Sub001Block081Mid + surrogateDiagTailX0RatChunk001Sub001Block081Tail =
      surrogateDiagTailX0RatChunk001Sub001Block081 := by
  unfold surrogateDiagTailX0RatChunk001Sub001Block081Head surrogateDiagTailX0RatChunk001Sub001Block081Mid surrogateDiagTailX0RatChunk001Sub001Block081Tail surrogateDiagTailX0RatChunk001Sub001Block081
  ring

def SurrogateDiagonalTailChunk001Sub001Block081HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub001Block081HeadSum X0 = surrogateDiagTailX0RatChunk001Sub001Block081Head

def SurrogateDiagonalTailChunk001Sub001Block081MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub001Block081MidSum X0 = surrogateDiagTailX0RatChunk001Sub001Block081Mid

def SurrogateDiagonalTailChunk001Sub001Block081TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub001Block081TailSum X0 = surrogateDiagTailX0RatChunk001Sub001Block081Tail

theorem surrogateDiagonalTailChunk001Sub001Block081_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk001Sub001Block081HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk001Sub001Block081MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk001Sub001Block081TailCertificateAt X0) :
    surrogateDiagonalTailChunk001Sub001Block081Sum X0 = surrogateDiagTailX0RatChunk001Sub001Block081 := by
  unfold SurrogateDiagonalTailChunk001Sub001Block081HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk001Sub001Block081MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk001Sub001Block081TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk001Sub001Block081Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk001Sub001Block081_eq_head_add_mid_add_tail

/-- Block 082 covers tail-support indices [17050,17075) and q from 28099 to 28137. -/

def TailChunk001Sub001Block082Part000SupportExplicit : Finset ℕ :=
  ([28099] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block082Part000 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block082Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28099
    = surrogateDiagTailX0RatChunk001Sub001Block082Part000

theorem surrogateDiagonalTailChunk001Sub001Block082Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block082Part000CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block082Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block082Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block082Part000CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block082Part000SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block082Part000] using hcert

def TailChunk001Sub001Block082Part001SupportExplicit : Finset ℕ :=
  ([28101] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block082Part001 : ℚ :=
  (734217669625 : ℚ) / 169179960001563721728

def SurrogateDiagonalTailChunk001Sub001Block082Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28101
    = surrogateDiagTailX0RatChunk001Sub001Block082Part001

theorem surrogateDiagonalTailChunk001Sub001Block082Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block082Part001CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block082Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block082Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block082Part001CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block082Part001SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block082Part001] using hcert

def TailChunk001Sub001Block082Part002SupportExplicit : Finset ℕ :=
  ([28102] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block082Part002 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block082Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28102
    = surrogateDiagTailX0RatChunk001Sub001Block082Part002

theorem surrogateDiagonalTailChunk001Sub001Block082Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block082Part002CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block082Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block082Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block082Part002CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block082Part002SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block082Part002] using hcert

def TailChunk001Sub001Block082Part003SupportExplicit : Finset ℕ :=
  ([28103] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block082Part003 : ℚ :=
  (52065903875 : ℚ) / 743319054621866271744

def SurrogateDiagonalTailChunk001Sub001Block082Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28103
    = surrogateDiagTailX0RatChunk001Sub001Block082Part003

theorem surrogateDiagonalTailChunk001Sub001Block082Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block082Part003CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block082Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block082Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block082Part003CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block082Part003SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block082Part003] using hcert

def TailChunk001Sub001Block082Part004SupportExplicit : Finset ℕ :=
  ([28105] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block082Part004 : ℚ :=
  (96590384113 : ℚ) / 8917883668345651200

def SurrogateDiagonalTailChunk001Sub001Block082Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28105
    = surrogateDiagTailX0RatChunk001Sub001Block082Part004

theorem surrogateDiagonalTailChunk001Sub001Block082Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block082Part004CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block082Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block082Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block082Part004CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block082Part004SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block082Part004] using hcert

def TailChunk001Sub001Block082Part005SupportExplicit : Finset ℕ :=
  ([28106] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block082Part005 : ℚ :=
  (187876006025 : ℚ) / 18128114615621615616

def SurrogateDiagonalTailChunk001Sub001Block082Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28106
    = surrogateDiagTailX0RatChunk001Sub001Block082Part005

theorem surrogateDiagonalTailChunk001Sub001Block082Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block082Part005CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block082Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block082Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block082Part005CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block082Part005SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block082Part005] using hcert

def TailChunk001Sub001Block082Part006SupportExplicit : Finset ℕ :=
  ([28109] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block082Part006 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block082Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28109
    = surrogateDiagTailX0RatChunk001Sub001Block082Part006

theorem surrogateDiagonalTailChunk001Sub001Block082Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block082Part006CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block082Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block082Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block082Part006CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block082Part006SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block082Part006] using hcert

def TailChunk001Sub001Block082Part007SupportExplicit : Finset ℕ :=
  ([28110] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block082Part007 : ℚ :=
  (356511512275 : ℚ) / 1965306137743982592

def SurrogateDiagonalTailChunk001Sub001Block082Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28110
    = surrogateDiagTailX0RatChunk001Sub001Block082Part007

theorem surrogateDiagonalTailChunk001Sub001Block082Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block082Part007CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block082Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block082Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block082Part007CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block082Part007SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block082Part007] using hcert

def TailChunk001Sub001Block082Part008SupportExplicit : Finset ℕ :=
  ([28111] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block082Part008 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block082Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28111
    = surrogateDiagTailX0RatChunk001Sub001Block082Part008

theorem surrogateDiagonalTailChunk001Sub001Block082Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block082Part008CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block082Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block082Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block082Part008CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block082Part008SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block082Part008] using hcert

def TailChunk001Sub001Block082Part009SupportExplicit : Finset ℕ :=
  ([28113] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block082Part009 : ℚ :=
  (5001 : ℚ) / 2466654607875200

def SurrogateDiagonalTailChunk001Sub001Block082Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28113
    = surrogateDiagTailX0RatChunk001Sub001Block082Part009

theorem surrogateDiagonalTailChunk001Sub001Block082Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block082Part009CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block082Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block082Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block082Part009CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block082Part009SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block082Part009] using hcert

def TailChunk001Sub001Block082Part010SupportExplicit : Finset ℕ :=
  ([28114] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block082Part010 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block082Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28114
    = surrogateDiagTailX0RatChunk001Sub001Block082Part010

theorem surrogateDiagonalTailChunk001Sub001Block082Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block082Part010CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block082Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block082Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block082Part010CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block082Part010SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block082Part010] using hcert

def TailChunk001Sub001Block082Part011SupportExplicit : Finset ℕ :=
  ([28115] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block082Part011 : ℚ :=
  (1976680734625 : ℚ) / 639484745736124090368

def SurrogateDiagonalTailChunk001Sub001Block082Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28115
    = surrogateDiagTailX0RatChunk001Sub001Block082Part011

theorem surrogateDiagonalTailChunk001Sub001Block082Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block082Part011CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block082Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block082Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block082Part011CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block082Part011SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block082Part011] using hcert

def TailChunk001Sub001Block082Part012SupportExplicit : Finset ℕ :=
  ([28117] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block082Part012 : ℚ :=
  (2125335329 : ℚ) / 10917285190549223040

def SurrogateDiagonalTailChunk001Sub001Block082Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28117
    = surrogateDiagTailX0RatChunk001Sub001Block082Part012

theorem surrogateDiagonalTailChunk001Sub001Block082Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block082Part012CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block082Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block082Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block082Part012CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block082Part012SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block082Part012] using hcert

def TailChunk001Sub001Block082Part013SupportExplicit : Finset ℕ :=
  ([28118] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block082Part013 : ℚ :=
  (43432681125 : ℚ) / 12713810337356054528

def SurrogateDiagonalTailChunk001Sub001Block082Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28118
    = surrogateDiagTailX0RatChunk001Sub001Block082Part013

theorem surrogateDiagonalTailChunk001Sub001Block082Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block082Part013CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block082Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block082Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block082Part013CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block082Part013SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block082Part013] using hcert

def TailChunk001Sub001Block082Part014SupportExplicit : Finset ℕ :=
  ([28119] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block082Part014 : ℚ :=
  (1053962998825 : ℚ) / 116379775291233927168

def SurrogateDiagonalTailChunk001Sub001Block082Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28119
    = surrogateDiagTailX0RatChunk001Sub001Block082Part014

theorem surrogateDiagonalTailChunk001Sub001Block082Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block082Part014CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block082Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block082Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block082Part014CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block082Part014SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block082Part014] using hcert

def TailChunk001Sub001Block082Part015SupportExplicit : Finset ℕ :=
  ([28121] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block082Part015 : ℚ :=
  (3278860631 : ℚ) / 29019717662976000000

def SurrogateDiagonalTailChunk001Sub001Block082Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28121
    = surrogateDiagTailX0RatChunk001Sub001Block082Part015

theorem surrogateDiagonalTailChunk001Sub001Block082Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block082Part015CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block082Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block082Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block082Part015CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block082Part015SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block082Part015] using hcert

def TailChunk001Sub001Block082Part016SupportExplicit : Finset ℕ :=
  ([28122] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block082Part016 : ℚ :=
  (153096968975 : ℚ) / 1881899884660948992

def SurrogateDiagonalTailChunk001Sub001Block082Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28122
    = surrogateDiagTailX0RatChunk001Sub001Block082Part016

theorem surrogateDiagonalTailChunk001Sub001Block082Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block082Part016CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block082Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block082Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block082Part016CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block082Part016SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block082Part016] using hcert

def TailChunk001Sub001Block082Part017SupportExplicit : Finset ℕ :=
  ([28123] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block082Part017 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block082Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28123
    = surrogateDiagTailX0RatChunk001Sub001Block082Part017

theorem surrogateDiagonalTailChunk001Sub001Block082Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block082Part017CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block082Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block082Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block082Part017CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block082Part017SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block082Part017] using hcert

def TailChunk001Sub001Block082Part018SupportExplicit : Finset ℕ :=
  ([28127] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block082Part018 : ℚ :=
  (2732020933 : ℚ) / 3557533530641241600

def SurrogateDiagonalTailChunk001Sub001Block082Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28127
    = surrogateDiagTailX0RatChunk001Sub001Block082Part018

theorem surrogateDiagonalTailChunk001Sub001Block082Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block082Part018CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block082Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block082Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block082Part018CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block082Part018SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block082Part018] using hcert

def TailChunk001Sub001Block082Part019SupportExplicit : Finset ℕ :=
  ([28129] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block082Part019 : ℚ :=
  (1570091375 : ℚ) / 5397430263466173504

def SurrogateDiagonalTailChunk001Sub001Block082Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28129
    = surrogateDiagTailX0RatChunk001Sub001Block082Part019

theorem surrogateDiagonalTailChunk001Sub001Block082Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block082Part019CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block082Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block082Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block082Part019CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block082Part019SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block082Part019] using hcert

def TailChunk001Sub001Block082Part020SupportExplicit : Finset ℕ :=
  ([28130] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block082Part020 : ℚ :=
  (1061306729275 : ℚ) / 33418263704012587008

def SurrogateDiagonalTailChunk001Sub001Block082Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28130
    = surrogateDiagTailX0RatChunk001Sub001Block082Part020

theorem surrogateDiagonalTailChunk001Sub001Block082Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block082Part020CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block082Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block082Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block082Part020CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block082Part020SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block082Part020] using hcert

def TailChunk001Sub001Block082Part021SupportExplicit : Finset ℕ :=
  ([28131] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block082Part021 : ℚ :=
  (125025 : ℚ) / 61824467109675008

def SurrogateDiagonalTailChunk001Sub001Block082Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28131
    = surrogateDiagTailX0RatChunk001Sub001Block082Part021

theorem surrogateDiagonalTailChunk001Sub001Block082Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block082Part021CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block082Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block082Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block082Part021CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block082Part021SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block082Part021] using hcert

def TailChunk001Sub001Block082Part022SupportExplicit : Finset ℕ :=
  ([28133] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block082Part022 : ℚ :=
  (1010895200725 : ℚ) / 844639893830928440448

def SurrogateDiagonalTailChunk001Sub001Block082Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28133
    = surrogateDiagTailX0RatChunk001Sub001Block082Part022

theorem surrogateDiagonalTailChunk001Sub001Block082Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block082Part022CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block082Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block082Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block082Part022CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block082Part022SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block082Part022] using hcert

def TailChunk001Sub001Block082Part023SupportExplicit : Finset ℕ :=
  ([28135] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block082Part023 : ℚ :=
  (9617891347 : ℚ) / 2211159118499020800

def SurrogateDiagonalTailChunk001Sub001Block082Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28135
    = surrogateDiagTailX0RatChunk001Sub001Block082Part023

theorem surrogateDiagonalTailChunk001Sub001Block082Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block082Part023CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block082Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block082Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block082Part023CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block082Part023SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block082Part023] using hcert

def TailChunk001Sub001Block082Part024SupportExplicit : Finset ℕ :=
  ([28137] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block082Part024 : ℚ :=
  (1520025 : ℚ) / 3557111712186368

def SurrogateDiagonalTailChunk001Sub001Block082Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28137
    = surrogateDiagTailX0RatChunk001Sub001Block082Part024

theorem surrogateDiagonalTailChunk001Sub001Block082Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block082Part024CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block082Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block082Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block082Part024CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block082Part024SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block082Part024] using hcert

def surrogateDiagonalTailChunk001Sub001Block082HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub001Block082Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block082Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block082Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block082Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block082Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block082Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block082Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block082Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block082Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block082Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub001Block082Head : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block082Part000
    + surrogateDiagTailX0RatChunk001Sub001Block082Part001
    + surrogateDiagTailX0RatChunk001Sub001Block082Part002
    + surrogateDiagTailX0RatChunk001Sub001Block082Part003
    + surrogateDiagTailX0RatChunk001Sub001Block082Part004
    + surrogateDiagTailX0RatChunk001Sub001Block082Part005
    + surrogateDiagTailX0RatChunk001Sub001Block082Part006
    + surrogateDiagTailX0RatChunk001Sub001Block082Part007
    + surrogateDiagTailX0RatChunk001Sub001Block082Part008
    + surrogateDiagTailX0RatChunk001Sub001Block082Part009

def surrogateDiagonalTailChunk001Sub001Block082MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub001Block082Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block082Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block082Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block082Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block082Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block082Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block082Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block082Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block082Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block082Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub001Block082Mid : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block082Part010
    + surrogateDiagTailX0RatChunk001Sub001Block082Part011
    + surrogateDiagTailX0RatChunk001Sub001Block082Part012
    + surrogateDiagTailX0RatChunk001Sub001Block082Part013
    + surrogateDiagTailX0RatChunk001Sub001Block082Part014
    + surrogateDiagTailX0RatChunk001Sub001Block082Part015
    + surrogateDiagTailX0RatChunk001Sub001Block082Part016
    + surrogateDiagTailX0RatChunk001Sub001Block082Part017
    + surrogateDiagTailX0RatChunk001Sub001Block082Part018
    + surrogateDiagTailX0RatChunk001Sub001Block082Part019

def surrogateDiagonalTailChunk001Sub001Block082TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub001Block082Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block082Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block082Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block082Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block082Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub001Block082Tail : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block082Part020
    + surrogateDiagTailX0RatChunk001Sub001Block082Part021
    + surrogateDiagTailX0RatChunk001Sub001Block082Part022
    + surrogateDiagTailX0RatChunk001Sub001Block082Part023
    + surrogateDiagTailX0RatChunk001Sub001Block082Part024

def surrogateDiagonalTailChunk001Sub001Block082Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk001Sub001Block082HeadSum X0
    + surrogateDiagonalTailChunk001Sub001Block082MidSum X0
    + surrogateDiagonalTailChunk001Sub001Block082TailSum X0

def surrogateDiagTailX0RatChunk001Sub001Block082 : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block082Part000
    + surrogateDiagTailX0RatChunk001Sub001Block082Part001
    + surrogateDiagTailX0RatChunk001Sub001Block082Part002
    + surrogateDiagTailX0RatChunk001Sub001Block082Part003
    + surrogateDiagTailX0RatChunk001Sub001Block082Part004
    + surrogateDiagTailX0RatChunk001Sub001Block082Part005
    + surrogateDiagTailX0RatChunk001Sub001Block082Part006
    + surrogateDiagTailX0RatChunk001Sub001Block082Part007
    + surrogateDiagTailX0RatChunk001Sub001Block082Part008
    + surrogateDiagTailX0RatChunk001Sub001Block082Part009
    + surrogateDiagTailX0RatChunk001Sub001Block082Part010
    + surrogateDiagTailX0RatChunk001Sub001Block082Part011
    + surrogateDiagTailX0RatChunk001Sub001Block082Part012
    + surrogateDiagTailX0RatChunk001Sub001Block082Part013
    + surrogateDiagTailX0RatChunk001Sub001Block082Part014
    + surrogateDiagTailX0RatChunk001Sub001Block082Part015
    + surrogateDiagTailX0RatChunk001Sub001Block082Part016
    + surrogateDiagTailX0RatChunk001Sub001Block082Part017
    + surrogateDiagTailX0RatChunk001Sub001Block082Part018
    + surrogateDiagTailX0RatChunk001Sub001Block082Part019
    + surrogateDiagTailX0RatChunk001Sub001Block082Part020
    + surrogateDiagTailX0RatChunk001Sub001Block082Part021
    + surrogateDiagTailX0RatChunk001Sub001Block082Part022
    + surrogateDiagTailX0RatChunk001Sub001Block082Part023
    + surrogateDiagTailX0RatChunk001Sub001Block082Part024

theorem surrogateDiagTailX0RatChunk001Sub001Block082_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk001Sub001Block082Head + surrogateDiagTailX0RatChunk001Sub001Block082Mid + surrogateDiagTailX0RatChunk001Sub001Block082Tail =
      surrogateDiagTailX0RatChunk001Sub001Block082 := by
  unfold surrogateDiagTailX0RatChunk001Sub001Block082Head surrogateDiagTailX0RatChunk001Sub001Block082Mid surrogateDiagTailX0RatChunk001Sub001Block082Tail surrogateDiagTailX0RatChunk001Sub001Block082
  ring

def SurrogateDiagonalTailChunk001Sub001Block082HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub001Block082HeadSum X0 = surrogateDiagTailX0RatChunk001Sub001Block082Head

def SurrogateDiagonalTailChunk001Sub001Block082MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub001Block082MidSum X0 = surrogateDiagTailX0RatChunk001Sub001Block082Mid

def SurrogateDiagonalTailChunk001Sub001Block082TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub001Block082TailSum X0 = surrogateDiagTailX0RatChunk001Sub001Block082Tail

theorem surrogateDiagonalTailChunk001Sub001Block082_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk001Sub001Block082HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk001Sub001Block082MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk001Sub001Block082TailCertificateAt X0) :
    surrogateDiagonalTailChunk001Sub001Block082Sum X0 = surrogateDiagTailX0RatChunk001Sub001Block082 := by
  unfold SurrogateDiagonalTailChunk001Sub001Block082HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk001Sub001Block082MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk001Sub001Block082TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk001Sub001Block082Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk001Sub001Block082_eq_head_add_mid_add_tail

/-- Block 083 covers tail-support indices [17075,17100) and q from 28138 to 28178. -/

def TailChunk001Sub001Block083Part000SupportExplicit : Finset ℕ :=
  ([28138] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block083Part000 : ℚ :=
  (16448129389 : ℚ) / 2668150147980931200

def SurrogateDiagonalTailChunk001Sub001Block083Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28138
    = surrogateDiagTailX0RatChunk001Sub001Block083Part000

theorem surrogateDiagonalTailChunk001Sub001Block083Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block083Part000CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block083Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block083Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block083Part000CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block083Part000SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block083Part000] using hcert

def TailChunk001Sub001Block083Part001SupportExplicit : Finset ℕ :=
  ([28139] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block083Part001 : ℚ :=
  (16646345713 : ℚ) / 50376006021382963200

def SurrogateDiagonalTailChunk001Sub001Block083Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28139
    = surrogateDiagTailX0RatChunk001Sub001Block083Part001

theorem surrogateDiagonalTailChunk001Sub001Block083Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block083Part001CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block083Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block083Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block083Part001CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block083Part001SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block083Part001] using hcert

def TailChunk001Sub001Block083Part002SupportExplicit : Finset ℕ :=
  ([28141] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block083Part002 : ℚ :=
  (38178756825 : ℚ) / 495831633143089365376

def SurrogateDiagonalTailChunk001Sub001Block083Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28141
    = surrogateDiagTailX0RatChunk001Sub001Block083Part002

theorem surrogateDiagonalTailChunk001Sub001Block083Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block083Part002CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block083Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block083Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block083Part002CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block083Part002SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block083Part002] using hcert

def TailChunk001Sub001Block083Part003SupportExplicit : Finset ℕ :=
  ([28142] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block083Part003 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block083Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28142
    = surrogateDiagTailX0RatChunk001Sub001Block083Part003

theorem surrogateDiagonalTailChunk001Sub001Block083Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block083Part003CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block083Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block083Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block083Part003CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block083Part003SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block083Part003] using hcert

def TailChunk001Sub001Block083Part004SupportExplicit : Finset ℕ :=
  ([28145] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block083Part004 : ℚ :=
  (43475417375 : ℚ) / 8561168321611825152

def SurrogateDiagonalTailChunk001Sub001Block083Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28145
    = surrogateDiagTailX0RatChunk001Sub001Block083Part004

theorem surrogateDiagonalTailChunk001Sub001Block083Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block083Part004CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block083Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block083Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block083Part004CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block083Part004SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block083Part004] using hcert

def TailChunk001Sub001Block083Part005SupportExplicit : Finset ℕ :=
  ([28146] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block083Part005 : ℚ :=
  (785932183 : ℚ) / 11061146991840960

def SurrogateDiagonalTailChunk001Sub001Block083Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28146
    = surrogateDiagTailX0RatChunk001Sub001Block083Part005

theorem surrogateDiagonalTailChunk001Sub001Block083Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block083Part005CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block083Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block083Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block083Part005CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block083Part005SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block083Part005] using hcert

def TailChunk001Sub001Block083Part006SupportExplicit : Finset ℕ :=
  ([28147] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block083Part006 : ℚ :=
  (40475998033 : ℚ) / 33852914478585907200

def SurrogateDiagonalTailChunk001Sub001Block083Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28147
    = surrogateDiagTailX0RatChunk001Sub001Block083Part006

theorem surrogateDiagonalTailChunk001Sub001Block083Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block083Part006CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block083Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block083Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block083Part006CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block083Part006SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block083Part006] using hcert

def TailChunk001Sub001Block083Part007SupportExplicit : Finset ℕ :=
  ([28149] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block083Part007 : ℚ :=
  (22031972953 : ℚ) / 8432672072631091200

def SurrogateDiagonalTailChunk001Sub001Block083Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28149
    = surrogateDiagTailX0RatChunk001Sub001Block083Part007

theorem surrogateDiagonalTailChunk001Sub001Block083Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block083Part007CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block083Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block083Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block083Part007CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block083Part007SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block083Part007] using hcert

def TailChunk001Sub001Block083Part008SupportExplicit : Finset ℕ :=
  ([28151] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block083Part008 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block083Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28151
    = surrogateDiagTailX0RatChunk001Sub001Block083Part008

theorem surrogateDiagonalTailChunk001Sub001Block083Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block083Part008CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block083Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block083Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block083Part008CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block083Part008SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block083Part008] using hcert

def TailChunk001Sub001Block083Part009SupportExplicit : Finset ℕ :=
  ([28153] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block083Part009 : ℚ :=
  (17683775 : ℚ) / 117673701184950144

def SurrogateDiagonalTailChunk001Sub001Block083Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28153
    = surrogateDiagTailX0RatChunk001Sub001Block083Part009

theorem surrogateDiagonalTailChunk001Sub001Block083Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block083Part009CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block083Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block083Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block083Part009CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block083Part009SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block083Part009] using hcert

def TailChunk001Sub001Block083Part010SupportExplicit : Finset ℕ :=
  ([28154] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block083Part010 : ℚ :=
  (562289161 : ℚ) / 39181613979844800

def SurrogateDiagonalTailChunk001Sub001Block083Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28154
    = surrogateDiagTailX0RatChunk001Sub001Block083Part010

theorem surrogateDiagonalTailChunk001Sub001Block083Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block083Part010CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block083Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block083Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block083Part010CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block083Part010SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block083Part010] using hcert

def TailChunk001Sub001Block083Part011SupportExplicit : Finset ℕ :=
  ([28155] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block083Part011 : ℚ :=
  (330632550475 : ℚ) / 31714520655006400512

def SurrogateDiagonalTailChunk001Sub001Block083Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28155
    = surrogateDiagTailX0RatChunk001Sub001Block083Part011

theorem surrogateDiagonalTailChunk001Sub001Block083Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block083Part011CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block083Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block083Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block083Part011CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block083Part011SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block083Part011] using hcert

def TailChunk001Sub001Block083Part012SupportExplicit : Finset ℕ :=
  ([28157] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block083Part012 : ℚ :=
  (11240711 : ℚ) / 69193644115230720

def SurrogateDiagonalTailChunk001Sub001Block083Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28157
    = surrogateDiagTailX0RatChunk001Sub001Block083Part012

theorem surrogateDiagonalTailChunk001Sub001Block083Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block083Part012CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block083Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block083Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block083Part012CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block083Part012SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block083Part012] using hcert

def TailChunk001Sub001Block083Part013SupportExplicit : Finset ℕ :=
  ([28159] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block083Part013 : ℚ :=
  (14448674551 : ℚ) / 54425936753084467200

def SurrogateDiagonalTailChunk001Sub001Block083Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28159
    = surrogateDiagTailX0RatChunk001Sub001Block083Part013

theorem surrogateDiagonalTailChunk001Sub001Block083Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block083Part013CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block083Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block083Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block083Part013CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block083Part013SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block083Part013] using hcert

def TailChunk001Sub001Block083Part014SupportExplicit : Finset ℕ :=
  ([28162] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block083Part014 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block083Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28162
    = surrogateDiagTailX0RatChunk001Sub001Block083Part014

theorem surrogateDiagonalTailChunk001Sub001Block083Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block083Part014CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block083Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block083Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block083Part014CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block083Part014SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block083Part014] using hcert

def TailChunk001Sub001Block083Part015SupportExplicit : Finset ℕ :=
  ([28163] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block083Part015 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block083Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28163
    = surrogateDiagTailX0RatChunk001Sub001Block083Part015

theorem surrogateDiagonalTailChunk001Sub001Block083Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block083Part015CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block083Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block083Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block083Part015CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block083Part015SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block083Part015] using hcert

def TailChunk001Sub001Block083Part016SupportExplicit : Finset ℕ :=
  ([28165] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block083Part016 : ℚ :=
  (41306650379 : ℚ) / 11378038282994073600

def SurrogateDiagonalTailChunk001Sub001Block083Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28165
    = surrogateDiagTailX0RatChunk001Sub001Block083Part016

theorem surrogateDiagonalTailChunk001Sub001Block083Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block083Part016CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block083Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block083Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block083Part016CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block083Part016SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block083Part016] using hcert

def TailChunk001Sub001Block083Part017SupportExplicit : Finset ℕ :=
  ([28166] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block083Part017 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block083Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28166
    = surrogateDiagTailX0RatChunk001Sub001Block083Part017

theorem surrogateDiagonalTailChunk001Sub001Block083Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block083Part017CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block083Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block083Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block083Part017CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block083Part017SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block083Part017] using hcert

def TailChunk001Sub001Block083Part018SupportExplicit : Finset ℕ :=
  ([28167] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block083Part018 : ℚ :=
  (366935179 : ℚ) / 582683318865100800

def SurrogateDiagonalTailChunk001Sub001Block083Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28167
    = surrogateDiagTailX0RatChunk001Sub001Block083Part018

theorem surrogateDiagonalTailChunk001Sub001Block083Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block083Part018CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block083Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block083Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block083Part018CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block083Part018SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block083Part018] using hcert

def TailChunk001Sub001Block083Part019SupportExplicit : Finset ℕ :=
  ([28169] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block083Part019 : ℚ :=
  (3604036975 : ℚ) / 8558262975423578112

def SurrogateDiagonalTailChunk001Sub001Block083Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28169
    = surrogateDiagTailX0RatChunk001Sub001Block083Part019

theorem surrogateDiagonalTailChunk001Sub001Block083Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block083Part019CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block083Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block083Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block083Part019CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block083Part019SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block083Part019] using hcert

def TailChunk001Sub001Block083Part020SupportExplicit : Finset ℕ :=
  ([28171] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block083Part020 : ℚ :=
  (1497046591 : ℚ) / 765202056439726080

def SurrogateDiagonalTailChunk001Sub001Block083Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28171
    = surrogateDiagTailX0RatChunk001Sub001Block083Part020

theorem surrogateDiagonalTailChunk001Sub001Block083Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block083Part020CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block083Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block083Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block083Part020CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block083Part020SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block083Part020] using hcert

def TailChunk001Sub001Block083Part021SupportExplicit : Finset ℕ :=
  ([28173] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block083Part021 : ℚ :=
  (1667 : ℚ) / 829260716630400

def SurrogateDiagonalTailChunk001Sub001Block083Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28173
    = surrogateDiagTailX0RatChunk001Sub001Block083Part021

theorem surrogateDiagonalTailChunk001Sub001Block083Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block083Part021CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block083Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block083Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block083Part021CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block083Part021SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block083Part021] using hcert

def TailChunk001Sub001Block083Part022SupportExplicit : Finset ℕ :=
  ([28174] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block083Part022 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block083Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28174
    = surrogateDiagTailX0RatChunk001Sub001Block083Part022

theorem surrogateDiagonalTailChunk001Sub001Block083Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block083Part022CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block083Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block083Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block083Part022CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block083Part022SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block083Part022] using hcert

def TailChunk001Sub001Block083Part023SupportExplicit : Finset ℕ :=
  ([28177] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block083Part023 : ℚ :=
  (417268948675 : ℚ) / 1266221530476783324288

def SurrogateDiagonalTailChunk001Sub001Block083Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28177
    = surrogateDiagTailX0RatChunk001Sub001Block083Part023

theorem surrogateDiagonalTailChunk001Sub001Block083Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block083Part023CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block083Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block083Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block083Part023CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block083Part023SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block083Part023] using hcert

def TailChunk001Sub001Block083Part024SupportExplicit : Finset ℕ :=
  ([28178] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block083Part024 : ℚ :=
  (81949006525 : ℚ) / 91319128763859468288

def SurrogateDiagonalTailChunk001Sub001Block083Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28178
    = surrogateDiagTailX0RatChunk001Sub001Block083Part024

theorem surrogateDiagonalTailChunk001Sub001Block083Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block083Part024CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block083Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block083Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block083Part024CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block083Part024SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block083Part024] using hcert

def surrogateDiagonalTailChunk001Sub001Block083HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub001Block083Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block083Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block083Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block083Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block083Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block083Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block083Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block083Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block083Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block083Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub001Block083Head : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block083Part000
    + surrogateDiagTailX0RatChunk001Sub001Block083Part001
    + surrogateDiagTailX0RatChunk001Sub001Block083Part002
    + surrogateDiagTailX0RatChunk001Sub001Block083Part003
    + surrogateDiagTailX0RatChunk001Sub001Block083Part004
    + surrogateDiagTailX0RatChunk001Sub001Block083Part005
    + surrogateDiagTailX0RatChunk001Sub001Block083Part006
    + surrogateDiagTailX0RatChunk001Sub001Block083Part007
    + surrogateDiagTailX0RatChunk001Sub001Block083Part008
    + surrogateDiagTailX0RatChunk001Sub001Block083Part009

def surrogateDiagonalTailChunk001Sub001Block083MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub001Block083Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block083Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block083Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block083Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block083Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block083Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block083Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block083Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block083Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block083Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub001Block083Mid : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block083Part010
    + surrogateDiagTailX0RatChunk001Sub001Block083Part011
    + surrogateDiagTailX0RatChunk001Sub001Block083Part012
    + surrogateDiagTailX0RatChunk001Sub001Block083Part013
    + surrogateDiagTailX0RatChunk001Sub001Block083Part014
    + surrogateDiagTailX0RatChunk001Sub001Block083Part015
    + surrogateDiagTailX0RatChunk001Sub001Block083Part016
    + surrogateDiagTailX0RatChunk001Sub001Block083Part017
    + surrogateDiagTailX0RatChunk001Sub001Block083Part018
    + surrogateDiagTailX0RatChunk001Sub001Block083Part019

def surrogateDiagonalTailChunk001Sub001Block083TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub001Block083Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block083Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block083Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block083Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block083Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub001Block083Tail : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block083Part020
    + surrogateDiagTailX0RatChunk001Sub001Block083Part021
    + surrogateDiagTailX0RatChunk001Sub001Block083Part022
    + surrogateDiagTailX0RatChunk001Sub001Block083Part023
    + surrogateDiagTailX0RatChunk001Sub001Block083Part024

def surrogateDiagonalTailChunk001Sub001Block083Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk001Sub001Block083HeadSum X0
    + surrogateDiagonalTailChunk001Sub001Block083MidSum X0
    + surrogateDiagonalTailChunk001Sub001Block083TailSum X0

def surrogateDiagTailX0RatChunk001Sub001Block083 : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block083Part000
    + surrogateDiagTailX0RatChunk001Sub001Block083Part001
    + surrogateDiagTailX0RatChunk001Sub001Block083Part002
    + surrogateDiagTailX0RatChunk001Sub001Block083Part003
    + surrogateDiagTailX0RatChunk001Sub001Block083Part004
    + surrogateDiagTailX0RatChunk001Sub001Block083Part005
    + surrogateDiagTailX0RatChunk001Sub001Block083Part006
    + surrogateDiagTailX0RatChunk001Sub001Block083Part007
    + surrogateDiagTailX0RatChunk001Sub001Block083Part008
    + surrogateDiagTailX0RatChunk001Sub001Block083Part009
    + surrogateDiagTailX0RatChunk001Sub001Block083Part010
    + surrogateDiagTailX0RatChunk001Sub001Block083Part011
    + surrogateDiagTailX0RatChunk001Sub001Block083Part012
    + surrogateDiagTailX0RatChunk001Sub001Block083Part013
    + surrogateDiagTailX0RatChunk001Sub001Block083Part014
    + surrogateDiagTailX0RatChunk001Sub001Block083Part015
    + surrogateDiagTailX0RatChunk001Sub001Block083Part016
    + surrogateDiagTailX0RatChunk001Sub001Block083Part017
    + surrogateDiagTailX0RatChunk001Sub001Block083Part018
    + surrogateDiagTailX0RatChunk001Sub001Block083Part019
    + surrogateDiagTailX0RatChunk001Sub001Block083Part020
    + surrogateDiagTailX0RatChunk001Sub001Block083Part021
    + surrogateDiagTailX0RatChunk001Sub001Block083Part022
    + surrogateDiagTailX0RatChunk001Sub001Block083Part023
    + surrogateDiagTailX0RatChunk001Sub001Block083Part024

theorem surrogateDiagTailX0RatChunk001Sub001Block083_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk001Sub001Block083Head + surrogateDiagTailX0RatChunk001Sub001Block083Mid + surrogateDiagTailX0RatChunk001Sub001Block083Tail =
      surrogateDiagTailX0RatChunk001Sub001Block083 := by
  unfold surrogateDiagTailX0RatChunk001Sub001Block083Head surrogateDiagTailX0RatChunk001Sub001Block083Mid surrogateDiagTailX0RatChunk001Sub001Block083Tail surrogateDiagTailX0RatChunk001Sub001Block083
  ring

def SurrogateDiagonalTailChunk001Sub001Block083HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub001Block083HeadSum X0 = surrogateDiagTailX0RatChunk001Sub001Block083Head

def SurrogateDiagonalTailChunk001Sub001Block083MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub001Block083MidSum X0 = surrogateDiagTailX0RatChunk001Sub001Block083Mid

def SurrogateDiagonalTailChunk001Sub001Block083TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub001Block083TailSum X0 = surrogateDiagTailX0RatChunk001Sub001Block083Tail

theorem surrogateDiagonalTailChunk001Sub001Block083_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk001Sub001Block083HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk001Sub001Block083MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk001Sub001Block083TailCertificateAt X0) :
    surrogateDiagonalTailChunk001Sub001Block083Sum X0 = surrogateDiagTailX0RatChunk001Sub001Block083 := by
  unfold SurrogateDiagonalTailChunk001Sub001Block083HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk001Sub001Block083MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk001Sub001Block083TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk001Sub001Block083Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk001Sub001Block083_eq_head_add_mid_add_tail

/-- Block 084 covers tail-support indices [17100,17125) and q from 28181 to 28218. -/

def TailChunk001Sub001Block084Part000SupportExplicit : Finset ℕ :=
  ([28181] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block084Part000 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block084Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28181
    = surrogateDiagTailX0RatChunk001Sub001Block084Part000

theorem surrogateDiagonalTailChunk001Sub001Block084Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block084Part000CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block084Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block084Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block084Part000CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block084Part000SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block084Part000] using hcert

def TailChunk001Sub001Block084Part001SupportExplicit : Finset ℕ :=
  ([28182] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block084Part001 : ℚ :=
  (53292861961 : ℚ) / 268792307712000000

def SurrogateDiagonalTailChunk001Sub001Block084Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28182
    = surrogateDiagTailX0RatChunk001Sub001Block084Part001

theorem surrogateDiagonalTailChunk001Sub001Block084Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block084Part001CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block084Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block084Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block084Part001CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block084Part001SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block084Part001] using hcert

def TailChunk001Sub001Block084Part002SupportExplicit : Finset ℕ :=
  ([28183] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block084Part002 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block084Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28183
    = surrogateDiagTailX0RatChunk001Sub001Block084Part002

theorem surrogateDiagonalTailChunk001Sub001Block084Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block084Part002CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block084Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block084Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block084Part002CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block084Part002SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block084Part002] using hcert

def TailChunk001Sub001Block084Part003SupportExplicit : Finset ℕ :=
  ([28185] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block084Part003 : ℚ :=
  (46034513675 : ℚ) / 5308330040151846912

def SurrogateDiagonalTailChunk001Sub001Block084Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28185
    = surrogateDiagTailX0RatChunk001Sub001Block084Part003

theorem surrogateDiagonalTailChunk001Sub001Block084Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block084Part003CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block084Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block084Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block084Part003CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block084Part003SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block084Part003] using hcert

def TailChunk001Sub001Block084Part004SupportExplicit : Finset ℕ :=
  ([28186] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block084Part004 : ℚ :=
  (632452525 : ℚ) / 186049195117903872

def SurrogateDiagonalTailChunk001Sub001Block084Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28186
    = surrogateDiagTailX0RatChunk001Sub001Block084Part004

theorem surrogateDiagonalTailChunk001Sub001Block084Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block084Part004CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block084Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block084Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block084Part004CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block084Part004SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block084Part004] using hcert

def TailChunk001Sub001Block084Part005SupportExplicit : Finset ℕ :=
  ([28187] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block084Part005 : ℚ :=
  (1984783271 : ℚ) / 19685139611426150400

def SurrogateDiagonalTailChunk001Sub001Block084Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28187
    = surrogateDiagTailX0RatChunk001Sub001Block084Part005

theorem surrogateDiagonalTailChunk001Sub001Block084Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block084Part005CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block084Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block084Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block084Part005CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block084Part005SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block084Part005] using hcert

def TailChunk001Sub001Block084Part006SupportExplicit : Finset ℕ :=
  ([28189] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block084Part006 : ℚ :=
  (1014917201125 : ℚ) / 851386858983574328448

def SurrogateDiagonalTailChunk001Sub001Block084Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28189
    = surrogateDiagTailX0RatChunk001Sub001Block084Part006

theorem surrogateDiagonalTailChunk001Sub001Block084Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block084Part006CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block084Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block084Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block084Part006CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block084Part006SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block084Part006] using hcert

def TailChunk001Sub001Block084Part007SupportExplicit : Finset ℕ :=
  ([28190] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block084Part007 : ℚ :=
  (993692251225 : ℚ) / 40367400111009712128

def SurrogateDiagonalTailChunk001Sub001Block084Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28190
    = surrogateDiagTailX0RatChunk001Sub001Block084Part007

theorem surrogateDiagonalTailChunk001Sub001Block084Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block084Part007CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block084Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block084Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block084Part007CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block084Part007SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block084Part007] using hcert

def TailChunk001Sub001Block084Part008SupportExplicit : Finset ℕ :=
  ([28191] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block084Part008 : ℚ :=
  (41675 : ℚ) / 20784556629743616

def SurrogateDiagonalTailChunk001Sub001Block084Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28191
    = surrogateDiagTailX0RatChunk001Sub001Block084Part008

theorem surrogateDiagonalTailChunk001Sub001Block084Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block084Part008CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block084Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block084Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block084Part008CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block084Part008SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block084Part008] using hcert

def TailChunk001Sub001Block084Part009SupportExplicit : Finset ℕ :=
  ([28194] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block084Part009 : ℚ :=
  (1384752630325 : ℚ) / 16937098961948540928

def SurrogateDiagonalTailChunk001Sub001Block084Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28194
    = surrogateDiagTailX0RatChunk001Sub001Block084Part009

theorem surrogateDiagonalTailChunk001Sub001Block084Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block084Part009CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block084Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block084Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block084Part009CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block084Part009SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block084Part009] using hcert

def TailChunk001Sub001Block084Part010SupportExplicit : Finset ℕ :=
  ([28195] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block084Part010 : ℚ :=
  (662646910875 : ℚ) / 215598559891453351936

def SurrogateDiagonalTailChunk001Sub001Block084Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28195
    = surrogateDiagTailX0RatChunk001Sub001Block084Part010

theorem surrogateDiagonalTailChunk001Sub001Block084Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block084Part010CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block084Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block084Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block084Part010CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block084Part010SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block084Part010] using hcert

def TailChunk001Sub001Block084Part011SupportExplicit : Finset ℕ :=
  ([28198] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block084Part011 : ℚ :=
  (48468546625 : ℚ) / 20542972246804541952

def SurrogateDiagonalTailChunk001Sub001Block084Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28198
    = surrogateDiagTailX0RatChunk001Sub001Block084Part011

theorem surrogateDiagonalTailChunk001Sub001Block084Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block084Part011CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block084Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block084Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block084Part011CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block084Part011SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block084Part011] using hcert

def TailChunk001Sub001Block084Part012SupportExplicit : Finset ℕ :=
  ([28199] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block084Part012 : ℚ :=
  (26119333375 : ℚ) / 376825872476368138752

def SurrogateDiagonalTailChunk001Sub001Block084Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28199
    = surrogateDiagTailX0RatChunk001Sub001Block084Part012

theorem surrogateDiagonalTailChunk001Sub001Block084Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block084Part012CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block084Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block084Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block084Part012CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block084Part012SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block084Part012] using hcert

def TailChunk001Sub001Block084Part013SupportExplicit : Finset ℕ :=
  ([28201] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block084Part013 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block084Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28201
    = surrogateDiagTailX0RatChunk001Sub001Block084Part013

theorem surrogateDiagonalTailChunk001Sub001Block084Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block084Part013CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block084Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block084Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block084Part013CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block084Part013SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block084Part013] using hcert

def TailChunk001Sub001Block084Part014SupportExplicit : Finset ℕ :=
  ([28202] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block084Part014 : ℚ :=
  (108716625 : ℚ) / 111264469760970008

def SurrogateDiagonalTailChunk001Sub001Block084Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28202
    = surrogateDiagTailX0RatChunk001Sub001Block084Part014

theorem surrogateDiagonalTailChunk001Sub001Block084Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block084Part014CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block084Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block084Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block084Part014CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block084Part014SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block084Part014] using hcert

def TailChunk001Sub001Block084Part015SupportExplicit : Finset ℕ :=
  ([28203] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block084Part015 : ℚ :=
  (513107736725 : ℚ) / 62889796407807442944

def SurrogateDiagonalTailChunk001Sub001Block084Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28203
    = surrogateDiagTailX0RatChunk001Sub001Block084Part015

theorem surrogateDiagonalTailChunk001Sub001Block084Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block084Part015CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block084Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block084Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block084Part015CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block084Part015SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block084Part015] using hcert

def TailChunk001Sub001Block084Part016SupportExplicit : Finset ℕ :=
  ([28205] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block084Part016 : ℚ :=
  (15914803859 : ℚ) / 5181711474127011840

def SurrogateDiagonalTailChunk001Sub001Block084Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28205
    = surrogateDiagTailX0RatChunk001Sub001Block084Part016

theorem surrogateDiagonalTailChunk001Sub001Block084Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block084Part016CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block084Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block084Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block084Part016CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block084Part016SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block084Part016] using hcert

def TailChunk001Sub001Block084Part017SupportExplicit : Finset ℕ :=
  ([28207] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block084Part017 : ℚ :=
  (75424399 : ℚ) / 729079244867635200

def SurrogateDiagonalTailChunk001Sub001Block084Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28207
    = surrogateDiagTailX0RatChunk001Sub001Block084Part017

theorem surrogateDiagonalTailChunk001Sub001Block084Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block084Part017CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block084Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block084Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block084Part017CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block084Part017SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block084Part017] using hcert

def TailChunk001Sub001Block084Part018SupportExplicit : Finset ℕ :=
  ([28209] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block084Part018 : ℚ :=
  (41675 : ℚ) / 20837697047842176

def SurrogateDiagonalTailChunk001Sub001Block084Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28209
    = surrogateDiagTailX0RatChunk001Sub001Block084Part018

theorem surrogateDiagonalTailChunk001Sub001Block084Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block084Part018CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block084Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block084Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block084Part018CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block084Part018SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block084Part018] using hcert

def TailChunk001Sub001Block084Part019SupportExplicit : Finset ℕ :=
  ([28210] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block084Part019 : ℚ :=
  (4091893919 : ℚ) / 46447310772633600

def SurrogateDiagonalTailChunk001Sub001Block084Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28210
    = surrogateDiagTailX0RatChunk001Sub001Block084Part019

theorem surrogateDiagonalTailChunk001Sub001Block084Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block084Part019CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block084Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block084Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block084Part019CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block084Part019SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block084Part019] using hcert

def TailChunk001Sub001Block084Part020SupportExplicit : Finset ℕ :=
  ([28211] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block084Part020 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block084Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28211
    = surrogateDiagTailX0RatChunk001Sub001Block084Part020

theorem surrogateDiagonalTailChunk001Sub001Block084Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block084Part020CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block084Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block084Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block084Part020CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block084Part020SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block084Part020] using hcert

def TailChunk001Sub001Block084Part021SupportExplicit : Finset ℕ :=
  ([28213] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block084Part021 : ℚ :=
  (3982712225 : ℚ) / 46725708967787249664

def SurrogateDiagonalTailChunk001Sub001Block084Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28213
    = surrogateDiagTailX0RatChunk001Sub001Block084Part021

theorem surrogateDiagonalTailChunk001Sub001Block084Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block084Part021CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block084Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block084Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block084Part021CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block084Part021SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block084Part021] using hcert

def TailChunk001Sub001Block084Part022SupportExplicit : Finset ℕ :=
  ([28214] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block084Part022 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block084Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28214
    = surrogateDiagTailX0RatChunk001Sub001Block084Part022

theorem surrogateDiagonalTailChunk001Sub001Block084Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block084Part022CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block084Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block084Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block084Part022CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block084Part022SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block084Part022] using hcert

def TailChunk001Sub001Block084Part023SupportExplicit : Finset ℕ :=
  ([28217] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block084Part023 : ℚ :=
  (47262039875 : ℚ) / 26755715369781264384

def SurrogateDiagonalTailChunk001Sub001Block084Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28217
    = surrogateDiagTailX0RatChunk001Sub001Block084Part023

theorem surrogateDiagonalTailChunk001Sub001Block084Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block084Part023CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block084Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block084Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block084Part023CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block084Part023SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block084Part023] using hcert

def TailChunk001Sub001Block084Part024SupportExplicit : Finset ℕ :=
  ([28218] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block084Part024 : ℚ :=
  (691212659975 : ℚ) / 9777939483065561664

def SurrogateDiagonalTailChunk001Sub001Block084Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28218
    = surrogateDiagTailX0RatChunk001Sub001Block084Part024

theorem surrogateDiagonalTailChunk001Sub001Block084Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block084Part024CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block084Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block084Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block084Part024CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block084Part024SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block084Part024] using hcert

def surrogateDiagonalTailChunk001Sub001Block084HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub001Block084Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block084Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block084Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block084Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block084Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block084Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block084Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block084Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block084Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block084Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub001Block084Head : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block084Part000
    + surrogateDiagTailX0RatChunk001Sub001Block084Part001
    + surrogateDiagTailX0RatChunk001Sub001Block084Part002
    + surrogateDiagTailX0RatChunk001Sub001Block084Part003
    + surrogateDiagTailX0RatChunk001Sub001Block084Part004
    + surrogateDiagTailX0RatChunk001Sub001Block084Part005
    + surrogateDiagTailX0RatChunk001Sub001Block084Part006
    + surrogateDiagTailX0RatChunk001Sub001Block084Part007
    + surrogateDiagTailX0RatChunk001Sub001Block084Part008
    + surrogateDiagTailX0RatChunk001Sub001Block084Part009

def surrogateDiagonalTailChunk001Sub001Block084MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub001Block084Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block084Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block084Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block084Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block084Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block084Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block084Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block084Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block084Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block084Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub001Block084Mid : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block084Part010
    + surrogateDiagTailX0RatChunk001Sub001Block084Part011
    + surrogateDiagTailX0RatChunk001Sub001Block084Part012
    + surrogateDiagTailX0RatChunk001Sub001Block084Part013
    + surrogateDiagTailX0RatChunk001Sub001Block084Part014
    + surrogateDiagTailX0RatChunk001Sub001Block084Part015
    + surrogateDiagTailX0RatChunk001Sub001Block084Part016
    + surrogateDiagTailX0RatChunk001Sub001Block084Part017
    + surrogateDiagTailX0RatChunk001Sub001Block084Part018
    + surrogateDiagTailX0RatChunk001Sub001Block084Part019

def surrogateDiagonalTailChunk001Sub001Block084TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub001Block084Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block084Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block084Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block084Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block084Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub001Block084Tail : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block084Part020
    + surrogateDiagTailX0RatChunk001Sub001Block084Part021
    + surrogateDiagTailX0RatChunk001Sub001Block084Part022
    + surrogateDiagTailX0RatChunk001Sub001Block084Part023
    + surrogateDiagTailX0RatChunk001Sub001Block084Part024

def surrogateDiagonalTailChunk001Sub001Block084Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk001Sub001Block084HeadSum X0
    + surrogateDiagonalTailChunk001Sub001Block084MidSum X0
    + surrogateDiagonalTailChunk001Sub001Block084TailSum X0

def surrogateDiagTailX0RatChunk001Sub001Block084 : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block084Part000
    + surrogateDiagTailX0RatChunk001Sub001Block084Part001
    + surrogateDiagTailX0RatChunk001Sub001Block084Part002
    + surrogateDiagTailX0RatChunk001Sub001Block084Part003
    + surrogateDiagTailX0RatChunk001Sub001Block084Part004
    + surrogateDiagTailX0RatChunk001Sub001Block084Part005
    + surrogateDiagTailX0RatChunk001Sub001Block084Part006
    + surrogateDiagTailX0RatChunk001Sub001Block084Part007
    + surrogateDiagTailX0RatChunk001Sub001Block084Part008
    + surrogateDiagTailX0RatChunk001Sub001Block084Part009
    + surrogateDiagTailX0RatChunk001Sub001Block084Part010
    + surrogateDiagTailX0RatChunk001Sub001Block084Part011
    + surrogateDiagTailX0RatChunk001Sub001Block084Part012
    + surrogateDiagTailX0RatChunk001Sub001Block084Part013
    + surrogateDiagTailX0RatChunk001Sub001Block084Part014
    + surrogateDiagTailX0RatChunk001Sub001Block084Part015
    + surrogateDiagTailX0RatChunk001Sub001Block084Part016
    + surrogateDiagTailX0RatChunk001Sub001Block084Part017
    + surrogateDiagTailX0RatChunk001Sub001Block084Part018
    + surrogateDiagTailX0RatChunk001Sub001Block084Part019
    + surrogateDiagTailX0RatChunk001Sub001Block084Part020
    + surrogateDiagTailX0RatChunk001Sub001Block084Part021
    + surrogateDiagTailX0RatChunk001Sub001Block084Part022
    + surrogateDiagTailX0RatChunk001Sub001Block084Part023
    + surrogateDiagTailX0RatChunk001Sub001Block084Part024

theorem surrogateDiagTailX0RatChunk001Sub001Block084_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk001Sub001Block084Head + surrogateDiagTailX0RatChunk001Sub001Block084Mid + surrogateDiagTailX0RatChunk001Sub001Block084Tail =
      surrogateDiagTailX0RatChunk001Sub001Block084 := by
  unfold surrogateDiagTailX0RatChunk001Sub001Block084Head surrogateDiagTailX0RatChunk001Sub001Block084Mid surrogateDiagTailX0RatChunk001Sub001Block084Tail surrogateDiagTailX0RatChunk001Sub001Block084
  ring

def SurrogateDiagonalTailChunk001Sub001Block084HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub001Block084HeadSum X0 = surrogateDiagTailX0RatChunk001Sub001Block084Head

def SurrogateDiagonalTailChunk001Sub001Block084MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub001Block084MidSum X0 = surrogateDiagTailX0RatChunk001Sub001Block084Mid

def SurrogateDiagonalTailChunk001Sub001Block084TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub001Block084TailSum X0 = surrogateDiagTailX0RatChunk001Sub001Block084Tail

theorem surrogateDiagonalTailChunk001Sub001Block084_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk001Sub001Block084HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk001Sub001Block084MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk001Sub001Block084TailCertificateAt X0) :
    surrogateDiagonalTailChunk001Sub001Block084Sum X0 = surrogateDiagTailX0RatChunk001Sub001Block084 := by
  unfold SurrogateDiagonalTailChunk001Sub001Block084HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk001Sub001Block084MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk001Sub001Block084TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk001Sub001Block084Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk001Sub001Block084_eq_head_add_mid_add_tail

/-- Block 085 covers tail-support indices [17125,17150) and q from 28219 to 28261. -/

def TailChunk001Sub001Block085Part000SupportExplicit : Finset ℕ :=
  ([28219] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block085Part000 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block085Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28219
    = surrogateDiagTailX0RatChunk001Sub001Block085Part000

theorem surrogateDiagonalTailChunk001Sub001Block085Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block085Part000CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block085Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block085Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block085Part000CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block085Part000SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block085Part000] using hcert

def TailChunk001Sub001Block085Part001SupportExplicit : Finset ℕ :=
  ([28221] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block085Part001 : ℚ :=
  (131721742025 : ℚ) / 129851873955110191104

def SurrogateDiagonalTailChunk001Sub001Block085Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28221
    = surrogateDiagTailX0RatChunk001Sub001Block085Part001

theorem surrogateDiagonalTailChunk001Sub001Block085Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block085Part001CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block085Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block085Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block085Part001CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block085Part001SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block085Part001] using hcert

def TailChunk001Sub001Block085Part002SupportExplicit : Finset ℕ :=
  ([28222] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block085Part002 : ℚ :=
  (128014025 : ℚ) / 160197354915250176

def SurrogateDiagonalTailChunk001Sub001Block085Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28222
    = surrogateDiagTailX0RatChunk001Sub001Block085Part002

theorem surrogateDiagonalTailChunk001Sub001Block085Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block085Part002CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block085Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block085Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block085Part002CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block085Part002SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block085Part002] using hcert

def TailChunk001Sub001Block085Part003SupportExplicit : Finset ℕ :=
  ([28226] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block085Part003 : ℚ :=
  (5516822607 : ℚ) / 900570457601238400

def SurrogateDiagonalTailChunk001Sub001Block085Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28226
    = surrogateDiagTailX0RatChunk001Sub001Block085Part003

theorem surrogateDiagonalTailChunk001Sub001Block085Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block085Part003CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block085Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block085Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block085Part003CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block085Part003SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block085Part003] using hcert

def TailChunk001Sub001Block085Part004SupportExplicit : Finset ℕ :=
  ([28229] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block085Part004 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block085Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28229
    = surrogateDiagTailX0RatChunk001Sub001Block085Part004

theorem surrogateDiagonalTailChunk001Sub001Block085Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block085Part004CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block085Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block085Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block085Part004CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block085Part004SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block085Part004] using hcert

def TailChunk001Sub001Block085Part005SupportExplicit : Finset ℕ :=
  ([28230] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block085Part005 : ℚ :=
  (10182634481 : ℚ) / 63971746594160640

def SurrogateDiagonalTailChunk001Sub001Block085Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28230
    = surrogateDiagTailX0RatChunk001Sub001Block085Part005

theorem surrogateDiagonalTailChunk001Sub001Block085Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block085Part005CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block085Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block085Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block085Part005CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block085Part005SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block085Part005] using hcert

def TailChunk001Sub001Block085Part006SupportExplicit : Finset ℕ :=
  ([28231] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block085Part006 : ℚ :=
  (133805910475 : ℚ) / 46282509908098449408

def SurrogateDiagonalTailChunk001Sub001Block085Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28231
    = surrogateDiagTailX0RatChunk001Sub001Block085Part006

theorem surrogateDiagonalTailChunk001Sub001Block085Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block085Part006CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block085Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block085Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block085Part006CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block085Part006SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block085Part006] using hcert

def TailChunk001Sub001Block085Part007SupportExplicit : Finset ℕ :=
  ([28234] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block085Part007 : ℚ :=
  (246204876025 : ℚ) / 79566911457365662848

def SurrogateDiagonalTailChunk001Sub001Block085Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28234
    = surrogateDiagTailX0RatChunk001Sub001Block085Part007

theorem surrogateDiagonalTailChunk001Sub001Block085Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block085Part007CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block085Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block085Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block085Part007CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block085Part007SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block085Part007] using hcert

def TailChunk001Sub001Block085Part008SupportExplicit : Finset ℕ :=
  ([28235] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block085Part008 : ℚ :=
  (1993582731625 : ℚ) / 650474565132114413568

def SurrogateDiagonalTailChunk001Sub001Block085Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28235
    = surrogateDiagTailX0RatChunk001Sub001Block085Part008

theorem surrogateDiagonalTailChunk001Sub001Block085Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block085Part008CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block085Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block085Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block085Part008CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block085Part008SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block085Part008] using hcert

def TailChunk001Sub001Block085Part009SupportExplicit : Finset ℕ :=
  ([28237] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block085Part009 : ℚ :=
  (1094686867 : ℚ) / 737427456000000000

def SurrogateDiagonalTailChunk001Sub001Block085Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28237
    = surrogateDiagTailX0RatChunk001Sub001Block085Part009

theorem surrogateDiagonalTailChunk001Sub001Block085Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block085Part009CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block085Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block085Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block085Part009CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block085Part009SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block085Part009] using hcert

def TailChunk001Sub001Block085Part010SupportExplicit : Finset ℕ :=
  ([28238] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block085Part010 : ℚ :=
  (288593275 : ℚ) / 20230384247635968

def SurrogateDiagonalTailChunk001Sub001Block085Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28238
    = surrogateDiagTailX0RatChunk001Sub001Block085Part010

theorem surrogateDiagonalTailChunk001Sub001Block085Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block085Part010CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block085Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block085Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block085Part010CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block085Part010SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block085Part010] using hcert

def TailChunk001Sub001Block085Part011SupportExplicit : Finset ℕ :=
  ([28239] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block085Part011 : ℚ :=
  (125025 : ℚ) / 62779472320268288

def SurrogateDiagonalTailChunk001Sub001Block085Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28239
    = surrogateDiagTailX0RatChunk001Sub001Block085Part011

theorem surrogateDiagonalTailChunk001Sub001Block085Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block085Part011CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block085Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block085Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block085Part011CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block085Part011SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block085Part011] using hcert

def TailChunk001Sub001Block085Part012SupportExplicit : Finset ℕ :=
  ([28241] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block085Part012 : ℚ :=
  (12783510199 : ℚ) / 55556827553682000000

def SurrogateDiagonalTailChunk001Sub001Block085Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28241
    = surrogateDiagTailX0RatChunk001Sub001Block085Part012

theorem surrogateDiagonalTailChunk001Sub001Block085Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block085Part012CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block085Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block085Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block085Part012CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block085Part012SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block085Part012] using hcert

def TailChunk001Sub001Block085Part013SupportExplicit : Finset ℕ :=
  ([28243] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block085Part013 : ℚ :=
  (367129421 : ℚ) / 3280856601904358400

def SurrogateDiagonalTailChunk001Sub001Block085Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28243
    = surrogateDiagTailX0RatChunk001Sub001Block085Part013

theorem surrogateDiagonalTailChunk001Sub001Block085Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block085Part013CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block085Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block085Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block085Part013CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block085Part013SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block085Part013] using hcert

def TailChunk001Sub001Block085Part014SupportExplicit : Finset ℕ :=
  ([28245] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block085Part014 : ℚ :=
  (898697939825 : ℚ) / 34237416717108117504

def SurrogateDiagonalTailChunk001Sub001Block085Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28245
    = surrogateDiagTailX0RatChunk001Sub001Block085Part014

theorem surrogateDiagonalTailChunk001Sub001Block085Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block085Part014CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block085Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block085Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block085Part014CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block085Part014SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block085Part014] using hcert

def TailChunk001Sub001Block085Part015SupportExplicit : Finset ℕ :=
  ([28246] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block085Part015 : ℚ :=
  (52029359075 : ℚ) / 28581354498288162816

def SurrogateDiagonalTailChunk001Sub001Block085Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28246
    = surrogateDiagTailX0RatChunk001Sub001Block085Part015

theorem surrogateDiagonalTailChunk001Sub001Block085Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block085Part015CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block085Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block085Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block085Part015CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block085Part015SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block085Part015] using hcert

def TailChunk001Sub001Block085Part016SupportExplicit : Finset ℕ :=
  ([28247] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block085Part016 : ℚ :=
  (8660163541 : ℚ) / 58039435325952000000

def SurrogateDiagonalTailChunk001Sub001Block085Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28247
    = surrogateDiagTailX0RatChunk001Sub001Block085Part016

theorem surrogateDiagonalTailChunk001Sub001Block085Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block085Part016CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block085Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block085Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block085Part016CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block085Part016SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block085Part016] using hcert

def TailChunk001Sub001Block085Part017SupportExplicit : Finset ℕ :=
  ([28249] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block085Part017 : ℚ :=
  (1087455611 : ℚ) / 1213151936879001600

def SurrogateDiagonalTailChunk001Sub001Block085Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28249
    = surrogateDiagTailX0RatChunk001Sub001Block085Part017

theorem surrogateDiagonalTailChunk001Sub001Block085Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block085Part017CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block085Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block085Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block085Part017CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block085Part017SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block085Part017] using hcert

def TailChunk001Sub001Block085Part018SupportExplicit : Finset ℕ :=
  ([28253] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block085Part018 : ℚ :=
  (419494058575 : ℚ) / 1279947383798836987008

def SurrogateDiagonalTailChunk001Sub001Block085Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28253
    = surrogateDiagTailX0RatChunk001Sub001Block085Part018

theorem surrogateDiagonalTailChunk001Sub001Block085Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block085Part018CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block085Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block085Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block085Part018CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block085Part018SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block085Part018] using hcert

def TailChunk001Sub001Block085Part019SupportExplicit : Finset ℕ :=
  ([28254] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block085Part019 : ℚ :=
  (1395431089825 : ℚ) / 15214689734086361088

def SurrogateDiagonalTailChunk001Sub001Block085Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28254
    = surrogateDiagTailX0RatChunk001Sub001Block085Part019

theorem surrogateDiagonalTailChunk001Sub001Block085Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block085Part019CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block085Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block085Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block085Part019CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block085Part019SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block085Part019] using hcert

def TailChunk001Sub001Block085Part020SupportExplicit : Finset ℕ :=
  ([28255] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block085Part020 : ℚ :=
  (5323751283 : ℚ) / 1739519685036800000

def SurrogateDiagonalTailChunk001Sub001Block085Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28255
    = surrogateDiagTailX0RatChunk001Sub001Block085Part020

theorem surrogateDiagonalTailChunk001Sub001Block085Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block085Part020CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block085Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block085Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block085Part020CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block085Part020SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block085Part020] using hcert

def TailChunk001Sub001Block085Part021SupportExplicit : Finset ℕ :=
  ([28257] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block085Part021 : ℚ :=
  (125025 : ℚ) / 62939709113825408

def SurrogateDiagonalTailChunk001Sub001Block085Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28257
    = surrogateDiagTailX0RatChunk001Sub001Block085Part021

theorem surrogateDiagonalTailChunk001Sub001Block085Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block085Part021CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block085Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block085Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block085Part021CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block085Part021SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block085Part021] using hcert

def TailChunk001Sub001Block085Part022SupportExplicit : Finset ℕ :=
  ([28258] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block085Part022 : ℚ :=
  (220563829 : ℚ) / 246064245142826880

def SurrogateDiagonalTailChunk001Sub001Block085Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28258
    = surrogateDiagTailX0RatChunk001Sub001Block085Part022

theorem surrogateDiagonalTailChunk001Sub001Block085Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block085Part022CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block085Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block085Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block085Part022CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block085Part022SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block085Part022] using hcert

def TailChunk001Sub001Block085Part023SupportExplicit : Finset ℕ :=
  ([28259] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block085Part023 : ℚ :=
  (95175346321 : ℚ) / 23260347216271411200

def SurrogateDiagonalTailChunk001Sub001Block085Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28259
    = surrogateDiagTailX0RatChunk001Sub001Block085Part023

theorem surrogateDiagonalTailChunk001Sub001Block085Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block085Part023CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block085Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block085Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block085Part023CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block085Part023SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block085Part023] using hcert

def TailChunk001Sub001Block085Part024SupportExplicit : Finset ℕ :=
  ([28261] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block085Part024 : ℚ :=
  (14578894875 : ℚ) / 123103152156096214624

def SurrogateDiagonalTailChunk001Sub001Block085Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28261
    = surrogateDiagTailX0RatChunk001Sub001Block085Part024

theorem surrogateDiagonalTailChunk001Sub001Block085Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block085Part024CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block085Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block085Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block085Part024CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block085Part024SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block085Part024] using hcert

def surrogateDiagonalTailChunk001Sub001Block085HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub001Block085Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block085Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block085Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block085Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block085Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block085Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block085Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block085Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block085Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block085Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub001Block085Head : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block085Part000
    + surrogateDiagTailX0RatChunk001Sub001Block085Part001
    + surrogateDiagTailX0RatChunk001Sub001Block085Part002
    + surrogateDiagTailX0RatChunk001Sub001Block085Part003
    + surrogateDiagTailX0RatChunk001Sub001Block085Part004
    + surrogateDiagTailX0RatChunk001Sub001Block085Part005
    + surrogateDiagTailX0RatChunk001Sub001Block085Part006
    + surrogateDiagTailX0RatChunk001Sub001Block085Part007
    + surrogateDiagTailX0RatChunk001Sub001Block085Part008
    + surrogateDiagTailX0RatChunk001Sub001Block085Part009

def surrogateDiagonalTailChunk001Sub001Block085MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub001Block085Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block085Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block085Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block085Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block085Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block085Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block085Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block085Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block085Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block085Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub001Block085Mid : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block085Part010
    + surrogateDiagTailX0RatChunk001Sub001Block085Part011
    + surrogateDiagTailX0RatChunk001Sub001Block085Part012
    + surrogateDiagTailX0RatChunk001Sub001Block085Part013
    + surrogateDiagTailX0RatChunk001Sub001Block085Part014
    + surrogateDiagTailX0RatChunk001Sub001Block085Part015
    + surrogateDiagTailX0RatChunk001Sub001Block085Part016
    + surrogateDiagTailX0RatChunk001Sub001Block085Part017
    + surrogateDiagTailX0RatChunk001Sub001Block085Part018
    + surrogateDiagTailX0RatChunk001Sub001Block085Part019

def surrogateDiagonalTailChunk001Sub001Block085TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub001Block085Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block085Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block085Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block085Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block085Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub001Block085Tail : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block085Part020
    + surrogateDiagTailX0RatChunk001Sub001Block085Part021
    + surrogateDiagTailX0RatChunk001Sub001Block085Part022
    + surrogateDiagTailX0RatChunk001Sub001Block085Part023
    + surrogateDiagTailX0RatChunk001Sub001Block085Part024

def surrogateDiagonalTailChunk001Sub001Block085Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk001Sub001Block085HeadSum X0
    + surrogateDiagonalTailChunk001Sub001Block085MidSum X0
    + surrogateDiagonalTailChunk001Sub001Block085TailSum X0

def surrogateDiagTailX0RatChunk001Sub001Block085 : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block085Part000
    + surrogateDiagTailX0RatChunk001Sub001Block085Part001
    + surrogateDiagTailX0RatChunk001Sub001Block085Part002
    + surrogateDiagTailX0RatChunk001Sub001Block085Part003
    + surrogateDiagTailX0RatChunk001Sub001Block085Part004
    + surrogateDiagTailX0RatChunk001Sub001Block085Part005
    + surrogateDiagTailX0RatChunk001Sub001Block085Part006
    + surrogateDiagTailX0RatChunk001Sub001Block085Part007
    + surrogateDiagTailX0RatChunk001Sub001Block085Part008
    + surrogateDiagTailX0RatChunk001Sub001Block085Part009
    + surrogateDiagTailX0RatChunk001Sub001Block085Part010
    + surrogateDiagTailX0RatChunk001Sub001Block085Part011
    + surrogateDiagTailX0RatChunk001Sub001Block085Part012
    + surrogateDiagTailX0RatChunk001Sub001Block085Part013
    + surrogateDiagTailX0RatChunk001Sub001Block085Part014
    + surrogateDiagTailX0RatChunk001Sub001Block085Part015
    + surrogateDiagTailX0RatChunk001Sub001Block085Part016
    + surrogateDiagTailX0RatChunk001Sub001Block085Part017
    + surrogateDiagTailX0RatChunk001Sub001Block085Part018
    + surrogateDiagTailX0RatChunk001Sub001Block085Part019
    + surrogateDiagTailX0RatChunk001Sub001Block085Part020
    + surrogateDiagTailX0RatChunk001Sub001Block085Part021
    + surrogateDiagTailX0RatChunk001Sub001Block085Part022
    + surrogateDiagTailX0RatChunk001Sub001Block085Part023
    + surrogateDiagTailX0RatChunk001Sub001Block085Part024

theorem surrogateDiagTailX0RatChunk001Sub001Block085_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk001Sub001Block085Head + surrogateDiagTailX0RatChunk001Sub001Block085Mid + surrogateDiagTailX0RatChunk001Sub001Block085Tail =
      surrogateDiagTailX0RatChunk001Sub001Block085 := by
  unfold surrogateDiagTailX0RatChunk001Sub001Block085Head surrogateDiagTailX0RatChunk001Sub001Block085Mid surrogateDiagTailX0RatChunk001Sub001Block085Tail surrogateDiagTailX0RatChunk001Sub001Block085
  ring

def SurrogateDiagonalTailChunk001Sub001Block085HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub001Block085HeadSum X0 = surrogateDiagTailX0RatChunk001Sub001Block085Head

def SurrogateDiagonalTailChunk001Sub001Block085MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub001Block085MidSum X0 = surrogateDiagTailX0RatChunk001Sub001Block085Mid

def SurrogateDiagonalTailChunk001Sub001Block085TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub001Block085TailSum X0 = surrogateDiagTailX0RatChunk001Sub001Block085Tail

theorem surrogateDiagonalTailChunk001Sub001Block085_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk001Sub001Block085HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk001Sub001Block085MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk001Sub001Block085TailCertificateAt X0) :
    surrogateDiagonalTailChunk001Sub001Block085Sum X0 = surrogateDiagTailX0RatChunk001Sub001Block085 := by
  unfold SurrogateDiagonalTailChunk001Sub001Block085HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk001Sub001Block085MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk001Sub001Block085TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk001Sub001Block085Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk001Sub001Block085_eq_head_add_mid_add_tail

/-- Block 086 covers tail-support indices [17150,17175) and q from 28262 to 28301. -/

def TailChunk001Sub001Block086Part000SupportExplicit : Finset ℕ :=
  ([28262] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block086Part000 : ℚ :=
  (41335457375 : ℚ) / 8013617970053548032

def SurrogateDiagonalTailChunk001Sub001Block086Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28262
    = surrogateDiagTailX0RatChunk001Sub001Block086Part000

theorem surrogateDiagonalTailChunk001Sub001Block086Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block086Part000CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block086Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block086Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block086Part000CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block086Part000SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block086Part000] using hcert

def TailChunk001Sub001Block086Part001SupportExplicit : Finset ℕ :=
  ([28263] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block086Part001 : ℚ :=
  (1667 : ℚ) / 839909193062400

def SurrogateDiagonalTailChunk001Sub001Block086Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28263
    = surrogateDiagTailX0RatChunk001Sub001Block086Part001

theorem surrogateDiagonalTailChunk001Sub001Block086Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block086Part001CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block086Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block086Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block086Part001CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block086Part001SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block086Part001] using hcert

def TailChunk001Sub001Block086Part002SupportExplicit : Finset ℕ :=
  ([28265] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block086Part002 : ℚ :=
  (1997819480875 : ℚ) / 653244011203027304448

def SurrogateDiagonalTailChunk001Sub001Block086Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28265
    = surrogateDiagTailX0RatChunk001Sub001Block086Part002

theorem surrogateDiagonalTailChunk001Sub001Block086Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block086Part002CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block086Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block086Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block086Part002CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block086Part002SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block086Part002] using hcert

def TailChunk001Sub001Block086Part003SupportExplicit : Finset ℕ :=
  ([28266] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block086Part003 : ℚ :=
  (1471325560525 : ℚ) / 10573747500097732608

def SurrogateDiagonalTailChunk001Sub001Block086Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28266
    = surrogateDiagTailX0RatChunk001Sub001Block086Part003

theorem surrogateDiagonalTailChunk001Sub001Block086Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block086Part003CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block086Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block086Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block086Part003CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block086Part003SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block086Part003] using hcert

def TailChunk001Sub001Block086Part004SupportExplicit : Finset ℕ :=
  ([28267] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block086Part004 : ℚ :=
  (191817455675 : ℚ) / 666010465691088528384

def SurrogateDiagonalTailChunk001Sub001Block086Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28267
    = surrogateDiagTailX0RatChunk001Sub001Block086Part004

theorem surrogateDiagonalTailChunk001Sub001Block086Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block086Part004CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block086Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block086Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block086Part004CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block086Part004SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block086Part004] using hcert

def TailChunk001Sub001Block086Part005SupportExplicit : Finset ℕ :=
  ([28270] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block086Part005 : ℚ :=
  (43423918741 : ℚ) / 1099731530101555200

def SurrogateDiagonalTailChunk001Sub001Block086Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28270
    = surrogateDiagTailX0RatChunk001Sub001Block086Part005

theorem surrogateDiagonalTailChunk001Sub001Block086Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block086Part005CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block086Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block086Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block086Part005CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block086Part005SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block086Part005] using hcert

def TailChunk001Sub001Block086Part006SupportExplicit : Finset ℕ :=
  ([28271] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block086Part006 : ℚ :=
  (14519793925 : ℚ) / 34731885972680736768

def SurrogateDiagonalTailChunk001Sub001Block086Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28271
    = surrogateDiagTailX0RatChunk001Sub001Block086Part006

theorem surrogateDiagonalTailChunk001Sub001Block086Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block086Part006CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block086Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block086Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block086Part006CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block086Part006SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block086Part006] using hcert

def TailChunk001Sub001Block086Part007SupportExplicit : Finset ℕ :=
  ([28274] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block086Part007 : ℚ :=
  (18321461 : ℚ) / 19528908344668800

def SurrogateDiagonalTailChunk001Sub001Block086Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28274
    = surrogateDiagTailX0RatChunk001Sub001Block086Part007

theorem surrogateDiagonalTailChunk001Sub001Block086Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block086Part007CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block086Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block086Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block086Part007CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block086Part007SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block086Part007] using hcert

def TailChunk001Sub001Block086Part008SupportExplicit : Finset ℕ :=
  ([28277] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block086Part008 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block086Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28277
    = surrogateDiagTailX0RatChunk001Sub001Block086Part008

theorem surrogateDiagonalTailChunk001Sub001Block086Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block086Part008CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block086Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block086Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block086Part008CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block086Part008SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block086Part008] using hcert

def TailChunk001Sub001Block086Part009SupportExplicit : Finset ℕ :=
  ([28279] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block086Part009 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block086Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28279
    = surrogateDiagTailX0RatChunk001Sub001Block086Part009

theorem surrogateDiagonalTailChunk001Sub001Block086Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block086Part009CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block086Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block086Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block086Part009CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block086Part009SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block086Part009] using hcert

def TailChunk001Sub001Block086Part010SupportExplicit : Finset ℕ :=
  ([28281] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block086Part010 : ℚ :=
  (4447394789 : ℚ) / 1718430163536445440

def SurrogateDiagonalTailChunk001Sub001Block086Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28281
    = surrogateDiagTailX0RatChunk001Sub001Block086Part010

theorem surrogateDiagonalTailChunk001Sub001Block086Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block086Part010CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block086Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block086Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block086Part010CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block086Part010SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block086Part010] using hcert

def TailChunk001Sub001Block086Part011SupportExplicit : Finset ℕ :=
  ([28282] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block086Part011 : ℚ :=
  (79414565125 : ℚ) / 92914881827733283968

def SurrogateDiagonalTailChunk001Sub001Block086Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28282
    = surrogateDiagTailX0RatChunk001Sub001Block086Part011

theorem surrogateDiagonalTailChunk001Sub001Block086Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block086Part011CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block086Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block086Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block086Part011CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block086Part011SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block086Part011] using hcert

def TailChunk001Sub001Block086Part012SupportExplicit : Finset ℕ :=
  ([28283] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block086Part012 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block086Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28283
    = surrogateDiagTailX0RatChunk001Sub001Block086Part012

theorem surrogateDiagonalTailChunk001Sub001Block086Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block086Part012CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block086Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block086Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block086Part012CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block086Part012SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block086Part012] using hcert

def TailChunk001Sub001Block086Part013SupportExplicit : Finset ℕ :=
  ([28285] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block086Part013 : ℚ :=
  (666882160125 : ℚ) / 218365071725306576896

def SurrogateDiagonalTailChunk001Sub001Block086Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28285
    = surrogateDiagTailX0RatChunk001Sub001Block086Part013

theorem surrogateDiagonalTailChunk001Sub001Block086Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block086Part013CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block086Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block086Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block086Part013CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block086Part013SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block086Part013] using hcert

def TailChunk001Sub001Block086Part014SupportExplicit : Finset ℕ :=
  ([28286] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block086Part014 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block086Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28286
    = surrogateDiagTailX0RatChunk001Sub001Block086Part014

theorem surrogateDiagonalTailChunk001Sub001Block086Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block086Part014CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block086Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block086Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block086Part014CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block086Part014SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block086Part014] using hcert

def TailChunk001Sub001Block086Part015SupportExplicit : Finset ℕ :=
  ([28289] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block086Part015 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block086Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28289
    = surrogateDiagTailX0RatChunk001Sub001Block086Part015

theorem surrogateDiagonalTailChunk001Sub001Block086Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block086Part015CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block086Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block086Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block086Part015CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block086Part015SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block086Part015] using hcert

def TailChunk001Sub001Block086Part016SupportExplicit : Finset ℕ :=
  ([28290] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block086Part016 : ℚ :=
  (56222610421 : ℚ) / 245684346499891200

def SurrogateDiagonalTailChunk001Sub001Block086Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28290
    = surrogateDiagTailX0RatChunk001Sub001Block086Part016

theorem surrogateDiagonalTailChunk001Sub001Block086Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block086Part016CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block086Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block086Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block086Part016CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block086Part016SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block086Part016] using hcert

def TailChunk001Sub001Block086Part017SupportExplicit : Finset ℕ :=
  ([28291] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block086Part017 : ℚ :=
  (62091847525 : ℚ) / 142983556306844516352

def SurrogateDiagonalTailChunk001Sub001Block086Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28291
    = surrogateDiagTailX0RatChunk001Sub001Block086Part017

theorem surrogateDiagonalTailChunk001Sub001Block086Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block086Part017CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block086Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block086Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block086Part017CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block086Part017SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block086Part017] using hcert

def TailChunk001Sub001Block086Part018SupportExplicit : Finset ℕ :=
  ([28293] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block086Part018 : ℚ :=
  (5001 : ℚ) / 2530444108803200

def SurrogateDiagonalTailChunk001Sub001Block086Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28293
    = surrogateDiagTailX0RatChunk001Sub001Block086Part018

theorem surrogateDiagonalTailChunk001Sub001Block086Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block086Part018CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block086Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block086Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block086Part018CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block086Part018SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block086Part018] using hcert

def TailChunk001Sub001Block086Part019SupportExplicit : Finset ℕ :=
  ([28294] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block086Part019 : ℚ :=
  (104320186475 : ℚ) / 7525044947750980608

def SurrogateDiagonalTailChunk001Sub001Block086Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28294
    = surrogateDiagTailX0RatChunk001Sub001Block086Part019

theorem surrogateDiagonalTailChunk001Sub001Block086Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block086Part019CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block086Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block086Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block086Part019CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block086Part019SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block086Part019] using hcert

def TailChunk001Sub001Block086Part020SupportExplicit : Finset ℕ :=
  ([28295] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block086Part020 : ℚ :=
  (2002060730125 : ℚ) / 656022291224389797888

def SurrogateDiagonalTailChunk001Sub001Block086Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28295
    = surrogateDiagTailX0RatChunk001Sub001Block086Part020

theorem surrogateDiagonalTailChunk001Sub001Block086Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block086Part020CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block086Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block086Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block086Part020CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block086Part020SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block086Part020] using hcert

def TailChunk001Sub001Block086Part021SupportExplicit : Finset ℕ :=
  ([28297] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block086Part021 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block086Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28297
    = surrogateDiagTailX0RatChunk001Sub001Block086Part021

theorem surrogateDiagonalTailChunk001Sub001Block086Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block086Part021CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block086Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block086Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block086Part021CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block086Part021SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block086Part021] using hcert

def TailChunk001Sub001Block086Part022SupportExplicit : Finset ℕ :=
  ([28298] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block086Part022 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block086Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28298
    = surrogateDiagTailX0RatChunk001Sub001Block086Part022

theorem surrogateDiagonalTailChunk001Sub001Block086Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block086Part022CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block086Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block086Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block086Part022CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block086Part022SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block086Part022] using hcert

def TailChunk001Sub001Block086Part023SupportExplicit : Finset ℕ :=
  ([28299] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block086Part023 : ℚ :=
  (41675 : ℚ) / 21104929250574336

def SurrogateDiagonalTailChunk001Sub001Block086Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28299
    = surrogateDiagTailX0RatChunk001Sub001Block086Part023

theorem surrogateDiagonalTailChunk001Sub001Block086Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block086Part023CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block086Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block086Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block086Part023CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block086Part023SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block086Part023] using hcert

def TailChunk001Sub001Block086Part024SupportExplicit : Finset ℕ :=
  ([28301] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block086Part024 : ℚ :=
  (6990350201 : ℚ) / 3102941760131174400

def SurrogateDiagonalTailChunk001Sub001Block086Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28301
    = surrogateDiagTailX0RatChunk001Sub001Block086Part024

theorem surrogateDiagonalTailChunk001Sub001Block086Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block086Part024CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block086Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block086Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block086Part024CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block086Part024SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block086Part024] using hcert

def surrogateDiagonalTailChunk001Sub001Block086HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub001Block086Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block086Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block086Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block086Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block086Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block086Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block086Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block086Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block086Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block086Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub001Block086Head : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block086Part000
    + surrogateDiagTailX0RatChunk001Sub001Block086Part001
    + surrogateDiagTailX0RatChunk001Sub001Block086Part002
    + surrogateDiagTailX0RatChunk001Sub001Block086Part003
    + surrogateDiagTailX0RatChunk001Sub001Block086Part004
    + surrogateDiagTailX0RatChunk001Sub001Block086Part005
    + surrogateDiagTailX0RatChunk001Sub001Block086Part006
    + surrogateDiagTailX0RatChunk001Sub001Block086Part007
    + surrogateDiagTailX0RatChunk001Sub001Block086Part008
    + surrogateDiagTailX0RatChunk001Sub001Block086Part009

def surrogateDiagonalTailChunk001Sub001Block086MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub001Block086Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block086Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block086Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block086Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block086Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block086Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block086Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block086Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block086Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block086Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub001Block086Mid : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block086Part010
    + surrogateDiagTailX0RatChunk001Sub001Block086Part011
    + surrogateDiagTailX0RatChunk001Sub001Block086Part012
    + surrogateDiagTailX0RatChunk001Sub001Block086Part013
    + surrogateDiagTailX0RatChunk001Sub001Block086Part014
    + surrogateDiagTailX0RatChunk001Sub001Block086Part015
    + surrogateDiagTailX0RatChunk001Sub001Block086Part016
    + surrogateDiagTailX0RatChunk001Sub001Block086Part017
    + surrogateDiagTailX0RatChunk001Sub001Block086Part018
    + surrogateDiagTailX0RatChunk001Sub001Block086Part019

def surrogateDiagonalTailChunk001Sub001Block086TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub001Block086Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block086Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block086Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block086Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block086Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub001Block086Tail : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block086Part020
    + surrogateDiagTailX0RatChunk001Sub001Block086Part021
    + surrogateDiagTailX0RatChunk001Sub001Block086Part022
    + surrogateDiagTailX0RatChunk001Sub001Block086Part023
    + surrogateDiagTailX0RatChunk001Sub001Block086Part024

def surrogateDiagonalTailChunk001Sub001Block086Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk001Sub001Block086HeadSum X0
    + surrogateDiagonalTailChunk001Sub001Block086MidSum X0
    + surrogateDiagonalTailChunk001Sub001Block086TailSum X0

def surrogateDiagTailX0RatChunk001Sub001Block086 : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block086Part000
    + surrogateDiagTailX0RatChunk001Sub001Block086Part001
    + surrogateDiagTailX0RatChunk001Sub001Block086Part002
    + surrogateDiagTailX0RatChunk001Sub001Block086Part003
    + surrogateDiagTailX0RatChunk001Sub001Block086Part004
    + surrogateDiagTailX0RatChunk001Sub001Block086Part005
    + surrogateDiagTailX0RatChunk001Sub001Block086Part006
    + surrogateDiagTailX0RatChunk001Sub001Block086Part007
    + surrogateDiagTailX0RatChunk001Sub001Block086Part008
    + surrogateDiagTailX0RatChunk001Sub001Block086Part009
    + surrogateDiagTailX0RatChunk001Sub001Block086Part010
    + surrogateDiagTailX0RatChunk001Sub001Block086Part011
    + surrogateDiagTailX0RatChunk001Sub001Block086Part012
    + surrogateDiagTailX0RatChunk001Sub001Block086Part013
    + surrogateDiagTailX0RatChunk001Sub001Block086Part014
    + surrogateDiagTailX0RatChunk001Sub001Block086Part015
    + surrogateDiagTailX0RatChunk001Sub001Block086Part016
    + surrogateDiagTailX0RatChunk001Sub001Block086Part017
    + surrogateDiagTailX0RatChunk001Sub001Block086Part018
    + surrogateDiagTailX0RatChunk001Sub001Block086Part019
    + surrogateDiagTailX0RatChunk001Sub001Block086Part020
    + surrogateDiagTailX0RatChunk001Sub001Block086Part021
    + surrogateDiagTailX0RatChunk001Sub001Block086Part022
    + surrogateDiagTailX0RatChunk001Sub001Block086Part023
    + surrogateDiagTailX0RatChunk001Sub001Block086Part024

theorem surrogateDiagTailX0RatChunk001Sub001Block086_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk001Sub001Block086Head + surrogateDiagTailX0RatChunk001Sub001Block086Mid + surrogateDiagTailX0RatChunk001Sub001Block086Tail =
      surrogateDiagTailX0RatChunk001Sub001Block086 := by
  unfold surrogateDiagTailX0RatChunk001Sub001Block086Head surrogateDiagTailX0RatChunk001Sub001Block086Mid surrogateDiagTailX0RatChunk001Sub001Block086Tail surrogateDiagTailX0RatChunk001Sub001Block086
  ring

def SurrogateDiagonalTailChunk001Sub001Block086HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub001Block086HeadSum X0 = surrogateDiagTailX0RatChunk001Sub001Block086Head

def SurrogateDiagonalTailChunk001Sub001Block086MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub001Block086MidSum X0 = surrogateDiagTailX0RatChunk001Sub001Block086Mid

def SurrogateDiagonalTailChunk001Sub001Block086TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub001Block086TailSum X0 = surrogateDiagTailX0RatChunk001Sub001Block086Tail

theorem surrogateDiagonalTailChunk001Sub001Block086_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk001Sub001Block086HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk001Sub001Block086MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk001Sub001Block086TailCertificateAt X0) :
    surrogateDiagonalTailChunk001Sub001Block086Sum X0 = surrogateDiagTailX0RatChunk001Sub001Block086 := by
  unfold SurrogateDiagonalTailChunk001Sub001Block086HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk001Sub001Block086MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk001Sub001Block086TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk001Sub001Block086Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk001Sub001Block086_eq_head_add_mid_add_tail

/-- Block 087 covers tail-support indices [17175,17200) and q from 28302 to 28342. -/

def TailChunk001Sub001Block087Part000SupportExplicit : Finset ℕ :=
  ([28302] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block087Part000 : ℚ :=
  (2703642993325 : ℚ) / 17542476550958481408

def SurrogateDiagonalTailChunk001Sub001Block087Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28302
    = surrogateDiagTailX0RatChunk001Sub001Block087Part000

theorem surrogateDiagonalTailChunk001Sub001Block087Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block087Part000CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block087Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block087Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block087Part000CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block087Part000SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block087Part000] using hcert

def TailChunk001Sub001Block087Part001SupportExplicit : Finset ℕ :=
  ([28303] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block087Part001 : ℚ :=
  (44808245833 : ℚ) / 36629186932512000000

def SurrogateDiagonalTailChunk001Sub001Block087Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28303
    = surrogateDiagTailX0RatChunk001Sub001Block087Part001

theorem surrogateDiagonalTailChunk001Sub001Block087Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block087Part001CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block087Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block087Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block087Part001CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block087Part001SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block087Part001] using hcert

def TailChunk001Sub001Block087Part002SupportExplicit : Finset ℕ :=
  ([28306] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block087Part002 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block087Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28306
    = surrogateDiagTailX0RatChunk001Sub001Block087Part002

theorem surrogateDiagonalTailChunk001Sub001Block087Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block087Part002CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block087Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block087Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block087Part002CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block087Part002SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block087Part002] using hcert

def TailChunk001Sub001Block087Part003SupportExplicit : Finset ℕ :=
  ([28307] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block087Part003 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block087Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28307
    = surrogateDiagTailX0RatChunk001Sub001Block087Part003

theorem surrogateDiagonalTailChunk001Sub001Block087Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block087Part003CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block087Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block087Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block087Part003CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block087Part003SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block087Part003] using hcert

def TailChunk001Sub001Block087Part004SupportExplicit : Finset ℕ :=
  ([28309] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block087Part004 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block087Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28309
    = surrogateDiagTailX0RatChunk001Sub001Block087Part004

theorem surrogateDiagonalTailChunk001Sub001Block087Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block087Part004CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block087Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block087Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block087Part004CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block087Part004SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block087Part004] using hcert

def TailChunk001Sub001Block087Part005SupportExplicit : Finset ℕ :=
  ([28310] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block087Part005 : ℚ :=
  (1076290589875 : ℚ) / 32240643853685096448

def SurrogateDiagonalTailChunk001Sub001Block087Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28310
    = surrogateDiagTailX0RatChunk001Sub001Block087Part005

theorem surrogateDiagonalTailChunk001Sub001Block087Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block087Part005CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block087Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block087Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block087Part005CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block087Part005SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block087Part005] using hcert

def TailChunk001Sub001Block087Part006SupportExplicit : Finset ℕ :=
  ([28311] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block087Part006 : ℚ :=
  (49692017425 : ℚ) / 2831917177076098944

def SurrogateDiagonalTailChunk001Sub001Block087Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28311
    = surrogateDiagTailX0RatChunk001Sub001Block087Part006

theorem surrogateDiagonalTailChunk001Sub001Block087Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block087Part006CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block087Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block087Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block087Part006CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block087Part006SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block087Part006] using hcert

def TailChunk001Sub001Block087Part007SupportExplicit : Finset ℕ :=
  ([28313] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block087Part007 : ℚ :=
  (2565754501 : ℚ) / 8938132097981803200

def SurrogateDiagonalTailChunk001Sub001Block087Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28313
    = surrogateDiagTailX0RatChunk001Sub001Block087Part007

theorem surrogateDiagonalTailChunk001Sub001Block087Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block087Part007CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block087Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block087Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block087Part007CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block087Part007SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block087Part007] using hcert

def TailChunk001Sub001Block087Part008SupportExplicit : Finset ℕ :=
  ([28315] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block087Part008 : ℚ :=
  (31842905375 : ℚ) / 4911167793905270784

def SurrogateDiagonalTailChunk001Sub001Block087Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28315
    = surrogateDiagTailX0RatChunk001Sub001Block087Part008

theorem surrogateDiagonalTailChunk001Sub001Block087Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block087Part008CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block087Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block087Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block087Part008CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block087Part008SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block087Part008] using hcert

def TailChunk001Sub001Block087Part009SupportExplicit : Finset ℕ :=
  ([28317] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block087Part009 : ℚ :=
  (2783932600775 : ℚ) / 158721857710183969344

def SurrogateDiagonalTailChunk001Sub001Block087Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28317
    = surrogateDiagTailX0RatChunk001Sub001Block087Part009

theorem surrogateDiagonalTailChunk001Sub001Block087Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block087Part009CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block087Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block087Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block087Part009CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block087Part009SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block087Part009] using hcert

def TailChunk001Sub001Block087Part010SupportExplicit : Finset ℕ :=
  ([28318] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block087Part010 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block087Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28318
    = surrogateDiagTailX0RatChunk001Sub001Block087Part010

theorem surrogateDiagonalTailChunk001Sub001Block087Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block087Part010CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block087Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block087Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block087Part010CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block087Part010SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block087Part010] using hcert

def TailChunk001Sub001Block087Part011SupportExplicit : Finset ℕ :=
  ([28319] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block087Part011 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block087Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28319
    = surrogateDiagTailX0RatChunk001Sub001Block087Part011

theorem surrogateDiagonalTailChunk001Sub001Block087Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block087Part011CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block087Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block087Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block087Part011CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block087Part011SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block087Part011] using hcert

def TailChunk001Sub001Block087Part012SupportExplicit : Finset ℕ :=
  ([28321] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block087Part012 : ℚ :=
  (53249176175 : ℚ) / 765404377112857817664

def SurrogateDiagonalTailChunk001Sub001Block087Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28321
    = surrogateDiagTailX0RatChunk001Sub001Block087Part012

theorem surrogateDiagonalTailChunk001Sub001Block087Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block087Part012CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block087Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block087Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block087Part012CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block087Part012SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block087Part012] using hcert

def TailChunk001Sub001Block087Part013SupportExplicit : Finset ℕ :=
  ([28326] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block087Part013 : ℚ :=
  (2786050139 : ℚ) / 39714109758504960

def SurrogateDiagonalTailChunk001Sub001Block087Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28326
    = surrogateDiagTailX0RatChunk001Sub001Block087Part013

theorem surrogateDiagonalTailChunk001Sub001Block087Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block087Part013CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block087Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block087Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block087Part013CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block087Part013SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block087Part013] using hcert

def TailChunk001Sub001Block087Part014SupportExplicit : Finset ℕ :=
  ([28327] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block087Part014 : ℚ :=
  (22096125175 : ℚ) / 43213513726913992704

def SurrogateDiagonalTailChunk001Sub001Block087Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28327
    = surrogateDiagTailX0RatChunk001Sub001Block087Part014

theorem surrogateDiagonalTailChunk001Sub001Block087Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block087Part014CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block087Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block087Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block087Part014CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block087Part014SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block087Part014] using hcert

def TailChunk001Sub001Block087Part015SupportExplicit : Finset ℕ :=
  ([28329] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block087Part015 : ℚ :=
  (178642726921 : ℚ) / 5227499679613747200

def SurrogateDiagonalTailChunk001Sub001Block087Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28329
    = surrogateDiagTailX0RatChunk001Sub001Block087Part015

theorem surrogateDiagonalTailChunk001Sub001Block087Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block087Part015CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block087Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block087Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block087Part015CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block087Part015SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block087Part015] using hcert

def TailChunk001Sub001Block087Part016SupportExplicit : Finset ℕ :=
  ([28330] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block087Part016 : ℚ :=
  (334525923175 : ℚ) / 13725196332539314176

def SurrogateDiagonalTailChunk001Sub001Block087Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28330
    = surrogateDiagTailX0RatChunk001Sub001Block087Part016

theorem surrogateDiagonalTailChunk001Sub001Block087Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block087Part016CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block087Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block087Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block087Part016CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block087Part016SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block087Part016] using hcert

def TailChunk001Sub001Block087Part017SupportExplicit : Finset ℕ :=
  ([28331] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block087Part017 : ℚ :=
  (551374579 : ℚ) / 3627464707872000000

def SurrogateDiagonalTailChunk001Sub001Block087Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28331
    = surrogateDiagTailX0RatChunk001Sub001Block087Part017

theorem surrogateDiagonalTailChunk001Sub001Block087Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block087Part017CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block087Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block087Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block087Part017CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block087Part017SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block087Part017] using hcert

def TailChunk001Sub001Block087Part018SupportExplicit : Finset ℕ :=
  ([28333] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block087Part018 : ℚ :=
  (25514506425 : ℚ) / 116218966446696300544

def SurrogateDiagonalTailChunk001Sub001Block087Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28333
    = surrogateDiagTailX0RatChunk001Sub001Block087Part018

theorem surrogateDiagonalTailChunk001Sub001Block087Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block087Part018CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block087Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block087Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block087Part018CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block087Part018SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block087Part018] using hcert

def TailChunk001Sub001Block087Part019SupportExplicit : Finset ℕ :=
  ([28334] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block087Part019 : ℚ :=
  (1520298967 : ℚ) / 875732058333388800

def SurrogateDiagonalTailChunk001Sub001Block087Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28334
    = surrogateDiagTailX0RatChunk001Sub001Block087Part019

theorem surrogateDiagonalTailChunk001Sub001Block087Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block087Part019CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block087Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block087Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block087Part019CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block087Part019SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block087Part019] using hcert

def TailChunk001Sub001Block087Part020SupportExplicit : Finset ℕ :=
  ([28335] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block087Part020 : ℚ :=
  (780131044125 : ℚ) / 21689199142778175488

def SurrogateDiagonalTailChunk001Sub001Block087Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28335
    = surrogateDiagTailX0RatChunk001Sub001Block087Part020

theorem surrogateDiagonalTailChunk001Sub001Block087Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block087Part020CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block087Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block087Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block087Part020CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block087Part020SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block087Part020] using hcert

def TailChunk001Sub001Block087Part021SupportExplicit : Finset ℕ :=
  ([28337] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block087Part021 : ℚ :=
  (114690273575 : ℚ) / 729285534369113085504

def SurrogateDiagonalTailChunk001Sub001Block087Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28337
    = surrogateDiagTailX0RatChunk001Sub001Block087Part021

theorem surrogateDiagonalTailChunk001Sub001Block087Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block087Part021CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block087Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block087Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block087Part021CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block087Part021SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block087Part021] using hcert

def TailChunk001Sub001Block087Part022SupportExplicit : Finset ℕ :=
  ([28338] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block087Part022 : ℚ :=
  (697102659725 : ℚ) / 9945366151028226624

def SurrogateDiagonalTailChunk001Sub001Block087Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28338
    = surrogateDiagTailX0RatChunk001Sub001Block087Part022

theorem surrogateDiagonalTailChunk001Sub001Block087Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block087Part022CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block087Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block087Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block087Part022CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block087Part022SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block087Part022] using hcert

def TailChunk001Sub001Block087Part023SupportExplicit : Finset ℕ :=
  ([28339] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block087Part023 : ℚ :=
  (52541775 : ℚ) / 126293363678117888

def SurrogateDiagonalTailChunk001Sub001Block087Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28339
    = surrogateDiagTailX0RatChunk001Sub001Block087Part023

theorem surrogateDiagonalTailChunk001Sub001Block087Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block087Part023CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block087Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block087Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block087Part023CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block087Part023SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block087Part023] using hcert

def TailChunk001Sub001Block087Part024SupportExplicit : Finset ℕ :=
  ([28342] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block087Part024 : ℚ :=
  (32379597175 : ℚ) / 22357864628283658752

def SurrogateDiagonalTailChunk001Sub001Block087Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28342
    = surrogateDiagTailX0RatChunk001Sub001Block087Part024

theorem surrogateDiagonalTailChunk001Sub001Block087Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block087Part024CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block087Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block087Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block087Part024CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block087Part024SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block087Part024] using hcert

def surrogateDiagonalTailChunk001Sub001Block087HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub001Block087Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block087Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block087Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block087Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block087Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block087Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block087Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block087Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block087Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block087Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub001Block087Head : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block087Part000
    + surrogateDiagTailX0RatChunk001Sub001Block087Part001
    + surrogateDiagTailX0RatChunk001Sub001Block087Part002
    + surrogateDiagTailX0RatChunk001Sub001Block087Part003
    + surrogateDiagTailX0RatChunk001Sub001Block087Part004
    + surrogateDiagTailX0RatChunk001Sub001Block087Part005
    + surrogateDiagTailX0RatChunk001Sub001Block087Part006
    + surrogateDiagTailX0RatChunk001Sub001Block087Part007
    + surrogateDiagTailX0RatChunk001Sub001Block087Part008
    + surrogateDiagTailX0RatChunk001Sub001Block087Part009

def surrogateDiagonalTailChunk001Sub001Block087MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub001Block087Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block087Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block087Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block087Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block087Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block087Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block087Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block087Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block087Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block087Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub001Block087Mid : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block087Part010
    + surrogateDiagTailX0RatChunk001Sub001Block087Part011
    + surrogateDiagTailX0RatChunk001Sub001Block087Part012
    + surrogateDiagTailX0RatChunk001Sub001Block087Part013
    + surrogateDiagTailX0RatChunk001Sub001Block087Part014
    + surrogateDiagTailX0RatChunk001Sub001Block087Part015
    + surrogateDiagTailX0RatChunk001Sub001Block087Part016
    + surrogateDiagTailX0RatChunk001Sub001Block087Part017
    + surrogateDiagTailX0RatChunk001Sub001Block087Part018
    + surrogateDiagTailX0RatChunk001Sub001Block087Part019

def surrogateDiagonalTailChunk001Sub001Block087TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub001Block087Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block087Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block087Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block087Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block087Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub001Block087Tail : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block087Part020
    + surrogateDiagTailX0RatChunk001Sub001Block087Part021
    + surrogateDiagTailX0RatChunk001Sub001Block087Part022
    + surrogateDiagTailX0RatChunk001Sub001Block087Part023
    + surrogateDiagTailX0RatChunk001Sub001Block087Part024

def surrogateDiagonalTailChunk001Sub001Block087Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk001Sub001Block087HeadSum X0
    + surrogateDiagonalTailChunk001Sub001Block087MidSum X0
    + surrogateDiagonalTailChunk001Sub001Block087TailSum X0

def surrogateDiagTailX0RatChunk001Sub001Block087 : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block087Part000
    + surrogateDiagTailX0RatChunk001Sub001Block087Part001
    + surrogateDiagTailX0RatChunk001Sub001Block087Part002
    + surrogateDiagTailX0RatChunk001Sub001Block087Part003
    + surrogateDiagTailX0RatChunk001Sub001Block087Part004
    + surrogateDiagTailX0RatChunk001Sub001Block087Part005
    + surrogateDiagTailX0RatChunk001Sub001Block087Part006
    + surrogateDiagTailX0RatChunk001Sub001Block087Part007
    + surrogateDiagTailX0RatChunk001Sub001Block087Part008
    + surrogateDiagTailX0RatChunk001Sub001Block087Part009
    + surrogateDiagTailX0RatChunk001Sub001Block087Part010
    + surrogateDiagTailX0RatChunk001Sub001Block087Part011
    + surrogateDiagTailX0RatChunk001Sub001Block087Part012
    + surrogateDiagTailX0RatChunk001Sub001Block087Part013
    + surrogateDiagTailX0RatChunk001Sub001Block087Part014
    + surrogateDiagTailX0RatChunk001Sub001Block087Part015
    + surrogateDiagTailX0RatChunk001Sub001Block087Part016
    + surrogateDiagTailX0RatChunk001Sub001Block087Part017
    + surrogateDiagTailX0RatChunk001Sub001Block087Part018
    + surrogateDiagTailX0RatChunk001Sub001Block087Part019
    + surrogateDiagTailX0RatChunk001Sub001Block087Part020
    + surrogateDiagTailX0RatChunk001Sub001Block087Part021
    + surrogateDiagTailX0RatChunk001Sub001Block087Part022
    + surrogateDiagTailX0RatChunk001Sub001Block087Part023
    + surrogateDiagTailX0RatChunk001Sub001Block087Part024

theorem surrogateDiagTailX0RatChunk001Sub001Block087_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk001Sub001Block087Head + surrogateDiagTailX0RatChunk001Sub001Block087Mid + surrogateDiagTailX0RatChunk001Sub001Block087Tail =
      surrogateDiagTailX0RatChunk001Sub001Block087 := by
  unfold surrogateDiagTailX0RatChunk001Sub001Block087Head surrogateDiagTailX0RatChunk001Sub001Block087Mid surrogateDiagTailX0RatChunk001Sub001Block087Tail surrogateDiagTailX0RatChunk001Sub001Block087
  ring

def SurrogateDiagonalTailChunk001Sub001Block087HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub001Block087HeadSum X0 = surrogateDiagTailX0RatChunk001Sub001Block087Head

def SurrogateDiagonalTailChunk001Sub001Block087MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub001Block087MidSum X0 = surrogateDiagTailX0RatChunk001Sub001Block087Mid

def SurrogateDiagonalTailChunk001Sub001Block087TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub001Block087TailSum X0 = surrogateDiagTailX0RatChunk001Sub001Block087Tail

theorem surrogateDiagonalTailChunk001Sub001Block087_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk001Sub001Block087HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk001Sub001Block087MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk001Sub001Block087TailCertificateAt X0) :
    surrogateDiagonalTailChunk001Sub001Block087Sum X0 = surrogateDiagTailX0RatChunk001Sub001Block087 := by
  unfold SurrogateDiagonalTailChunk001Sub001Block087HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk001Sub001Block087MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk001Sub001Block087TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk001Sub001Block087Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk001Sub001Block087_eq_head_add_mid_add_tail

/-- Block 088 covers tail-support indices [17200,17225) and q from 28343 to 28382. -/

def TailChunk001Sub001Block088Part000SupportExplicit : Finset ℕ :=
  ([28343] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block088Part000 : ℚ :=
  (1026018952225 : ℚ) / 870149501549837549568

def SurrogateDiagonalTailChunk001Sub001Block088Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28343
    = surrogateDiagTailX0RatChunk001Sub001Block088Part000

theorem surrogateDiagonalTailChunk001Sub001Block088Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block088Part000CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block088Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block088Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block088Part000CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block088Part000SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block088Part000] using hcert

def TailChunk001Sub001Block088Part001SupportExplicit : Finset ℕ :=
  ([28345] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block088Part001 : ℚ :=
  (669713159625 : ℚ) / 220224146635066802176

def SurrogateDiagonalTailChunk001Sub001Block088Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28345
    = surrogateDiagTailX0RatChunk001Sub001Block088Part001

theorem surrogateDiagonalTailChunk001Sub001Block088Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block088Part001CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block088Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block088Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block088Part001CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block088Part001SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block088Part001] using hcert

def TailChunk001Sub001Block088Part002SupportExplicit : Finset ℕ :=
  ([28346] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block088Part002 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block088Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28346
    = surrogateDiagTailX0RatChunk001Sub001Block088Part002

theorem surrogateDiagonalTailChunk001Sub001Block088Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block088Part002CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block088Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block088Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block088Part002CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block088Part002SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block088Part002] using hcert

def TailChunk001Sub001Block088Part003SupportExplicit : Finset ℕ :=
  ([28347] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block088Part003 : ℚ :=
  (98591772767 : ℚ) / 4336366579063833600

def SurrogateDiagonalTailChunk001Sub001Block088Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28347
    = surrogateDiagTailX0RatChunk001Sub001Block088Part003

theorem surrogateDiagonalTailChunk001Sub001Block088Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block088Part003CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block088Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block088Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block088Part003CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block088Part003SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block088Part003] using hcert

def TailChunk001Sub001Block088Part004SupportExplicit : Finset ℕ :=
  ([28349] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block088Part004 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block088Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28349
    = surrogateDiagTailX0RatChunk001Sub001Block088Part004

theorem surrogateDiagonalTailChunk001Sub001Block088Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block088Part004CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block088Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block088Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block088Part004CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block088Part004SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block088Part004] using hcert

def TailChunk001Sub001Block088Part005SupportExplicit : Finset ℕ :=
  ([28351] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block088Part005 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block088Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28351
    = surrogateDiagTailX0RatChunk001Sub001Block088Part005

theorem surrogateDiagonalTailChunk001Sub001Block088Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block088Part005CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block088Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block088Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block088Part005CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block088Part005SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block088Part005] using hcert

def TailChunk001Sub001Block088Part006SupportExplicit : Finset ℕ :=
  ([28353] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block088Part006 : ℚ :=
  (2573280044675 : ℚ) / 115236036605103980544

def SurrogateDiagonalTailChunk001Sub001Block088Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28353
    = surrogateDiagTailX0RatChunk001Sub001Block088Part006

theorem surrogateDiagonalTailChunk001Sub001Block088Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block088Part006CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block088Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block088Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block088Part006CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block088Part006SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block088Part006] using hcert

def TailChunk001Sub001Block088Part007SupportExplicit : Finset ℕ :=
  ([28354] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block088Part007 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block088Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28354
    = surrogateDiagTailX0RatChunk001Sub001Block088Part007

theorem surrogateDiagonalTailChunk001Sub001Block088Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block088Part007CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block088Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block088Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block088Part007CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block088Part007SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block088Part007] using hcert

def TailChunk001Sub001Block088Part008SupportExplicit : Finset ℕ :=
  ([28355] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block088Part008 : ℚ :=
  (2091304749025 : ℚ) / 590885944941787742208

def SurrogateDiagonalTailChunk001Sub001Block088Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28355
    = surrogateDiagTailX0RatChunk001Sub001Block088Part008

theorem surrogateDiagonalTailChunk001Sub001Block088Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block088Part008CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block088Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block088Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block088Part008CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block088Part008SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block088Part008] using hcert

def TailChunk001Sub001Block088Part009SupportExplicit : Finset ℕ :=
  ([28357] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block088Part009 : ℚ :=
  (41081248093 : ℚ) / 34874817578802000000

def SurrogateDiagonalTailChunk001Sub001Block088Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28357
    = surrogateDiagTailX0RatChunk001Sub001Block088Part009

theorem surrogateDiagonalTailChunk001Sub001Block088Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block088Part009CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block088Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block088Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block088Part009CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block088Part009SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block088Part009] using hcert

def TailChunk001Sub001Block088Part010SupportExplicit : Finset ℕ :=
  ([28358] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block088Part010 : ℚ :=
  (5568191703 : ℚ) / 917548538058342400

def SurrogateDiagonalTailChunk001Sub001Block088Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28358
    = surrogateDiagTailX0RatChunk001Sub001Block088Part010

theorem surrogateDiagonalTailChunk001Sub001Block088Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block088Part010CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block088Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block088Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block088Part010CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block088Part010SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block088Part010] using hcert

def TailChunk001Sub001Block088Part011SupportExplicit : Finset ℕ :=
  ([28361] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block088Part011 : ℚ :=
  (68060765675 : ℚ) / 760164143893355732544

def SurrogateDiagonalTailChunk001Sub001Block088Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28361
    = surrogateDiagTailX0RatChunk001Sub001Block088Part011

theorem surrogateDiagonalTailChunk001Sub001Block088Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block088Part011CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block088Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block088Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block088Part011CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block088Part011SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block088Part011] using hcert

def TailChunk001Sub001Block088Part012SupportExplicit : Finset ℕ :=
  ([28362] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block088Part012 : ℚ :=
  (1401752205475 : ℚ) / 16937098961948540928

def SurrogateDiagonalTailChunk001Sub001Block088Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28362
    = surrogateDiagTailX0RatChunk001Sub001Block088Part012

theorem surrogateDiagonalTailChunk001Sub001Block088Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block088Part012CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block088Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block088Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block088Part012CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block088Part012SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block088Part012] using hcert

def TailChunk001Sub001Block088Part013SupportExplicit : Finset ℕ :=
  ([28363] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block088Part013 : ℚ :=
  (2190697577 : ℚ) / 30738946560000000000

def SurrogateDiagonalTailChunk001Sub001Block088Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28363
    = surrogateDiagTailX0RatChunk001Sub001Block088Part013

theorem surrogateDiagonalTailChunk001Sub001Block088Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block088Part013CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block088Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block088Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block088Part013CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block088Part013SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block088Part013] using hcert

def TailChunk001Sub001Block088Part014SupportExplicit : Finset ℕ :=
  ([28365] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block088Part014 : ℚ :=
  (178558689991 : ℚ) / 4300676923392000000

def SurrogateDiagonalTailChunk001Sub001Block088Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28365
    = surrogateDiagTailX0RatChunk001Sub001Block088Part014

theorem surrogateDiagonalTailChunk001Sub001Block088Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block088Part014CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block088Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block088Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block088Part014CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block088Part014SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block088Part014] using hcert

def TailChunk001Sub001Block088Part015SupportExplicit : Finset ℕ :=
  ([28366] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block088Part015 : ℚ :=
  (2003999419 : ℚ) / 487940172936883200

def SurrogateDiagonalTailChunk001Sub001Block088Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28366
    = surrogateDiagTailX0RatChunk001Sub001Block088Part015

theorem surrogateDiagonalTailChunk001Sub001Block088Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block088Part015CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block088Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block088Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block088Part015CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block088Part015SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block088Part015] using hcert

def TailChunk001Sub001Block088Part016SupportExplicit : Finset ℕ :=
  ([28367] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block088Part016 : ℚ :=
  (561804839725 : ℚ) / 1300745020003878094848

def SurrogateDiagonalTailChunk001Sub001Block088Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28367
    = surrogateDiagTailX0RatChunk001Sub001Block088Part016

theorem surrogateDiagonalTailChunk001Sub001Block088Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block088Part016CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block088Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block088Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block088Part016CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block088Part016SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block088Part016] using hcert

def TailChunk001Sub001Block088Part017SupportExplicit : Finset ℕ :=
  ([28369] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block088Part017 : ℚ :=
  (1042152437 : ℚ) / 1380602081923844100

def SurrogateDiagonalTailChunk001Sub001Block088Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28369
    = surrogateDiagTailX0RatChunk001Sub001Block088Part017

theorem surrogateDiagonalTailChunk001Sub001Block088Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block088Part017CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block088Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block088Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block088Part017CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block088Part017SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block088Part017] using hcert

def TailChunk001Sub001Block088Part018SupportExplicit : Finset ℕ :=
  ([28370] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block088Part018 : ℚ :=
  (1006411201525 : ℚ) / 41408712769298792448

def SurrogateDiagonalTailChunk001Sub001Block088Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28370
    = surrogateDiagTailX0RatChunk001Sub001Block088Part018

theorem surrogateDiagonalTailChunk001Sub001Block088Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block088Part018CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block088Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block088Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block088Part018CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block088Part018SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block088Part018] using hcert

def TailChunk001Sub001Block088Part019SupportExplicit : Finset ℕ :=
  ([28373] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block088Part019 : ℚ :=
  (913988425 : ℚ) / 2202259495894253568

def SurrogateDiagonalTailChunk001Sub001Block088Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28373
    = surrogateDiagTailX0RatChunk001Sub001Block088Part019

theorem surrogateDiagonalTailChunk001Sub001Block088Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block088Part019CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block088Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block088Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block088Part019CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block088Part019SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block088Part019] using hcert

def TailChunk001Sub001Block088Part020SupportExplicit : Finset ℕ :=
  ([28374] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block088Part020 : ℚ :=
  (349437267325 : ℚ) / 4998005407923904512

def SurrogateDiagonalTailChunk001Sub001Block088Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28374
    = surrogateDiagTailX0RatChunk001Sub001Block088Part020

theorem surrogateDiagonalTailChunk001Sub001Block088Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block088Part020CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block088Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block088Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block088Part020CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block088Part020SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block088Part020] using hcert

def TailChunk001Sub001Block088Part021SupportExplicit : Finset ℕ :=
  ([28378] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block088Part021 : ℚ :=
  (42844084675 : ℚ) / 3033312252838019136

def SurrogateDiagonalTailChunk001Sub001Block088Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28378
    = surrogateDiagTailX0RatChunk001Sub001Block088Part021

theorem surrogateDiagonalTailChunk001Sub001Block088Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block088Part021CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block088Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block088Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block088Part021CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block088Part021SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block088Part021] using hcert

def TailChunk001Sub001Block088Part022SupportExplicit : Finset ℕ :=
  ([28379] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block088Part022 : ℚ :=
  (902993926975 : ℚ) / 985539012317371957248

def SurrogateDiagonalTailChunk001Sub001Block088Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28379
    = surrogateDiagTailX0RatChunk001Sub001Block088Part022

theorem surrogateDiagonalTailChunk001Sub001Block088Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block088Part022CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block088Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block088Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block088Part022CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block088Part022SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block088Part022] using hcert

def TailChunk001Sub001Block088Part023SupportExplicit : Finset ℕ :=
  ([28381] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block088Part023 : ℚ :=
  (2389124921 : ℚ) / 30738946560000000000

def SurrogateDiagonalTailChunk001Sub001Block088Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28381
    = surrogateDiagTailX0RatChunk001Sub001Block088Part023

theorem surrogateDiagonalTailChunk001Sub001Block088Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block088Part023CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block088Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block088Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block088Part023CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block088Part023SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block088Part023] using hcert

def TailChunk001Sub001Block088Part024SupportExplicit : Finset ℕ :=
  ([28382] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block088Part024 : ℚ :=
  (16360562475 : ℚ) / 7028443933568425984

def SurrogateDiagonalTailChunk001Sub001Block088Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28382
    = surrogateDiagTailX0RatChunk001Sub001Block088Part024

theorem surrogateDiagonalTailChunk001Sub001Block088Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block088Part024CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block088Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block088Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block088Part024CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block088Part024SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block088Part024] using hcert

def surrogateDiagonalTailChunk001Sub001Block088HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub001Block088Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block088Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block088Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block088Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block088Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block088Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block088Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block088Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block088Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block088Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub001Block088Head : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block088Part000
    + surrogateDiagTailX0RatChunk001Sub001Block088Part001
    + surrogateDiagTailX0RatChunk001Sub001Block088Part002
    + surrogateDiagTailX0RatChunk001Sub001Block088Part003
    + surrogateDiagTailX0RatChunk001Sub001Block088Part004
    + surrogateDiagTailX0RatChunk001Sub001Block088Part005
    + surrogateDiagTailX0RatChunk001Sub001Block088Part006
    + surrogateDiagTailX0RatChunk001Sub001Block088Part007
    + surrogateDiagTailX0RatChunk001Sub001Block088Part008
    + surrogateDiagTailX0RatChunk001Sub001Block088Part009

def surrogateDiagonalTailChunk001Sub001Block088MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub001Block088Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block088Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block088Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block088Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block088Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block088Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block088Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block088Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block088Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block088Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub001Block088Mid : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block088Part010
    + surrogateDiagTailX0RatChunk001Sub001Block088Part011
    + surrogateDiagTailX0RatChunk001Sub001Block088Part012
    + surrogateDiagTailX0RatChunk001Sub001Block088Part013
    + surrogateDiagTailX0RatChunk001Sub001Block088Part014
    + surrogateDiagTailX0RatChunk001Sub001Block088Part015
    + surrogateDiagTailX0RatChunk001Sub001Block088Part016
    + surrogateDiagTailX0RatChunk001Sub001Block088Part017
    + surrogateDiagTailX0RatChunk001Sub001Block088Part018
    + surrogateDiagTailX0RatChunk001Sub001Block088Part019

def surrogateDiagonalTailChunk001Sub001Block088TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub001Block088Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block088Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block088Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block088Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block088Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub001Block088Tail : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block088Part020
    + surrogateDiagTailX0RatChunk001Sub001Block088Part021
    + surrogateDiagTailX0RatChunk001Sub001Block088Part022
    + surrogateDiagTailX0RatChunk001Sub001Block088Part023
    + surrogateDiagTailX0RatChunk001Sub001Block088Part024

def surrogateDiagonalTailChunk001Sub001Block088Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk001Sub001Block088HeadSum X0
    + surrogateDiagonalTailChunk001Sub001Block088MidSum X0
    + surrogateDiagonalTailChunk001Sub001Block088TailSum X0

def surrogateDiagTailX0RatChunk001Sub001Block088 : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block088Part000
    + surrogateDiagTailX0RatChunk001Sub001Block088Part001
    + surrogateDiagTailX0RatChunk001Sub001Block088Part002
    + surrogateDiagTailX0RatChunk001Sub001Block088Part003
    + surrogateDiagTailX0RatChunk001Sub001Block088Part004
    + surrogateDiagTailX0RatChunk001Sub001Block088Part005
    + surrogateDiagTailX0RatChunk001Sub001Block088Part006
    + surrogateDiagTailX0RatChunk001Sub001Block088Part007
    + surrogateDiagTailX0RatChunk001Sub001Block088Part008
    + surrogateDiagTailX0RatChunk001Sub001Block088Part009
    + surrogateDiagTailX0RatChunk001Sub001Block088Part010
    + surrogateDiagTailX0RatChunk001Sub001Block088Part011
    + surrogateDiagTailX0RatChunk001Sub001Block088Part012
    + surrogateDiagTailX0RatChunk001Sub001Block088Part013
    + surrogateDiagTailX0RatChunk001Sub001Block088Part014
    + surrogateDiagTailX0RatChunk001Sub001Block088Part015
    + surrogateDiagTailX0RatChunk001Sub001Block088Part016
    + surrogateDiagTailX0RatChunk001Sub001Block088Part017
    + surrogateDiagTailX0RatChunk001Sub001Block088Part018
    + surrogateDiagTailX0RatChunk001Sub001Block088Part019
    + surrogateDiagTailX0RatChunk001Sub001Block088Part020
    + surrogateDiagTailX0RatChunk001Sub001Block088Part021
    + surrogateDiagTailX0RatChunk001Sub001Block088Part022
    + surrogateDiagTailX0RatChunk001Sub001Block088Part023
    + surrogateDiagTailX0RatChunk001Sub001Block088Part024

theorem surrogateDiagTailX0RatChunk001Sub001Block088_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk001Sub001Block088Head + surrogateDiagTailX0RatChunk001Sub001Block088Mid + surrogateDiagTailX0RatChunk001Sub001Block088Tail =
      surrogateDiagTailX0RatChunk001Sub001Block088 := by
  unfold surrogateDiagTailX0RatChunk001Sub001Block088Head surrogateDiagTailX0RatChunk001Sub001Block088Mid surrogateDiagTailX0RatChunk001Sub001Block088Tail surrogateDiagTailX0RatChunk001Sub001Block088
  ring

def SurrogateDiagonalTailChunk001Sub001Block088HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub001Block088HeadSum X0 = surrogateDiagTailX0RatChunk001Sub001Block088Head

def SurrogateDiagonalTailChunk001Sub001Block088MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub001Block088MidSum X0 = surrogateDiagTailX0RatChunk001Sub001Block088Mid

def SurrogateDiagonalTailChunk001Sub001Block088TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub001Block088TailSum X0 = surrogateDiagTailX0RatChunk001Sub001Block088Tail

theorem surrogateDiagonalTailChunk001Sub001Block088_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk001Sub001Block088HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk001Sub001Block088MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk001Sub001Block088TailCertificateAt X0) :
    surrogateDiagonalTailChunk001Sub001Block088Sum X0 = surrogateDiagTailX0RatChunk001Sub001Block088 := by
  unfold SurrogateDiagonalTailChunk001Sub001Block088HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk001Sub001Block088MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk001Sub001Block088TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk001Sub001Block088Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk001Sub001Block088_eq_head_add_mid_add_tail

/-- Block 089 covers tail-support indices [17225,17250) and q from 28383 to 28419. -/

def TailChunk001Sub001Block089Part000SupportExplicit : Finset ℕ :=
  ([28383] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block089Part000 : ℚ :=
  (5593849951 : ℚ) / 320413928794164480

def SurrogateDiagonalTailChunk001Sub001Block089Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28383
    = surrogateDiagTailX0RatChunk001Sub001Block089Part000

theorem surrogateDiagonalTailChunk001Sub001Block089Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block089Part000CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block089Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block089Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block089Part000CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block089Part000SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block089Part000] using hcert

def TailChunk001Sub001Block089Part001SupportExplicit : Finset ℕ :=
  ([28385] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block089Part001 : ℚ :=
  (4344002831 : ℚ) / 1785590660034662400

def SurrogateDiagonalTailChunk001Sub001Block089Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28385
    = surrogateDiagTailX0RatChunk001Sub001Block089Part001

theorem surrogateDiagonalTailChunk001Sub001Block089Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block089Part001CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block089Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block089Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block089Part001CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block089Part001SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block089Part001] using hcert

def TailChunk001Sub001Block089Part002SupportExplicit : Finset ℕ :=
  ([28387] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block089Part002 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block089Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28387
    = surrogateDiagTailX0RatChunk001Sub001Block089Part002

theorem surrogateDiagonalTailChunk001Sub001Block089Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block089Part002CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block089Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block089Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block089Part002CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block089Part002SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block089Part002] using hcert

def TailChunk001Sub001Block089Part003SupportExplicit : Finset ℕ :=
  ([28389] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block089Part003 : ℚ :=
  (2798107600475 : ℚ) / 160342488944354516544

def SurrogateDiagonalTailChunk001Sub001Block089Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28389
    = surrogateDiagTailX0RatChunk001Sub001Block089Part003

theorem surrogateDiagonalTailChunk001Sub001Block089Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block089Part003CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block089Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block089Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block089Part003CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block089Part003SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block089Part003] using hcert

def TailChunk001Sub001Block089Part004SupportExplicit : Finset ℕ :=
  ([28390] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block089Part004 : ℚ :=
  (664158335875 : ℚ) / 31855109844592754688

def SurrogateDiagonalTailChunk001Sub001Block089Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28390
    = surrogateDiagTailX0RatChunk001Sub001Block089Part004

theorem surrogateDiagonalTailChunk001Sub001Block089Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block089Part004CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block089Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block089Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block089Part004CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block089Part004SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block089Part004] using hcert

def TailChunk001Sub001Block089Part005SupportExplicit : Finset ℕ :=
  ([28391] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block089Part005 : ℚ :=
  (22278798863 : ℚ) / 18434003623319961600

def SurrogateDiagonalTailChunk001Sub001Block089Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28391
    = surrogateDiagTailX0RatChunk001Sub001Block089Part005

theorem surrogateDiagonalTailChunk001Sub001Block089Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block089Part005CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block089Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block089Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block089Part005CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block089Part005SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block089Part005] using hcert

def TailChunk001Sub001Block089Part006SupportExplicit : Finset ℕ :=
  ([28393] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block089Part006 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block089Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28393
    = surrogateDiagTailX0RatChunk001Sub001Block089Part006

theorem surrogateDiagonalTailChunk001Sub001Block089Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block089Part006CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block089Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block089Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block089Part006CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block089Part006SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block089Part006] using hcert

def TailChunk001Sub001Block089Part007SupportExplicit : Finset ℕ :=
  ([28394] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block089Part007 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block089Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28394
    = surrogateDiagTailX0RatChunk001Sub001Block089Part007

theorem surrogateDiagonalTailChunk001Sub001Block089Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block089Part007CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block089Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block089Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block089Part007CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block089Part007SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block089Part007] using hcert

def TailChunk001Sub001Block089Part008SupportExplicit : Finset ℕ :=
  ([28397] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block089Part008 : ℚ :=
  (36092606575 : ℚ) / 380735835841185841152

def SurrogateDiagonalTailChunk001Sub001Block089Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28397
    = surrogateDiagTailX0RatChunk001Sub001Block089Part008

theorem surrogateDiagonalTailChunk001Sub001Block089Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block089Part008CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block089Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block089Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block089Part008CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block089Part008SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block089Part008] using hcert

def TailChunk001Sub001Block089Part009SupportExplicit : Finset ℕ :=
  ([28398] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block089Part009 : ℚ :=
  (12501018475 : ℚ) / 179105021715494784

def SurrogateDiagonalTailChunk001Sub001Block089Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28398
    = surrogateDiagTailX0RatChunk001Sub001Block089Part009

theorem surrogateDiagonalTailChunk001Sub001Block089Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block089Part009CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block089Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block089Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block089Part009CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block089Part009SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block089Part009] using hcert

def TailChunk001Sub001Block089Part010SupportExplicit : Finset ℕ :=
  ([28399] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block089Part010 : ℚ :=
  (79236227125 : ℚ) / 67465274759742652416

def SurrogateDiagonalTailChunk001Sub001Block089Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28399
    = surrogateDiagTailX0RatChunk001Sub001Block089Part010

theorem surrogateDiagonalTailChunk001Sub001Block089Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block089Part010CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block089Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block089Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block089Part010CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block089Part010SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block089Part010] using hcert

def TailChunk001Sub001Block089Part011SupportExplicit : Finset ℕ :=
  ([28401] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block089Part011 : ℚ :=
  (2800473600425 : ℚ) / 160613795971613857344

def SurrogateDiagonalTailChunk001Sub001Block089Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28401
    = surrogateDiagTailX0RatChunk001Sub001Block089Part011

theorem surrogateDiagonalTailChunk001Sub001Block089Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block089Part011CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block089Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block089Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block089Part011CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block089Part011SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block089Part011] using hcert

def TailChunk001Sub001Block089Part012SupportExplicit : Finset ℕ :=
  ([28402] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block089Part012 : ℚ :=
  (16756104109 : ℚ) / 2769782655762000000

def SurrogateDiagonalTailChunk001Sub001Block089Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28402
    = surrogateDiagTailX0RatChunk001Sub001Block089Part012

theorem surrogateDiagonalTailChunk001Sub001Block089Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block089Part012CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block089Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block089Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block089Part012CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block089Part012SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block089Part012] using hcert

def TailChunk001Sub001Block089Part013SupportExplicit : Finset ℕ :=
  ([28403] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block089Part013 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block089Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28403
    = surrogateDiagTailX0RatChunk001Sub001Block089Part013

theorem surrogateDiagonalTailChunk001Sub001Block089Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block089Part013CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block089Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block089Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block089Part013CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block089Part013SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block089Part013] using hcert

def TailChunk001Sub001Block089Part014SupportExplicit : Finset ℕ :=
  ([28405] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block089Part014 : ℚ :=
  (551520712925 : ℚ) / 163208418485310849024

def SurrogateDiagonalTailChunk001Sub001Block089Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28405
    = surrogateDiagTailX0RatChunk001Sub001Block089Part014

theorem surrogateDiagonalTailChunk001Sub001Block089Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block089Part014CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block089Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block089Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block089Part014CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block089Part014SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block089Part014] using hcert

def TailChunk001Sub001Block089Part015SupportExplicit : Finset ℕ :=
  ([28406] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block089Part015 : ℚ :=
  (257934984575 : ℚ) / 27407767871145452544

def SurrogateDiagonalTailChunk001Sub001Block089Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28406
    = surrogateDiagTailX0RatChunk001Sub001Block089Part015

theorem surrogateDiagonalTailChunk001Sub001Block089Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block089Part015CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block089Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block089Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block089Part015CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block089Part015SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block089Part015] using hcert

def TailChunk001Sub001Block089Part016SupportExplicit : Finset ℕ :=
  ([28407] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block089Part016 : ℚ :=
  (2642274230225 : ℚ) / 125284095766428647424

def SurrogateDiagonalTailChunk001Sub001Block089Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28407
    = surrogateDiagTailX0RatChunk001Sub001Block089Part016

theorem surrogateDiagonalTailChunk001Sub001Block089Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block089Part016CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block089Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block089Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block089Part016CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block089Part016SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block089Part016] using hcert

def TailChunk001Sub001Block089Part017SupportExplicit : Finset ℕ :=
  ([28409] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block089Part017 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block089Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28409
    = surrogateDiagTailX0RatChunk001Sub001Block089Part017

theorem surrogateDiagonalTailChunk001Sub001Block089Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block089Part017CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block089Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block089Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block089Part017CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block089Part017SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block089Part017] using hcert

def TailChunk001Sub001Block089Part018SupportExplicit : Finset ℕ :=
  ([28410] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block089Part018 : ℚ :=
  (504230883675 : ℚ) / 2734198859043536896

def SurrogateDiagonalTailChunk001Sub001Block089Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28410
    = surrogateDiagTailX0RatChunk001Sub001Block089Part018

theorem surrogateDiagonalTailChunk001Sub001Block089Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block089Part018CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block089Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block089Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block089Part018CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block089Part018SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block089Part018] using hcert

def TailChunk001Sub001Block089Part019SupportExplicit : Finset ℕ :=
  ([28411] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block089Part019 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block089Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28411
    = surrogateDiagTailX0RatChunk001Sub001Block089Part019

theorem surrogateDiagonalTailChunk001Sub001Block089Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block089Part019CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block089Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block089Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block089Part019CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block089Part019SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block089Part019] using hcert

def TailChunk001Sub001Block089Part020SupportExplicit : Finset ℕ :=
  ([28414] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block089Part020 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block089Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28414
    = surrogateDiagTailX0RatChunk001Sub001Block089Part020

theorem surrogateDiagonalTailChunk001Sub001Block089Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block089Part020CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block089Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block089Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block089Part020CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block089Part020SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block089Part020] using hcert

def TailChunk001Sub001Block089Part021SupportExplicit : Finset ℕ :=
  ([28415] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block089Part021 : ℚ :=
  (2019070727125 : ℚ) / 667224126426697648128

def SurrogateDiagonalTailChunk001Sub001Block089Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28415
    = surrogateDiagTailX0RatChunk001Sub001Block089Part021

theorem surrogateDiagonalTailChunk001Sub001Block089Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block089Part021CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block089Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block089Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block089Part021CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block089Part021SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block089Part021] using hcert

def TailChunk001Sub001Block089Part022SupportExplicit : Finset ℕ :=
  ([28417] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block089Part022 : ℚ :=
  (234173267 : ℚ) / 3454639695253094400

def SurrogateDiagonalTailChunk001Sub001Block089Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28417
    = surrogateDiagTailX0RatChunk001Sub001Block089Part022

theorem surrogateDiagonalTailChunk001Sub001Block089Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block089Part022CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block089Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block089Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block089Part022CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block089Part022SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block089Part022] using hcert

def TailChunk001Sub001Block089Part023SupportExplicit : Finset ℕ :=
  ([28418] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block089Part023 : ℚ :=
  (41788843625 : ℚ) / 8192187563755732992

def SurrogateDiagonalTailChunk001Sub001Block089Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28418
    = surrogateDiagTailX0RatChunk001Sub001Block089Part023

theorem surrogateDiagonalTailChunk001Sub001Block089Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block089Part023CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block089Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block089Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block089Part023CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block089Part023SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block089Part023] using hcert

def TailChunk001Sub001Block089Part024SupportExplicit : Finset ℕ :=
  ([28419] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block089Part024 : ℚ :=
  (1402012237675 : ℚ) / 80510700944791437312

def SurrogateDiagonalTailChunk001Sub001Block089Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28419
    = surrogateDiagTailX0RatChunk001Sub001Block089Part024

theorem surrogateDiagonalTailChunk001Sub001Block089Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block089Part024CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block089Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block089Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block089Part024CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block089Part024SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block089Part024] using hcert

def surrogateDiagonalTailChunk001Sub001Block089HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub001Block089Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block089Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block089Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block089Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block089Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block089Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block089Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block089Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block089Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block089Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub001Block089Head : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block089Part000
    + surrogateDiagTailX0RatChunk001Sub001Block089Part001
    + surrogateDiagTailX0RatChunk001Sub001Block089Part002
    + surrogateDiagTailX0RatChunk001Sub001Block089Part003
    + surrogateDiagTailX0RatChunk001Sub001Block089Part004
    + surrogateDiagTailX0RatChunk001Sub001Block089Part005
    + surrogateDiagTailX0RatChunk001Sub001Block089Part006
    + surrogateDiagTailX0RatChunk001Sub001Block089Part007
    + surrogateDiagTailX0RatChunk001Sub001Block089Part008
    + surrogateDiagTailX0RatChunk001Sub001Block089Part009

def surrogateDiagonalTailChunk001Sub001Block089MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub001Block089Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block089Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block089Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block089Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block089Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block089Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block089Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block089Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block089Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block089Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub001Block089Mid : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block089Part010
    + surrogateDiagTailX0RatChunk001Sub001Block089Part011
    + surrogateDiagTailX0RatChunk001Sub001Block089Part012
    + surrogateDiagTailX0RatChunk001Sub001Block089Part013
    + surrogateDiagTailX0RatChunk001Sub001Block089Part014
    + surrogateDiagTailX0RatChunk001Sub001Block089Part015
    + surrogateDiagTailX0RatChunk001Sub001Block089Part016
    + surrogateDiagTailX0RatChunk001Sub001Block089Part017
    + surrogateDiagTailX0RatChunk001Sub001Block089Part018
    + surrogateDiagTailX0RatChunk001Sub001Block089Part019

def surrogateDiagonalTailChunk001Sub001Block089TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub001Block089Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block089Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block089Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block089Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block089Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub001Block089Tail : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block089Part020
    + surrogateDiagTailX0RatChunk001Sub001Block089Part021
    + surrogateDiagTailX0RatChunk001Sub001Block089Part022
    + surrogateDiagTailX0RatChunk001Sub001Block089Part023
    + surrogateDiagTailX0RatChunk001Sub001Block089Part024

def surrogateDiagonalTailChunk001Sub001Block089Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk001Sub001Block089HeadSum X0
    + surrogateDiagonalTailChunk001Sub001Block089MidSum X0
    + surrogateDiagonalTailChunk001Sub001Block089TailSum X0

def surrogateDiagTailX0RatChunk001Sub001Block089 : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block089Part000
    + surrogateDiagTailX0RatChunk001Sub001Block089Part001
    + surrogateDiagTailX0RatChunk001Sub001Block089Part002
    + surrogateDiagTailX0RatChunk001Sub001Block089Part003
    + surrogateDiagTailX0RatChunk001Sub001Block089Part004
    + surrogateDiagTailX0RatChunk001Sub001Block089Part005
    + surrogateDiagTailX0RatChunk001Sub001Block089Part006
    + surrogateDiagTailX0RatChunk001Sub001Block089Part007
    + surrogateDiagTailX0RatChunk001Sub001Block089Part008
    + surrogateDiagTailX0RatChunk001Sub001Block089Part009
    + surrogateDiagTailX0RatChunk001Sub001Block089Part010
    + surrogateDiagTailX0RatChunk001Sub001Block089Part011
    + surrogateDiagTailX0RatChunk001Sub001Block089Part012
    + surrogateDiagTailX0RatChunk001Sub001Block089Part013
    + surrogateDiagTailX0RatChunk001Sub001Block089Part014
    + surrogateDiagTailX0RatChunk001Sub001Block089Part015
    + surrogateDiagTailX0RatChunk001Sub001Block089Part016
    + surrogateDiagTailX0RatChunk001Sub001Block089Part017
    + surrogateDiagTailX0RatChunk001Sub001Block089Part018
    + surrogateDiagTailX0RatChunk001Sub001Block089Part019
    + surrogateDiagTailX0RatChunk001Sub001Block089Part020
    + surrogateDiagTailX0RatChunk001Sub001Block089Part021
    + surrogateDiagTailX0RatChunk001Sub001Block089Part022
    + surrogateDiagTailX0RatChunk001Sub001Block089Part023
    + surrogateDiagTailX0RatChunk001Sub001Block089Part024

theorem surrogateDiagTailX0RatChunk001Sub001Block089_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk001Sub001Block089Head + surrogateDiagTailX0RatChunk001Sub001Block089Mid + surrogateDiagTailX0RatChunk001Sub001Block089Tail =
      surrogateDiagTailX0RatChunk001Sub001Block089 := by
  unfold surrogateDiagTailX0RatChunk001Sub001Block089Head surrogateDiagTailX0RatChunk001Sub001Block089Mid surrogateDiagTailX0RatChunk001Sub001Block089Tail surrogateDiagTailX0RatChunk001Sub001Block089
  ring

def SurrogateDiagonalTailChunk001Sub001Block089HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub001Block089HeadSum X0 = surrogateDiagTailX0RatChunk001Sub001Block089Head

def SurrogateDiagonalTailChunk001Sub001Block089MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub001Block089MidSum X0 = surrogateDiagTailX0RatChunk001Sub001Block089Mid

def SurrogateDiagonalTailChunk001Sub001Block089TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub001Block089TailSum X0 = surrogateDiagTailX0RatChunk001Sub001Block089Tail

theorem surrogateDiagonalTailChunk001Sub001Block089_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk001Sub001Block089HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk001Sub001Block089MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk001Sub001Block089TailCertificateAt X0) :
    surrogateDiagonalTailChunk001Sub001Block089Sum X0 = surrogateDiagTailX0RatChunk001Sub001Block089 := by
  unfold SurrogateDiagonalTailChunk001Sub001Block089HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk001Sub001Block089MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk001Sub001Block089TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk001Sub001Block089Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk001Sub001Block089_eq_head_add_mid_add_tail

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

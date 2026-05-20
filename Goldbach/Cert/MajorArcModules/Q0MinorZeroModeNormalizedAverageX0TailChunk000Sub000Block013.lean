import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0TailPilot25

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

open scoped BigOperators

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

/- Generated direct-term certificate blocks for tail chunk 000, subchunk 000, blocks [13,14). -/

/- Block 013 covers tail-support indices [325,350) and q from 586 to 623. -/

def TailChunk000Sub000Block013Part000SupportExplicit : Finset ℕ :=
  ([586] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block013Part000 : ℚ :=
  (22730668975 : ℚ) / 4544627303712

def SurrogateDiagonalTailChunk000Sub000Block013Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 586
    = surrogateDiagTailX0RatChunk000Sub000Block013Part000

theorem surrogateDiagonalTailChunk000Sub000Block013Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block013Part000CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block013Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block013Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block013Part000CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block013Part000SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block013Part000] using hcert

def TailChunk000Sub000Block013Part001SupportExplicit : Finset ℕ :=
  ([587] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block013Part001 : ℚ :=
  (8062914600 : ℚ) / 12285874685267

def SurrogateDiagonalTailChunk000Sub000Block013Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 587
    = surrogateDiagTailX0RatChunk000Sub000Block013Part001

theorem surrogateDiagonalTailChunk000Sub000Block013Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block013Part001CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block013Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block013Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block013Part001CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block013Part001SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block013Part001] using hcert

def TailChunk000Sub000Block013Part002SupportExplicit : Finset ℕ :=
  ([589] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block013Part002 : ℚ :=
  (7121579743 : ℚ) / 8504756611200

def SurrogateDiagonalTailChunk000Sub000Block013Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 589
    = surrogateDiagTailX0RatChunk000Sub000Block013Part002

theorem surrogateDiagonalTailChunk000Sub000Block013Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block013Part002CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block013Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block013Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block013Part002CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block013Part002SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block013Part002] using hcert

def TailChunk000Sub000Block013Part003SupportExplicit : Finset ℕ :=
  ([590] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block013Part003 : ℚ :=
  (36364646375 : ℚ) / 3622002975744

def SurrogateDiagonalTailChunk000Sub000Block013Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 590
    = surrogateDiagTailX0RatChunk000Sub000Block013Part003

theorem surrogateDiagonalTailChunk000Sub000Block013Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block013Part003CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block013Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block013Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block013Part003CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block013Part003SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block013Part003] using hcert

def TailChunk000Sub000Block013Part004SupportExplicit : Finset ℕ :=
  ([591] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block013Part004 : ℚ :=
  (7393389475 : ℚ) / 3690210534528

def SurrogateDiagonalTailChunk000Sub000Block013Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 591
    = surrogateDiagTailX0RatChunk000Sub000Block013Part004

theorem surrogateDiagonalTailChunk000Sub000Block013Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block013Part004CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block013Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block013Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block013Part004CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block013Part004SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block013Part004] using hcert

def TailChunk000Sub000Block013Part005SupportExplicit : Finset ℕ :=
  ([593] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block013Part005 : ℚ :=
  (43894586425 : ℚ) / 76780987686912

def SurrogateDiagonalTailChunk000Sub000Block013Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 593
    = surrogateDiagTailX0RatChunk000Sub000Block013Part005

theorem surrogateDiagonalTailChunk000Sub000Block013Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block013Part005CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block013Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block013Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block013Part005CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block013Part005SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block013Part005] using hcert

def TailChunk000Sub000Block013Part006SupportExplicit : Finset ℕ :=
  ([595] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block013Part006 : ℚ :=
  (6482416675 : ℚ) / 3020502859776

def SurrogateDiagonalTailChunk000Sub000Block013Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 595
    = surrogateDiagTailX0RatChunk000Sub000Block013Part006

theorem surrogateDiagonalTailChunk000Sub000Block013Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block013Part006CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block013Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block013Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block013Part006CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block013Part006SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block013Part006] using hcert

def TailChunk000Sub000Block013Part007SupportExplicit : Finset ℕ :=
  ([597] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block013Part007 : ℚ :=
  (60353977175 : ℚ) / 30745220134464

def SurrogateDiagonalTailChunk000Sub000Block013Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 597
    = surrogateDiagTailX0RatChunk000Sub000Block013Part007

theorem surrogateDiagonalTailChunk000Sub000Block013Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block013Part007CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block013Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block013Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block013Part007CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block013Part007SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block013Part007] using hcert

def TailChunk000Sub000Block013Part008SupportExplicit : Finset ℕ :=
  ([598] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block013Part008 : ℚ :=
  (7217136875 : ℚ) / 1104205436928

def SurrogateDiagonalTailChunk000Sub000Block013Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 598
    = surrogateDiagTailX0RatChunk000Sub000Block013Part008

theorem surrogateDiagonalTailChunk000Sub000Block013Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block013Part008CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block013Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block013Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block013Part008CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block013Part008SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block013Part008] using hcert

def TailChunk000Sub000Block013Part009SupportExplicit : Finset ℕ :=
  ([599] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block013Part009 : ℚ :=
  (645841800 : ℚ) / 1024889398559

def SurrogateDiagonalTailChunk000Sub000Block013Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 599
    = surrogateDiagTailX0RatChunk000Sub000Block013Part009

theorem surrogateDiagonalTailChunk000Sub000Block013Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block013Part009CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block013Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block013Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block013Part009CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block013Part009SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block013Part009] using hcert

def TailChunk000Sub000Block013Part010SupportExplicit : Finset ℕ :=
  ([601] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block013Part010 : ℚ :=
  (4695613 : ℚ) / 7501500000

def SurrogateDiagonalTailChunk000Sub000Block013Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 601
    = surrogateDiagTailX0RatChunk000Sub000Block013Part010

theorem surrogateDiagonalTailChunk000Sub000Block013Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block013Part010CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block013Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block013Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block013Part010CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block013Part010SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block013Part010] using hcert

def TailChunk000Sub000Block013Part011SupportExplicit : Finset ℕ :=
  ([602] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block013Part011 : ℚ :=
  (76486107475 : ℚ) / 10083911419008

def SurrogateDiagonalTailChunk000Sub000Block013Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 602
    = surrogateDiagTailX0RatChunk000Sub000Block013Part011

theorem surrogateDiagonalTailChunk000Sub000Block013Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block013Part011CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block013Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block013Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block013Part011CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block013Part011SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block013Part011] using hcert

def TailChunk000Sub000Block013Part012SupportExplicit : Finset ℕ :=
  ([606] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block013Part012 : ℚ :=
  (49504691 : ℚ) / 3200640000

def SurrogateDiagonalTailChunk000Sub000Block013Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 606
    = surrogateDiagTailX0RatChunk000Sub000Block013Part012

theorem surrogateDiagonalTailChunk000Sub000Block013Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block013Part012CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block013Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block013Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block013Part012CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block013Part012SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block013Part012] using hcert

def TailChunk000Sub000Block013Part013SupportExplicit : Finset ℕ :=
  ([607] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block013Part013 : ℚ :=
  (45991646425 : ℚ) / 84305782594962

def SurrogateDiagonalTailChunk000Sub000Block013Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 607
    = surrogateDiagTailX0RatChunk000Sub000Block013Part013

theorem surrogateDiagonalTailChunk000Sub000Block013Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block013Part013CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block013Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block013Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block013Part013CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block013Part013SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block013Part013] using hcert

def TailChunk000Sub000Block013Part014SupportExplicit : Finset ℕ :=
  ([609] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block013Part014 : ℚ :=
  (102769976875 : ℚ) / 31870139793408

def SurrogateDiagonalTailChunk000Sub000Block013Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 609
    = surrogateDiagTailX0RatChunk000Sub000Block013Part014

theorem surrogateDiagonalTailChunk000Sub000Block013Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block013Part014CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block013Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block013Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block013Part014CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block013Part014SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block013Part014] using hcert

def TailChunk000Sub000Block013Part015SupportExplicit : Finset ℕ :=
  ([610] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block013Part015 : ℚ :=
  (982605503 : ℚ) / 110614118400

def SurrogateDiagonalTailChunk000Sub000Block013Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 610
    = surrogateDiagTailX0RatChunk000Sub000Block013Part015

theorem surrogateDiagonalTailChunk000Sub000Block013Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block013Part015CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block013Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block013Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block013Part015CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block013Part015SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block013Part015] using hcert

def TailChunk000Sub000Block013Part016SupportExplicit : Finset ℕ :=
  ([611] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block013Part016 : ℚ :=
  (169021552525 : ℚ) / 232157741303808

def SurrogateDiagonalTailChunk000Sub000Block013Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 611
    = surrogateDiagTailX0RatChunk000Sub000Block013Part016

theorem surrogateDiagonalTailChunk000Sub000Block013Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block013Part016CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block013Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block013Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block013Part016CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block013Part016SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block013Part016] using hcert

def TailChunk000Sub000Block013Part017SupportExplicit : Finset ℕ :=
  ([613] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block013Part017 : ℚ :=
  (46905365425 : ℚ) / 87694540360992

def SurrogateDiagonalTailChunk000Sub000Block013Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 613
    = surrogateDiagTailX0RatChunk000Sub000Block013Part017

theorem surrogateDiagonalTailChunk000Sub000Block013Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block013Part017CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block013Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block013Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block013Part017CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block013Part017SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block013Part017] using hcert

def TailChunk000Sub000Block013Part018SupportExplicit : Finset ℕ :=
  ([614] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block013Part018 : ℚ :=
  (11745781625 : ℚ) / 2740454386281

def SurrogateDiagonalTailChunk000Sub000Block013Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 614
    = surrogateDiagTailX0RatChunk000Sub000Block013Part018

theorem surrogateDiagonalTailChunk000Sub000Block013Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block013Part018CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block013Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block013Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block013Part018CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block013Part018SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block013Part018] using hcert

def TailChunk000Sub000Block013Part019SupportExplicit : Finset ℕ :=
  ([615] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block013Part019 : ℚ :=
  (493298111 : ℚ) / 131098214400

def SurrogateDiagonalTailChunk000Sub000Block013Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 615
    = surrogateDiagTailX0RatChunk000Sub000Block013Part019

theorem surrogateDiagonalTailChunk000Sub000Block013Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block013Part019CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block013Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block013Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block013Part019CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block013Part019SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block013Part019] using hcert

def TailChunk000Sub000Block013Part020SupportExplicit : Finset ℕ :=
  ([617] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block013Part020 : ℚ :=
  (47519504425 : ℚ) / 90009783316992

def SurrogateDiagonalTailChunk000Sub000Block013Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 617
    = surrogateDiagTailX0RatChunk000Sub000Block013Part020

theorem surrogateDiagonalTailChunk000Sub000Block013Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block013Part020CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block013Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block013Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block013Part020CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block013Part020SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block013Part020] using hcert

def TailChunk000Sub000Block013Part021SupportExplicit : Finset ℕ :=
  ([618] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block013Part021 : ℚ :=
  (4202875 : ℚ) / 288648576

def SurrogateDiagonalTailChunk000Sub000Block013Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 618
    = surrogateDiagTailX0RatChunk000Sub000Block013Part021

theorem surrogateDiagonalTailChunk000Sub000Block013Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block013Part021CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block013Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block013Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block013Part021CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block013Part021SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block013Part021] using hcert

def TailChunk000Sub000Block013Part022SupportExplicit : Finset ℕ :=
  ([619] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block013Part022 : ℚ :=
  (47828071825 : ℚ) / 91184446852722

def SurrogateDiagonalTailChunk000Sub000Block013Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 619
    = surrogateDiagTailX0RatChunk000Sub000Block013Part022

theorem surrogateDiagonalTailChunk000Sub000Block013Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block013Part022CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block013Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block013Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block013Part022CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block013Part022SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block013Part022] using hcert

def TailChunk000Sub000Block013Part023SupportExplicit : Finset ℕ :=
  ([622] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block013Part023 : ℚ :=
  (96430837 : ℚ) / 23092642605

def SurrogateDiagonalTailChunk000Sub000Block013Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 622
    = surrogateDiagTailX0RatChunk000Sub000Block013Part023

theorem surrogateDiagonalTailChunk000Sub000Block013Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block013Part023CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block013Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block013Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block013Part023CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block013Part023SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block013Part023] using hcert

def TailChunk000Sub000Block013Part024SupportExplicit : Finset ℕ :=
  ([623] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block013Part024 : ℚ :=
  (164994274825 : ℚ) / 194340156899328

def SurrogateDiagonalTailChunk000Sub000Block013Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 623
    = surrogateDiagTailX0RatChunk000Sub000Block013Part024

theorem surrogateDiagonalTailChunk000Sub000Block013Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block013Part024CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block013Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block013Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block013Part024CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block013Part024SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block013Part024] using hcert

def surrogateDiagonalTailChunk000Sub000Block013HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block013Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block013Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block013Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block013Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block013Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block013Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block013Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block013Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block013Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block013Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block013Head : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block013Part000
    + surrogateDiagTailX0RatChunk000Sub000Block013Part001
    + surrogateDiagTailX0RatChunk000Sub000Block013Part002
    + surrogateDiagTailX0RatChunk000Sub000Block013Part003
    + surrogateDiagTailX0RatChunk000Sub000Block013Part004
    + surrogateDiagTailX0RatChunk000Sub000Block013Part005
    + surrogateDiagTailX0RatChunk000Sub000Block013Part006
    + surrogateDiagTailX0RatChunk000Sub000Block013Part007
    + surrogateDiagTailX0RatChunk000Sub000Block013Part008
    + surrogateDiagTailX0RatChunk000Sub000Block013Part009

def surrogateDiagonalTailChunk000Sub000Block013MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block013Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block013Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block013Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block013Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block013Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block013Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block013Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block013Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block013Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block013Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block013Mid : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block013Part010
    + surrogateDiagTailX0RatChunk000Sub000Block013Part011
    + surrogateDiagTailX0RatChunk000Sub000Block013Part012
    + surrogateDiagTailX0RatChunk000Sub000Block013Part013
    + surrogateDiagTailX0RatChunk000Sub000Block013Part014
    + surrogateDiagTailX0RatChunk000Sub000Block013Part015
    + surrogateDiagTailX0RatChunk000Sub000Block013Part016
    + surrogateDiagTailX0RatChunk000Sub000Block013Part017
    + surrogateDiagTailX0RatChunk000Sub000Block013Part018
    + surrogateDiagTailX0RatChunk000Sub000Block013Part019

def surrogateDiagonalTailChunk000Sub000Block013TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block013Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block013Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block013Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block013Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block013Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block013Tail : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block013Part020
    + surrogateDiagTailX0RatChunk000Sub000Block013Part021
    + surrogateDiagTailX0RatChunk000Sub000Block013Part022
    + surrogateDiagTailX0RatChunk000Sub000Block013Part023
    + surrogateDiagTailX0RatChunk000Sub000Block013Part024

def surrogateDiagonalTailChunk000Sub000Block013Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub000Block013HeadSum X0
    + surrogateDiagonalTailChunk000Sub000Block013MidSum X0
    + surrogateDiagonalTailChunk000Sub000Block013TailSum X0

def surrogateDiagTailX0RatChunk000Sub000Block013 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block013Part000
    + surrogateDiagTailX0RatChunk000Sub000Block013Part001
    + surrogateDiagTailX0RatChunk000Sub000Block013Part002
    + surrogateDiagTailX0RatChunk000Sub000Block013Part003
    + surrogateDiagTailX0RatChunk000Sub000Block013Part004
    + surrogateDiagTailX0RatChunk000Sub000Block013Part005
    + surrogateDiagTailX0RatChunk000Sub000Block013Part006
    + surrogateDiagTailX0RatChunk000Sub000Block013Part007
    + surrogateDiagTailX0RatChunk000Sub000Block013Part008
    + surrogateDiagTailX0RatChunk000Sub000Block013Part009
    + surrogateDiagTailX0RatChunk000Sub000Block013Part010
    + surrogateDiagTailX0RatChunk000Sub000Block013Part011
    + surrogateDiagTailX0RatChunk000Sub000Block013Part012
    + surrogateDiagTailX0RatChunk000Sub000Block013Part013
    + surrogateDiagTailX0RatChunk000Sub000Block013Part014
    + surrogateDiagTailX0RatChunk000Sub000Block013Part015
    + surrogateDiagTailX0RatChunk000Sub000Block013Part016
    + surrogateDiagTailX0RatChunk000Sub000Block013Part017
    + surrogateDiagTailX0RatChunk000Sub000Block013Part018
    + surrogateDiagTailX0RatChunk000Sub000Block013Part019
    + surrogateDiagTailX0RatChunk000Sub000Block013Part020
    + surrogateDiagTailX0RatChunk000Sub000Block013Part021
    + surrogateDiagTailX0RatChunk000Sub000Block013Part022
    + surrogateDiagTailX0RatChunk000Sub000Block013Part023
    + surrogateDiagTailX0RatChunk000Sub000Block013Part024

theorem surrogateDiagTailX0RatChunk000Sub000Block013_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk000Sub000Block013Head + surrogateDiagTailX0RatChunk000Sub000Block013Mid + surrogateDiagTailX0RatChunk000Sub000Block013Tail =
      surrogateDiagTailX0RatChunk000Sub000Block013 := by
  unfold surrogateDiagTailX0RatChunk000Sub000Block013Head surrogateDiagTailX0RatChunk000Sub000Block013Mid surrogateDiagTailX0RatChunk000Sub000Block013Tail surrogateDiagTailX0RatChunk000Sub000Block013
  ring

def SurrogateDiagonalTailChunk000Sub000Block013HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block013HeadSum X0 = surrogateDiagTailX0RatChunk000Sub000Block013Head

def SurrogateDiagonalTailChunk000Sub000Block013MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block013MidSum X0 = surrogateDiagTailX0RatChunk000Sub000Block013Mid

def SurrogateDiagonalTailChunk000Sub000Block013TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block013TailSum X0 = surrogateDiagTailX0RatChunk000Sub000Block013Tail

theorem surrogateDiagonalTailChunk000Sub000Block013_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk000Sub000Block013HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk000Sub000Block013MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk000Sub000Block013TailCertificateAt X0) :
    surrogateDiagonalTailChunk000Sub000Block013Sum X0 = surrogateDiagTailX0RatChunk000Sub000Block013 := by
  unfold SurrogateDiagonalTailChunk000Sub000Block013HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk000Sub000Block013MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk000Sub000Block013TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk000Sub000Block013Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk000Sub000Block013_eq_head_add_mid_add_tail

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

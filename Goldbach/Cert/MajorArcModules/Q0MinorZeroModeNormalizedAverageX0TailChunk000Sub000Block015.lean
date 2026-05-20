import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0TailPilot25

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

open scoped BigOperators

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

/- Generated direct-term certificate blocks for tail chunk 000, subchunk 000, blocks [15,16). -/

/- Block 015 covers tail-support indices [375,400) and q from 667 to 705. -/

def TailChunk000Sub000Block015Part000SupportExplicit : Finset ℕ :=
  ([667] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block015Part000 : ℚ :=
  (102207136475 : ℚ) / 180019566633984

def SurrogateDiagonalTailChunk000Sub000Block015Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 667
    = surrogateDiagTailX0RatChunk000Sub000Block015Part000

theorem surrogateDiagonalTailChunk000Sub000Block015Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block015Part000CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block015Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block015Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block015Part000CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block015Part000SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block015Part000] using hcert

def TailChunk000Sub000Block015Part001SupportExplicit : Finset ℕ :=
  ([669] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block015Part001 : ℚ :=
  (133099180525 : ℚ) / 97175937541248

def SurrogateDiagonalTailChunk000Sub000Block015Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 669
    = surrogateDiagTailX0RatChunk000Sub000Block015Part001

theorem surrogateDiagonalTailChunk000Sub000Block015Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block015Part001CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block015Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block015Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block015Part001CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block015Part001SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block015Part001] using hcert

def TailChunk000Sub000Block015Part002SupportExplicit : Finset ℕ :=
  ([670] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block015Part002 : ℚ :=
  (41461915625 : ℚ) / 6073129903104

def SurrogateDiagonalTailChunk000Sub000Block015Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 670
    = surrogateDiagTailX0RatChunk000Sub000Block015Part002

theorem surrogateDiagonalTailChunk000Sub000Block015Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block015Part002CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block015Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block015Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block015Part002CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block015Part002SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block015Part002] using hcert

def TailChunk000Sub000Block015Part003SupportExplicit : Finset ℕ :=
  ([671] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block015Part003 : ℚ :=
  (473303293 : ℚ) / 864172800000

def SurrogateDiagonalTailChunk000Sub000Block015Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 671
    = surrogateDiagTailX0RatChunk000Sub000Block015Part003

theorem surrogateDiagonalTailChunk000Sub000Block015Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block015Part003CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block015Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block015Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block015Part003CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block015Part003SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block015Part003] using hcert

def TailChunk000Sub000Block015Part004SupportExplicit : Finset ℕ :=
  ([673] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block015Part004 : ℚ :=
  (56536862425 : ℚ) / 127480559173632

def SurrogateDiagonalTailChunk000Sub000Block015Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 673
    = surrogateDiagTailX0RatChunk000Sub000Block015Part004

theorem surrogateDiagonalTailChunk000Sub000Block015Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block015Part004CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block015Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block015Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block015Part004CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block015Part004SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block015Part004] using hcert

def TailChunk000Sub000Block015Part005SupportExplicit : Finset ℕ :=
  ([674] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block015Part005 : ℚ :=
  (3932326625 : ℚ) / 1180375547904

def SurrogateDiagonalTailChunk000Sub000Block015Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 674
    = surrogateDiagTailX0RatChunk000Sub000Block015Part005

theorem surrogateDiagonalTailChunk000Sub000Block015Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block015Part005CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block015Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block015Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block015Part005CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block015Part005SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block015Part005] using hcert

def TailChunk000Sub000Block015Part006SupportExplicit : Finset ℕ :=
  ([677] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block015Part006 : ℚ :=
  (200278314775 : ℚ) / 522172074972288

def SurrogateDiagonalTailChunk000Sub000Block015Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 677
    = surrogateDiagTailX0RatChunk000Sub000Block015Part006

theorem surrogateDiagonalTailChunk000Sub000Block015Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block015Part006CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block015Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block015Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block015Part006CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block015Part006SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block015Part006] using hcert

def TailChunk000Sub000Block015Part007SupportExplicit : Finset ℕ :=
  ([678] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block015Part007 : ℚ :=
  (508425 : ℚ) / 44957696

def SurrogateDiagonalTailChunk000Sub000Block015Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 678
    = surrogateDiagTailX0RatChunk000Sub000Block015Part007

theorem surrogateDiagonalTailChunk000Sub000Block015Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block015Part007CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block015Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block015Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block015Part007CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block015Part007SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block015Part007] using hcert

def TailChunk000Sub000Block015Part008SupportExplicit : Finset ℕ :=
  ([679] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block015Part008 : ℚ :=
  (19217935975 : ℚ) / 30582591455232

def SurrogateDiagonalTailChunk000Sub000Block015Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 679
    = surrogateDiagTailX0RatChunk000Sub000Block015Part008

theorem surrogateDiagonalTailChunk000Sub000Block015Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block015Part008CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block015Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block015Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block015Part008CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block015Part008SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block015Part008] using hcert

def TailChunk000Sub000Block015Part009SupportExplicit : Finset ℕ :=
  ([681] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block015Part009 : ℚ :=
  (137916121225 : ℚ) / 104371181102208

def SurrogateDiagonalTailChunk000Sub000Block015Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 681
    = surrogateDiagTailX0RatChunk000Sub000Block015Part009

theorem surrogateDiagonalTailChunk000Sub000Block015Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block015Part009CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block015Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block015Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block015Part009CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block015Part009SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block015Part009] using hcert

def TailChunk000Sub000Block015Part010SupportExplicit : Finset ℕ :=
  ([682] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block015Part010 : ℚ :=
  (3602693479 : ℚ) / 810162000000

def SurrogateDiagonalTailChunk000Sub000Block015Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 682
    = surrogateDiagTailX0RatChunk000Sub000Block015Part010

theorem surrogateDiagonalTailChunk000Sub000Block015Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block015Part010CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block015Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block015Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block015Part010CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block015Part010SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block015Part010] using hcert

def TailChunk000Sub000Block015Part011SupportExplicit : Finset ℕ :=
  ([683] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block015Part011 : ℚ :=
  (18531275525 : ℚ) / 49178091691608

def SurrogateDiagonalTailChunk000Sub000Block015Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 683
    = surrogateDiagTailX0RatChunk000Sub000Block015Part011

theorem surrogateDiagonalTailChunk000Sub000Block015Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block015Part011CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block015Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block015Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block015Part011CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block015Part011SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block015Part011] using hcert

def TailChunk000Sub000Block015Part012SupportExplicit : Finset ℕ :=
  ([685] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block015Part012 : ℚ :=
  (182767663525 : ℚ) / 218989079298048

def SurrogateDiagonalTailChunk000Sub000Block015Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 685
    = surrogateDiagTailX0RatChunk000Sub000Block015Part012

theorem surrogateDiagonalTailChunk000Sub000Block015Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block015Part012CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block015Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block015Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block015Part012CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block015Part012SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block015Part012] using hcert

def TailChunk000Sub000Block015Part013SupportExplicit : Finset ℕ :=
  ([687] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block015Part013 : ℚ :=
  (2345369425 : ℚ) / 1689297952032

def SurrogateDiagonalTailChunk000Sub000Block015Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 687
    = surrogateDiagTailX0RatChunk000Sub000Block015Part013

theorem surrogateDiagonalTailChunk000Sub000Block015Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block015Part013CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block015Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block015Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block015Part013CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block015Part013SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block015Part013] using hcert

def TailChunk000Sub000Block015Part014SupportExplicit : Finset ℕ :=
  ([689] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block015Part014 : ℚ :=
  (7872758275 : ℚ) / 15796249178112

def SurrogateDiagonalTailChunk000Sub000Block015Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 689
    = surrogateDiagTailX0RatChunk000Sub000Block015Part014

theorem surrogateDiagonalTailChunk000Sub000Block015Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block015Part014CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block015Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block015Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block015Part014CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block015Part014SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block015Part014] using hcert

def TailChunk000Sub000Block015Part015SupportExplicit : Finset ℕ :=
  ([690] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block015Part015 : ℚ :=
  (54523605025 : ℚ) / 2399261196288

def SurrogateDiagonalTailChunk000Sub000Block015Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 690
    = surrogateDiagTailX0RatChunk000Sub000Block015Part015

theorem surrogateDiagonalTailChunk000Sub000Block015Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block015Part015CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block015Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block015Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block015Part015CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block015Part015SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block015Part015] using hcert

def TailChunk000Sub000Block015Part016SupportExplicit : Finset ℕ :=
  ([691] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block015Part016 : ℚ :=
  (8345890399 : ℚ) / 22671654424200

def SurrogateDiagonalTailChunk000Sub000Block015Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 691
    = surrogateDiagTailX0RatChunk000Sub000Block015Part016

theorem surrogateDiagonalTailChunk000Sub000Block015Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block015Part016CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block015Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block015Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block015Part016CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block015Part016SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block015Part016] using hcert

def TailChunk000Sub000Block015Part017SupportExplicit : Finset ℕ :=
  ([694] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block015Part017 : ℚ :=
  (37522454625 : ℚ) / 11945655866776

def SurrogateDiagonalTailChunk000Sub000Block015Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 694
    = surrogateDiagTailX0RatChunk000Sub000Block015Part017

theorem surrogateDiagonalTailChunk000Sub000Block015Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block015Part017CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block015Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block015Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block015Part017CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block015Part017SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block015Part017] using hcert

def TailChunk000Sub000Block015Part018SupportExplicit : Finset ℕ :=
  ([695] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block015Part018 : ℚ :=
  (169100995375 : ℚ) / 232157741303808

def SurrogateDiagonalTailChunk000Sub000Block015Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 695
    = surrogateDiagTailX0RatChunk000Sub000Block015Part018

theorem surrogateDiagonalTailChunk000Sub000Block015Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block015Part018CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block015Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block015Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block015Part018CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block015Part018SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block015Part018] using hcert

def TailChunk000Sub000Block015Part019SupportExplicit : Finset ℕ :=
  ([697] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block015Part019 : ℚ :=
  (326029893 : ℚ) / 699190476800

def SurrogateDiagonalTailChunk000Sub000Block015Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 697
    = surrogateDiagTailX0RatChunk000Sub000Block015Part019

theorem surrogateDiagonalTailChunk000Sub000Block015Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block015Part019CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block015Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block015Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block015Part019CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block015Part019SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block015Part019] using hcert

def TailChunk000Sub000Block015Part020SupportExplicit : Finset ℕ :=
  ([698] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block015Part020 : ℚ :=
  (106298777725 : ℚ) / 36672780129408

def SurrogateDiagonalTailChunk000Sub000Block015Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 698
    = surrogateDiagTailX0RatChunk000Sub000Block015Part020

theorem surrogateDiagonalTailChunk000Sub000Block015Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block015Part020CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block015Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block015Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block015Part020CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block015Part020SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block015Part020] using hcert

def TailChunk000Sub000Block015Part021SupportExplicit : Finset ℕ :=
  ([699] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block015Part021 : ℚ :=
  (145302813775 : ℚ) / 115904095223808

def SurrogateDiagonalTailChunk000Sub000Block015Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 699
    = surrogateDiagTailX0RatChunk000Sub000Block015Part021

theorem surrogateDiagonalTailChunk000Sub000Block015Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block015Part021CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block015Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block015Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block015Part021CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block015Part021SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block015Part021] using hcert

def TailChunk000Sub000Block015Part022SupportExplicit : Finset ℕ :=
  ([701] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block015Part022 : ℚ :=
  (1227028297 : ℚ) / 3430686000000

def SurrogateDiagonalTailChunk000Sub000Block015Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 701
    = surrogateDiagTailX0RatChunk000Sub000Block015Part022

theorem surrogateDiagonalTailChunk000Sub000Block015Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block015Part022CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block015Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block015Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block015Part022CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block015Part022SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block015Part022] using hcert

def TailChunk000Sub000Block015Part023SupportExplicit : Finset ℕ :=
  ([703] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block015Part023 : ℚ :=
  (199587973375 : ℚ) / 440886582724608

def SurrogateDiagonalTailChunk000Sub000Block015Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 703
    = surrogateDiagTailX0RatChunk000Sub000Block015Part023

theorem surrogateDiagonalTailChunk000Sub000Block015Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block015Part023CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block015Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block015Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block015Part023CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block015Part023SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block015Part023] using hcert

def TailChunk000Sub000Block015Part024SupportExplicit : Finset ℕ :=
  ([705] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block015Part024 : ℚ :=
  (18948750975 : ℚ) / 7643053211648

def SurrogateDiagonalTailChunk000Sub000Block015Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 705
    = surrogateDiagTailX0RatChunk000Sub000Block015Part024

theorem surrogateDiagonalTailChunk000Sub000Block015Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block015Part024CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block015Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block015Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block015Part024CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block015Part024SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block015Part024] using hcert

def surrogateDiagonalTailChunk000Sub000Block015HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block015Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block015Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block015Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block015Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block015Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block015Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block015Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block015Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block015Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block015Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block015Head : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block015Part000
    + surrogateDiagTailX0RatChunk000Sub000Block015Part001
    + surrogateDiagTailX0RatChunk000Sub000Block015Part002
    + surrogateDiagTailX0RatChunk000Sub000Block015Part003
    + surrogateDiagTailX0RatChunk000Sub000Block015Part004
    + surrogateDiagTailX0RatChunk000Sub000Block015Part005
    + surrogateDiagTailX0RatChunk000Sub000Block015Part006
    + surrogateDiagTailX0RatChunk000Sub000Block015Part007
    + surrogateDiagTailX0RatChunk000Sub000Block015Part008
    + surrogateDiagTailX0RatChunk000Sub000Block015Part009

def surrogateDiagonalTailChunk000Sub000Block015MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block015Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block015Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block015Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block015Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block015Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block015Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block015Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block015Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block015Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block015Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block015Mid : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block015Part010
    + surrogateDiagTailX0RatChunk000Sub000Block015Part011
    + surrogateDiagTailX0RatChunk000Sub000Block015Part012
    + surrogateDiagTailX0RatChunk000Sub000Block015Part013
    + surrogateDiagTailX0RatChunk000Sub000Block015Part014
    + surrogateDiagTailX0RatChunk000Sub000Block015Part015
    + surrogateDiagTailX0RatChunk000Sub000Block015Part016
    + surrogateDiagTailX0RatChunk000Sub000Block015Part017
    + surrogateDiagTailX0RatChunk000Sub000Block015Part018
    + surrogateDiagTailX0RatChunk000Sub000Block015Part019

def surrogateDiagonalTailChunk000Sub000Block015TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block015Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block015Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block015Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block015Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block015Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block015Tail : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block015Part020
    + surrogateDiagTailX0RatChunk000Sub000Block015Part021
    + surrogateDiagTailX0RatChunk000Sub000Block015Part022
    + surrogateDiagTailX0RatChunk000Sub000Block015Part023
    + surrogateDiagTailX0RatChunk000Sub000Block015Part024

def surrogateDiagonalTailChunk000Sub000Block015Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub000Block015HeadSum X0
    + surrogateDiagonalTailChunk000Sub000Block015MidSum X0
    + surrogateDiagonalTailChunk000Sub000Block015TailSum X0

def surrogateDiagTailX0RatChunk000Sub000Block015 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block015Part000
    + surrogateDiagTailX0RatChunk000Sub000Block015Part001
    + surrogateDiagTailX0RatChunk000Sub000Block015Part002
    + surrogateDiagTailX0RatChunk000Sub000Block015Part003
    + surrogateDiagTailX0RatChunk000Sub000Block015Part004
    + surrogateDiagTailX0RatChunk000Sub000Block015Part005
    + surrogateDiagTailX0RatChunk000Sub000Block015Part006
    + surrogateDiagTailX0RatChunk000Sub000Block015Part007
    + surrogateDiagTailX0RatChunk000Sub000Block015Part008
    + surrogateDiagTailX0RatChunk000Sub000Block015Part009
    + surrogateDiagTailX0RatChunk000Sub000Block015Part010
    + surrogateDiagTailX0RatChunk000Sub000Block015Part011
    + surrogateDiagTailX0RatChunk000Sub000Block015Part012
    + surrogateDiagTailX0RatChunk000Sub000Block015Part013
    + surrogateDiagTailX0RatChunk000Sub000Block015Part014
    + surrogateDiagTailX0RatChunk000Sub000Block015Part015
    + surrogateDiagTailX0RatChunk000Sub000Block015Part016
    + surrogateDiagTailX0RatChunk000Sub000Block015Part017
    + surrogateDiagTailX0RatChunk000Sub000Block015Part018
    + surrogateDiagTailX0RatChunk000Sub000Block015Part019
    + surrogateDiagTailX0RatChunk000Sub000Block015Part020
    + surrogateDiagTailX0RatChunk000Sub000Block015Part021
    + surrogateDiagTailX0RatChunk000Sub000Block015Part022
    + surrogateDiagTailX0RatChunk000Sub000Block015Part023
    + surrogateDiagTailX0RatChunk000Sub000Block015Part024

theorem surrogateDiagTailX0RatChunk000Sub000Block015_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk000Sub000Block015Head + surrogateDiagTailX0RatChunk000Sub000Block015Mid + surrogateDiagTailX0RatChunk000Sub000Block015Tail =
      surrogateDiagTailX0RatChunk000Sub000Block015 := by
  unfold surrogateDiagTailX0RatChunk000Sub000Block015Head surrogateDiagTailX0RatChunk000Sub000Block015Mid surrogateDiagTailX0RatChunk000Sub000Block015Tail surrogateDiagTailX0RatChunk000Sub000Block015
  ring

def SurrogateDiagonalTailChunk000Sub000Block015HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block015HeadSum X0 = surrogateDiagTailX0RatChunk000Sub000Block015Head

def SurrogateDiagonalTailChunk000Sub000Block015MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block015MidSum X0 = surrogateDiagTailX0RatChunk000Sub000Block015Mid

def SurrogateDiagonalTailChunk000Sub000Block015TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block015TailSum X0 = surrogateDiagTailX0RatChunk000Sub000Block015Tail

theorem surrogateDiagonalTailChunk000Sub000Block015_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk000Sub000Block015HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk000Sub000Block015MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk000Sub000Block015TailCertificateAt X0) :
    surrogateDiagonalTailChunk000Sub000Block015Sum X0 = surrogateDiagTailX0RatChunk000Sub000Block015 := by
  unfold SurrogateDiagonalTailChunk000Sub000Block015HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk000Sub000Block015MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk000Sub000Block015TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk000Sub000Block015Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk000Sub000Block015_eq_head_add_mid_add_tail

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

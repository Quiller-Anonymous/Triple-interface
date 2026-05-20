import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0TailPilot25

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

open scoped BigOperators

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

/- Generated direct-term certificate blocks for tail chunk 000, subchunk 000, blocks [39,40). -/

/- Block 039 covers tail-support indices [975,1000) and q from 1649 to 1693. -/

def TailChunk000Sub000Block039Part000SupportExplicit : Finset ℕ :=
  ([1649] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block039Part000 : ℚ :=
  (475634122375 : ℚ) / 13918477177847808

def SurrogateDiagonalTailChunk000Sub000Block039Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1649
    = surrogateDiagTailX0RatChunk000Sub000Block039Part000

theorem surrogateDiagonalTailChunk000Sub000Block039Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block039Part000CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block039Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block039Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block039Part000CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block039Part000SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block039Part000] using hcert

def TailChunk000Sub000Block039Part001SupportExplicit : Finset ℕ :=
  ([1651] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block039Part001 : ℚ :=
  (234095434625 : ℚ) / 6534374599517184

def SurrogateDiagonalTailChunk000Sub000Block039Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1651
    = surrogateDiagTailX0RatChunk000Sub000Block039Part001

theorem surrogateDiagonalTailChunk000Sub000Block039Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block039Part001CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block039Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block039Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block039Part001CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block039Part001SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block039Part001] using hcert

def TailChunk000Sub000Block039Part002SupportExplicit : Finset ℕ :=
  ([1653] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block039Part002 : ℚ :=
  (312634638175 : ℚ) / 2581481323266048

def SurrogateDiagonalTailChunk000Sub000Block039Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1653
    = surrogateDiagTailX0RatChunk000Sub000Block039Part002

theorem surrogateDiagonalTailChunk000Sub000Block039Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block039Part002CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block039Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block039Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block039Part002CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block039Part002SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block039Part002] using hcert

def TailChunk000Sub000Block039Part003SupportExplicit : Finset ℕ :=
  ([1654] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block039Part003 : ℚ :=
  (85405633875 : ℚ) / 387994700236696

def SurrogateDiagonalTailChunk000Sub000Block039Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1654
    = surrogateDiagTailX0RatChunk000Sub000Block039Part003

theorem surrogateDiagonalTailChunk000Sub000Block039Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block039Part003CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block039Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block039Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block039Part003CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block039Part003SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block039Part003] using hcert

def TailChunk000Sub000Block039Part004SupportExplicit : Finset ℕ :=
  ([1655] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block039Part004 : ℚ :=
  (1638816697 : ℚ) / 30365649515520

def SurrogateDiagonalTailChunk000Sub000Block039Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1655
    = surrogateDiagTailX0RatChunk000Sub000Block039Part004

theorem surrogateDiagonalTailChunk000Sub000Block039Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block039Part004CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block039Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block039Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block039Part004CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block039Part004SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block039Part004] using hcert

def TailChunk000Sub000Block039Part005SupportExplicit : Finset ℕ :=
  ([1657] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block039Part005 : ℚ :=
  (57178140425 : ℚ) / 2089419671734272

def SurrogateDiagonalTailChunk000Sub000Block039Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1657
    = surrogateDiagTailX0RatChunk000Sub000Block039Part005

theorem surrogateDiagonalTailChunk000Sub000Block039Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block039Part005CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block039Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block039Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block039Part005CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block039Part005SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block039Part005] using hcert

def TailChunk000Sub000Block039Part006SupportExplicit : Finset ℕ :=
  ([1658] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block039Part006 : ℚ :=
  (3178489625 : ℚ) / 14509858831488

def SurrogateDiagonalTailChunk000Sub000Block039Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1658
    = surrogateDiagTailX0RatChunk000Sub000Block039Part006

theorem surrogateDiagonalTailChunk000Sub000Block039Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block039Part006CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block039Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block039Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block039Part006CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block039Part006SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block039Part006] using hcert

def TailChunk000Sub000Block039Part007SupportExplicit : Finset ℕ :=
  ([1659] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block039Part007 : ℚ :=
  (19411375 : ℚ) / 127924033536

def SurrogateDiagonalTailChunk000Sub000Block039Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1659
    = surrogateDiagTailX0RatChunk000Sub000Block039Part007

theorem surrogateDiagonalTailChunk000Sub000Block039Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block039Part007CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block039Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block039Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block039Part007CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block039Part007SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block039Part007] using hcert

def TailChunk000Sub000Block039Part008SupportExplicit : Finset ℕ :=
  ([1661] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block039Part008 : ℚ :=
  (373810547 : ℚ) / 10127025000000

def SurrogateDiagonalTailChunk000Sub000Block039Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1661
    = surrogateDiagTailX0RatChunk000Sub000Block039Part008

theorem surrogateDiagonalTailChunk000Sub000Block039Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block039Part008CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block039Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block039Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block039Part008CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block039Part008SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block039Part008] using hcert

def TailChunk000Sub000Block039Part009SupportExplicit : Finset ℕ :=
  ([1662] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block039Part009 : ℚ :=
  (11467925 : ℚ) / 15474087936

def SurrogateDiagonalTailChunk000Sub000Block039Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1662
    = surrogateDiagTailX0RatChunk000Sub000Block039Part009

theorem surrogateDiagonalTailChunk000Sub000Block039Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block039Part009CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block039Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block039Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block039Part009CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block039Part009SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block039Part009] using hcert

def TailChunk000Sub000Block039Part010SupportExplicit : Finset ℕ :=
  ([1663] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block039Part010 : ℚ :=
  (57592974425 : ℚ) / 2119866087199752

def SurrogateDiagonalTailChunk000Sub000Block039Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1663
    = surrogateDiagTailX0RatChunk000Sub000Block039Part010

theorem surrogateDiagonalTailChunk000Sub000Block039Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block039Part010CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block039Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block039Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block039Part010CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block039Part010SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block039Part010] using hcert

def TailChunk000Sub000Block039Part011SupportExplicit : Finset ℕ :=
  ([1667] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block039Part011 : ℚ :=
  (125025 : ℚ) / 4624076296

def SurrogateDiagonalTailChunk000Sub000Block039Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1667
    = surrogateDiagTailX0RatChunk000Sub000Block039Part011

theorem surrogateDiagonalTailChunk000Sub000Block039Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block039Part011CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block039Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block039Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block039Part011CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block039Part011SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block039Part011] using hcert

def TailChunk000Sub000Block039Part012SupportExplicit : Finset ℕ :=
  ([1669] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block039Part012 : ℚ :=
  (58009307825 : ℚ) / 2150644038959232

def SurrogateDiagonalTailChunk000Sub000Block039Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1669
    = surrogateDiagTailX0RatChunk000Sub000Block039Part012

theorem surrogateDiagonalTailChunk000Sub000Block039Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block039Part012CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block039Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block039Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block039Part012CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block039Part012SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block039Part012] using hcert

def TailChunk000Sub000Block039Part013SupportExplicit : Finset ℕ :=
  ([1670] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block039Part013 : ℚ :=
  (103116109325 : ℚ) / 243035200840704

def SurrogateDiagonalTailChunk000Sub000Block039Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1670
    = surrogateDiagTailX0RatChunk000Sub000Block039Part013

theorem surrogateDiagonalTailChunk000Sub000Block039Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block039Part013CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block039Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block039Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block039Part013CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block039Part013SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block039Part013] using hcert

def TailChunk000Sub000Block039Part014SupportExplicit : Finset ℕ :=
  ([1671] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block039Part014 : ℚ :=
  (4355025 : ℚ) / 47782533248

def SurrogateDiagonalTailChunk000Sub000Block039Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1671
    = surrogateDiagTailX0RatChunk000Sub000Block039Part014

theorem surrogateDiagonalTailChunk000Sub000Block039Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block039Part014CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block039Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block039Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block039Part014CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block039Part014SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block039Part014] using hcert

def TailChunk000Sub000Block039Part015SupportExplicit : Finset ℕ :=
  ([1673] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block039Part015 : ℚ :=
  (444486022525 : ℚ) / 10397757600332928

def SurrogateDiagonalTailChunk000Sub000Block039Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1673
    = surrogateDiagTailX0RatChunk000Sub000Block039Part015

theorem surrogateDiagonalTailChunk000Sub000Block039Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block039Part015CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block039Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block039Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block039Part015CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block039Part015SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block039Part015] using hcert

def TailChunk000Sub000Block039Part016SupportExplicit : Finset ℕ :=
  ([1677] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block039Part016 : ℚ :=
  (79241985325 : ℚ) / 645370330816512

def SurrogateDiagonalTailChunk000Sub000Block039Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1677
    = surrogateDiagTailX0RatChunk000Sub000Block039Part016

theorem surrogateDiagonalTailChunk000Sub000Block039Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block039Part016CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block039Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block039Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block039Part016CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block039Part016SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block039Part016] using hcert

def TailChunk000Sub000Block039Part017SupportExplicit : Finset ℕ :=
  ([1678] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block039Part017 : ℚ :=
  (87902134875 : ℚ) / 411037720719256

def SurrogateDiagonalTailChunk000Sub000Block039Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1678
    = surrogateDiagTailX0RatChunk000Sub000Block039Part017

theorem surrogateDiagonalTailChunk000Sub000Block039Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block039Part017CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block039Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block039Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block039Part017CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block039Part017SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block039Part017] using hcert

def TailChunk000Sub000Block039Part018SupportExplicit : Finset ℕ :=
  ([1679] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block039Part018 : ℚ :=
  (498376006675 : ℚ) / 15741552708845568

def SurrogateDiagonalTailChunk000Sub000Block039Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1679
    = surrogateDiagTailX0RatChunk000Sub000Block039Part018

theorem surrogateDiagonalTailChunk000Sub000Block039Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block039Part018CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block039Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block039Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block039Part018CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block039Part018SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block039Part018] using hcert

def TailChunk000Sub000Block039Part019SupportExplicit : Finset ℕ :=
  ([1685] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block039Part019 : ℚ :=
  (212346085625 : ℚ) / 4079377893556224

def SurrogateDiagonalTailChunk000Sub000Block039Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1685
    = surrogateDiagTailX0RatChunk000Sub000Block039Part019

theorem surrogateDiagonalTailChunk000Sub000Block039Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block039Part019CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block039Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block039Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block039Part019CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block039Part019SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block039Part019] using hcert

def TailChunk000Sub000Block039Part020SupportExplicit : Finset ℕ :=
  ([1686] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block039Part020 : ℚ :=
  (1416183 : ℚ) / 1966899200

def SurrogateDiagonalTailChunk000Sub000Block039Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1686
    = surrogateDiagTailX0RatChunk000Sub000Block039Part020

theorem surrogateDiagonalTailChunk000Sub000Block039Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block039Part020CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block039Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block039Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block039Part020CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block039Part020SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block039Part020] using hcert

def TailChunk000Sub000Block039Part021SupportExplicit : Finset ℕ :=
  ([1687] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block039Part021 : ℚ :=
  (506175173 : ℚ) / 11946324787200

def SurrogateDiagonalTailChunk000Sub000Block039Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1687
    = surrogateDiagTailX0RatChunk000Sub000Block039Part021

theorem surrogateDiagonalTailChunk000Sub000Block039Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block039Part021CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block039Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block039Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block039Part021CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block039Part021SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block039Part021] using hcert

def TailChunk000Sub000Block039Part022SupportExplicit : Finset ℕ :=
  ([1689] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block039Part022 : ℚ :=
  (69256824775 : ℚ) / 997773838224672

def SurrogateDiagonalTailChunk000Sub000Block039Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1689
    = surrogateDiagTailX0RatChunk000Sub000Block039Part022

theorem surrogateDiagonalTailChunk000Sub000Block039Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block039Part022CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block039Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block039Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block039Part022CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block039Part022SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block039Part022] using hcert

def TailChunk000Sub000Block039Part023SupportExplicit : Finset ℕ :=
  ([1691] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block039Part023 : ℚ :=
  (251121089075 : ℚ) / 7870776354422784

def SurrogateDiagonalTailChunk000Sub000Block039Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1691
    = surrogateDiagTailX0RatChunk000Sub000Block039Part023

theorem surrogateDiagonalTailChunk000Sub000Block039Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block039Part023CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block039Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block039Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block039Part023CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block039Part023SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block039Part023] using hcert

def TailChunk000Sub000Block039Part024SupportExplicit : Finset ℕ :=
  ([1693] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block039Part024 : ℚ :=
  (59689635425 : ℚ) / 2277119300153472

def SurrogateDiagonalTailChunk000Sub000Block039Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1693
    = surrogateDiagTailX0RatChunk000Sub000Block039Part024

theorem surrogateDiagonalTailChunk000Sub000Block039Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block039Part024CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block039Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block039Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block039Part024CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block039Part024SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block039Part024] using hcert

def surrogateDiagonalTailChunk000Sub000Block039HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block039Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block039Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block039Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block039Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block039Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block039Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block039Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block039Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block039Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block039Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block039Head : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block039Part000
    + surrogateDiagTailX0RatChunk000Sub000Block039Part001
    + surrogateDiagTailX0RatChunk000Sub000Block039Part002
    + surrogateDiagTailX0RatChunk000Sub000Block039Part003
    + surrogateDiagTailX0RatChunk000Sub000Block039Part004
    + surrogateDiagTailX0RatChunk000Sub000Block039Part005
    + surrogateDiagTailX0RatChunk000Sub000Block039Part006
    + surrogateDiagTailX0RatChunk000Sub000Block039Part007
    + surrogateDiagTailX0RatChunk000Sub000Block039Part008
    + surrogateDiagTailX0RatChunk000Sub000Block039Part009

def surrogateDiagonalTailChunk000Sub000Block039MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block039Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block039Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block039Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block039Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block039Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block039Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block039Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block039Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block039Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block039Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block039Mid : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block039Part010
    + surrogateDiagTailX0RatChunk000Sub000Block039Part011
    + surrogateDiagTailX0RatChunk000Sub000Block039Part012
    + surrogateDiagTailX0RatChunk000Sub000Block039Part013
    + surrogateDiagTailX0RatChunk000Sub000Block039Part014
    + surrogateDiagTailX0RatChunk000Sub000Block039Part015
    + surrogateDiagTailX0RatChunk000Sub000Block039Part016
    + surrogateDiagTailX0RatChunk000Sub000Block039Part017
    + surrogateDiagTailX0RatChunk000Sub000Block039Part018
    + surrogateDiagTailX0RatChunk000Sub000Block039Part019

def surrogateDiagonalTailChunk000Sub000Block039TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block039Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block039Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block039Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block039Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block039Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block039Tail : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block039Part020
    + surrogateDiagTailX0RatChunk000Sub000Block039Part021
    + surrogateDiagTailX0RatChunk000Sub000Block039Part022
    + surrogateDiagTailX0RatChunk000Sub000Block039Part023
    + surrogateDiagTailX0RatChunk000Sub000Block039Part024

def surrogateDiagonalTailChunk000Sub000Block039Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub000Block039HeadSum X0
    + surrogateDiagonalTailChunk000Sub000Block039MidSum X0
    + surrogateDiagonalTailChunk000Sub000Block039TailSum X0

def surrogateDiagTailX0RatChunk000Sub000Block039 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block039Part000
    + surrogateDiagTailX0RatChunk000Sub000Block039Part001
    + surrogateDiagTailX0RatChunk000Sub000Block039Part002
    + surrogateDiagTailX0RatChunk000Sub000Block039Part003
    + surrogateDiagTailX0RatChunk000Sub000Block039Part004
    + surrogateDiagTailX0RatChunk000Sub000Block039Part005
    + surrogateDiagTailX0RatChunk000Sub000Block039Part006
    + surrogateDiagTailX0RatChunk000Sub000Block039Part007
    + surrogateDiagTailX0RatChunk000Sub000Block039Part008
    + surrogateDiagTailX0RatChunk000Sub000Block039Part009
    + surrogateDiagTailX0RatChunk000Sub000Block039Part010
    + surrogateDiagTailX0RatChunk000Sub000Block039Part011
    + surrogateDiagTailX0RatChunk000Sub000Block039Part012
    + surrogateDiagTailX0RatChunk000Sub000Block039Part013
    + surrogateDiagTailX0RatChunk000Sub000Block039Part014
    + surrogateDiagTailX0RatChunk000Sub000Block039Part015
    + surrogateDiagTailX0RatChunk000Sub000Block039Part016
    + surrogateDiagTailX0RatChunk000Sub000Block039Part017
    + surrogateDiagTailX0RatChunk000Sub000Block039Part018
    + surrogateDiagTailX0RatChunk000Sub000Block039Part019
    + surrogateDiagTailX0RatChunk000Sub000Block039Part020
    + surrogateDiagTailX0RatChunk000Sub000Block039Part021
    + surrogateDiagTailX0RatChunk000Sub000Block039Part022
    + surrogateDiagTailX0RatChunk000Sub000Block039Part023
    + surrogateDiagTailX0RatChunk000Sub000Block039Part024

theorem surrogateDiagTailX0RatChunk000Sub000Block039_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk000Sub000Block039Head + surrogateDiagTailX0RatChunk000Sub000Block039Mid + surrogateDiagTailX0RatChunk000Sub000Block039Tail =
      surrogateDiagTailX0RatChunk000Sub000Block039 := by
  unfold surrogateDiagTailX0RatChunk000Sub000Block039Head surrogateDiagTailX0RatChunk000Sub000Block039Mid surrogateDiagTailX0RatChunk000Sub000Block039Tail surrogateDiagTailX0RatChunk000Sub000Block039
  ring

def SurrogateDiagonalTailChunk000Sub000Block039HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block039HeadSum X0 = surrogateDiagTailX0RatChunk000Sub000Block039Head

def SurrogateDiagonalTailChunk000Sub000Block039MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block039MidSum X0 = surrogateDiagTailX0RatChunk000Sub000Block039Mid

def SurrogateDiagonalTailChunk000Sub000Block039TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block039TailSum X0 = surrogateDiagTailX0RatChunk000Sub000Block039Tail

theorem surrogateDiagonalTailChunk000Sub000Block039_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk000Sub000Block039HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk000Sub000Block039MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk000Sub000Block039TailCertificateAt X0) :
    surrogateDiagonalTailChunk000Sub000Block039Sum X0 = surrogateDiagTailX0RatChunk000Sub000Block039 := by
  unfold SurrogateDiagonalTailChunk000Sub000Block039HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk000Sub000Block039MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk000Sub000Block039TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk000Sub000Block039Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk000Sub000Block039_eq_head_add_mid_add_tail

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

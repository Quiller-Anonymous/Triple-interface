import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0TailPilot25

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

open scoped BigOperators

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

/- Generated direct-term certificate blocks for tail chunk 000, subchunk 000, blocks [40,41). -/

/- Block 040 covers tail-support indices [1000,1025) and q from 1695 to 1735. -/

def TailChunk000Sub000Block040Part000SupportExplicit : Finset ℕ :=
  ([1695] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block040Part000 : ℚ :=
  (284774567275 : ℚ) / 1611606081404928

def SurrogateDiagonalTailChunk000Sub000Block040Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1695
    = surrogateDiagTailX0RatChunk000Sub000Block040Part000

theorem surrogateDiagonalTailChunk000Sub000Block040Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block040Part000CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block040Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block040Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block040Part000CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block040Part000SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block040Part000] using hcert

def TailChunk000Sub000Block040Part001SupportExplicit : Finset ℕ :=
  ([1697] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block040Part001 : ℚ :=
  (179916067275 : ℚ) / 6896186465714176

def SurrogateDiagonalTailChunk000Sub000Block040Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1697
    = surrogateDiagTailX0RatChunk000Sub000Block040Part001

theorem surrogateDiagonalTailChunk000Sub000Block040Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block040Part001CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block040Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block040Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block040Part001CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block040Part001SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block040Part001] using hcert

def TailChunk000Sub000Block040Part002SupportExplicit : Finset ℕ :=
  ([1698] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block040Part002 : ℚ :=
  (11970125 : ℚ) / 16864177536

def SurrogateDiagonalTailChunk000Sub000Block040Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1698
    = surrogateDiagTailX0RatChunk000Sub000Block040Part002

theorem surrogateDiagonalTailChunk000Sub000Block040Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block040Part002CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block040Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block040Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block040Part002CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block040Part002SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block040Part002] using hcert

def TailChunk000Sub000Block040Part003SupportExplicit : Finset ℕ :=
  ([1699] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block040Part003 : ℚ :=
  (60113465825 : ℚ) / 2309591077410312

def SurrogateDiagonalTailChunk000Sub000Block040Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1699
    = surrogateDiagTailX0RatChunk000Sub000Block040Part003

theorem surrogateDiagonalTailChunk000Sub000Block040Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block040Part003CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block040Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block040Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block040Part003CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block040Part003SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block040Part003] using hcert

def TailChunk000Sub000Block040Part004SupportExplicit : Finset ℕ :=
  ([1702] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block040Part004 : ℚ :=
  (252396973825 : ℚ) / 983847044302848

def SurrogateDiagonalTailChunk000Sub000Block040Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1702
    = surrogateDiagTailX0RatChunk000Sub000Block040Part004

theorem surrogateDiagonalTailChunk000Sub000Block040Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block040Part004CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block040Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block040Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block040Part004CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block040Part004SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block040Part004] using hcert

def TailChunk000Sub000Block040Part005SupportExplicit : Finset ℕ :=
  ([1703] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block040Part005 : ℚ :=
  (994184519 : ℚ) / 29617967208960

def SurrogateDiagonalTailChunk000Sub000Block040Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1703
    = surrogateDiagTailX0RatChunk000Sub000Block040Part005

theorem surrogateDiagonalTailChunk000Sub000Block040Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block040Part005CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block040Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block040Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block040Part005CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block040Part005SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block040Part005] using hcert

def TailChunk000Sub000Block040Part006SupportExplicit : Finset ℕ :=
  ([1705] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block040Part006 : ℚ :=
  (15105493579 : ℚ) / 207401472000000

def SurrogateDiagonalTailChunk000Sub000Block040Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1705
    = surrogateDiagTailX0RatChunk000Sub000Block040Part006

theorem surrogateDiagonalTailChunk000Sub000Block040Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block040Part006CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block040Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block040Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block040Part006CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block040Part006SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block040Part006] using hcert

def TailChunk000Sub000Block040Part007SupportExplicit : Finset ℕ :=
  ([1706] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block040Part007 : ℚ :=
  (3365191625 : ℚ) / 16266728535168

def SurrogateDiagonalTailChunk000Sub000Block040Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1706
    = surrogateDiagTailX0RatChunk000Sub000Block040Part007

theorem surrogateDiagonalTailChunk000Sub000Block040Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block040Part007CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block040Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block040Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block040Part007CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block040Part007SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block040Part007] using hcert

def TailChunk000Sub000Block040Part008SupportExplicit : Finset ℕ :=
  ([1707] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block040Part008 : ℚ :=
  (1136175 : ℚ) / 13010780672

def SurrogateDiagonalTailChunk000Sub000Block040Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1707
    = surrogateDiagTailX0RatChunk000Sub000Block040Part008

theorem surrogateDiagonalTailChunk000Sub000Block040Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block040Part008CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block040Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block040Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block040Part008CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block040Part008SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block040Part008] using hcert

def TailChunk000Sub000Block040Part009SupportExplicit : Finset ℕ :=
  ([1709] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block040Part009 : ℚ :=
  (3723868275 : ℚ) / 144764138291584

def SurrogateDiagonalTailChunk000Sub000Block040Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1709
    = surrogateDiagTailX0RatChunk000Sub000Block040Part009

theorem surrogateDiagonalTailChunk000Sub000Block040Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block040Part009CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block040Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block040Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block040Part009CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block040Part009SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block040Part009] using hcert

def TailChunk000Sub000Block040Part010SupportExplicit : Finset ℕ :=
  ([1711] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block040Part010 : ℚ :=
  (520430038225 : ℚ) / 17392858289522688

def SurrogateDiagonalTailChunk000Sub000Block040Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1711
    = surrogateDiagTailX0RatChunk000Sub000Block040Part010

theorem surrogateDiagonalTailChunk000Sub000Block040Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block040Part010CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block040Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block040Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block040Part010CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block040Part010SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block040Part010] using hcert

def TailChunk000Sub000Block040Part011SupportExplicit : Finset ℕ :=
  ([1713] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block040Part011 : ℚ :=
  (244091 : ℚ) / 2814933600

def SurrogateDiagonalTailChunk000Sub000Block040Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1713
    = surrogateDiagTailX0RatChunk000Sub000Block040Part011

theorem surrogateDiagonalTailChunk000Sub000Block040Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block040Part011CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block040Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block040Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block040Part011CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block040Part011SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block040Part011] using hcert

def TailChunk000Sub000Block040Part012SupportExplicit : Finset ℕ :=
  ([1714] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block040Part012 : ℚ :=
  (91714318875 : ℚ) / 447507855087616

def SurrogateDiagonalTailChunk000Sub000Block040Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1714
    = surrogateDiagTailX0RatChunk000Sub000Block040Part012

theorem surrogateDiagonalTailChunk000Sub000Block040Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block040Part012CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block040Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block040Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block040Part012CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block040Part012SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block040Part012] using hcert

def TailChunk000Sub000Block040Part013SupportExplicit : Finset ℕ :=
  ([1717] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block040Part013 : ℚ :=
  (2057699917 : ℚ) / 65549107200000

def SurrogateDiagonalTailChunk000Sub000Block040Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1717
    = surrogateDiagTailX0RatChunk000Sub000Block040Part013

theorem surrogateDiagonalTailChunk000Sub000Block040Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block040Part013CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block040Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block040Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block040Part013CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block040Part013SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block040Part013] using hcert

def TailChunk000Sub000Block040Part014SupportExplicit : Finset ℕ :=
  ([1718] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block040Part014 : ℚ :=
  (115201671125 : ℚ) / 677557277978724

def SurrogateDiagonalTailChunk000Sub000Block040Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1718
    = surrogateDiagTailX0RatChunk000Sub000Block040Part014

theorem surrogateDiagonalTailChunk000Sub000Block040Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block040Part014CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block040Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block040Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block040Part014CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block040Part014SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block040Part014] using hcert

def TailChunk000Sub000Block040Part015SupportExplicit : Finset ℕ :=
  ([1721] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block040Part015 : ℚ :=
  (7401640659 : ℚ) / 291796032870400

def SurrogateDiagonalTailChunk000Sub000Block040Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1721
    = surrogateDiagTailX0RatChunk000Sub000Block040Part015

theorem surrogateDiagonalTailChunk000Sub000Block040Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block040Part015CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block040Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block040Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block040Part015CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block040Part015SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block040Part015] using hcert

def TailChunk000Sub000Block040Part016SupportExplicit : Finset ℕ :=
  ([1722] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block040Part016 : ℚ :=
  (668380253 : ℚ) / 589941964800

def SurrogateDiagonalTailChunk000Sub000Block040Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1722
    = surrogateDiagTailX0RatChunk000Sub000Block040Part016

theorem surrogateDiagonalTailChunk000Sub000Block040Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block040Part016CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block040Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block040Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block040Part016CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block040Part016SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block040Part016] using hcert

def TailChunk000Sub000Block040Part017SupportExplicit : Finset ℕ :=
  ([1723] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block040Part017 : ℚ :=
  (1261709825 : ℚ) / 49856393324808

def SurrogateDiagonalTailChunk000Sub000Block040Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1723
    = surrogateDiagTailX0RatChunk000Sub000Block040Part017

theorem surrogateDiagonalTailChunk000Sub000Block040Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block040Part017CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block040Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block040Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block040Part017CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block040Part017SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block040Part017] using hcert

def TailChunk000Sub000Block040Part018SupportExplicit : Finset ℕ :=
  ([1726] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block040Part018 : ℚ :=
  (93003028875 : ℚ) / 460187340677656

def SurrogateDiagonalTailChunk000Sub000Block040Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1726
    = surrogateDiagTailX0RatChunk000Sub000Block040Part018

theorem surrogateDiagonalTailChunk000Sub000Block040Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block040Part018CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block040Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block040Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block040Part018CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block040Part018SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block040Part018] using hcert

def TailChunk000Sub000Block040Part019SupportExplicit : Finset ℕ :=
  ([1727] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block040Part019 : ℚ :=
  (3357444821 : ℚ) / 98726557363200

def SurrogateDiagonalTailChunk000Sub000Block040Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1727
    = surrogateDiagTailX0RatChunk000Sub000Block040Part019

theorem surrogateDiagonalTailChunk000Sub000Block040Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block040Part019CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block040Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block040Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block040Part019CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block040Part019SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block040Part019] using hcert

def TailChunk000Sub000Block040Part020SupportExplicit : Finset ℕ :=
  ([1729] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block040Part020 : ℚ :=
  (207452717375 : ℚ) / 3527092661796864

def SurrogateDiagonalTailChunk000Sub000Block040Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1729
    = surrogateDiagTailX0RatChunk000Sub000Block040Part020

theorem surrogateDiagonalTailChunk000Sub000Block040Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block040Part020CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block040Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block040Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block040Part020CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block040Part020SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block040Part020] using hcert

def TailChunk000Sub000Block040Part021SupportExplicit : Finset ℕ :=
  ([1730] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block040Part021 : ℚ :=
  (16131096075 : ℚ) / 46687365259264

def SurrogateDiagonalTailChunk000Sub000Block040Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1730
    = surrogateDiagTailX0RatChunk000Sub000Block040Part021

theorem surrogateDiagonalTailChunk000Sub000Block040Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block040Part021CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block040Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block040Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block040Part021CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block040Part021SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block040Part021] using hcert

def TailChunk000Sub000Block040Part022SupportExplicit : Finset ℕ :=
  ([1731] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block040Part022 : ℚ :=
  (194725 : ℚ) / 2293235712

def SurrogateDiagonalTailChunk000Sub000Block040Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1731
    = surrogateDiagTailX0RatChunk000Sub000Block040Part022

theorem surrogateDiagonalTailChunk000Sub000Block040Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block040Part022CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block040Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block040Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block040Part022CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block040Part022SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block040Part022] using hcert

def TailChunk000Sub000Block040Part023SupportExplicit : Finset ℕ :=
  ([1733] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block040Part023 : ℚ :=
  (187630480275 : ℚ) / 7500619849818496

def SurrogateDiagonalTailChunk000Sub000Block040Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1733
    = surrogateDiagTailX0RatChunk000Sub000Block040Part023

theorem surrogateDiagonalTailChunk000Sub000Block040Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block040Part023CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block040Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block040Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block040Part023CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block040Part023SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block040Part023] using hcert

def TailChunk000Sub000Block040Part024SupportExplicit : Finset ℕ :=
  ([1735] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block040Part024 : ℚ :=
  (225136143125 : ℚ) / 4587131852841984

def SurrogateDiagonalTailChunk000Sub000Block040Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1735
    = surrogateDiagTailX0RatChunk000Sub000Block040Part024

theorem surrogateDiagonalTailChunk000Sub000Block040Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block040Part024CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block040Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block040Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block040Part024CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block040Part024SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block040Part024] using hcert

def surrogateDiagonalTailChunk000Sub000Block040HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block040Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block040Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block040Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block040Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block040Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block040Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block040Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block040Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block040Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block040Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block040Head : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block040Part000
    + surrogateDiagTailX0RatChunk000Sub000Block040Part001
    + surrogateDiagTailX0RatChunk000Sub000Block040Part002
    + surrogateDiagTailX0RatChunk000Sub000Block040Part003
    + surrogateDiagTailX0RatChunk000Sub000Block040Part004
    + surrogateDiagTailX0RatChunk000Sub000Block040Part005
    + surrogateDiagTailX0RatChunk000Sub000Block040Part006
    + surrogateDiagTailX0RatChunk000Sub000Block040Part007
    + surrogateDiagTailX0RatChunk000Sub000Block040Part008
    + surrogateDiagTailX0RatChunk000Sub000Block040Part009

def surrogateDiagonalTailChunk000Sub000Block040MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block040Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block040Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block040Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block040Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block040Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block040Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block040Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block040Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block040Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block040Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block040Mid : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block040Part010
    + surrogateDiagTailX0RatChunk000Sub000Block040Part011
    + surrogateDiagTailX0RatChunk000Sub000Block040Part012
    + surrogateDiagTailX0RatChunk000Sub000Block040Part013
    + surrogateDiagTailX0RatChunk000Sub000Block040Part014
    + surrogateDiagTailX0RatChunk000Sub000Block040Part015
    + surrogateDiagTailX0RatChunk000Sub000Block040Part016
    + surrogateDiagTailX0RatChunk000Sub000Block040Part017
    + surrogateDiagTailX0RatChunk000Sub000Block040Part018
    + surrogateDiagTailX0RatChunk000Sub000Block040Part019

def surrogateDiagonalTailChunk000Sub000Block040TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block040Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block040Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block040Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block040Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block040Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block040Tail : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block040Part020
    + surrogateDiagTailX0RatChunk000Sub000Block040Part021
    + surrogateDiagTailX0RatChunk000Sub000Block040Part022
    + surrogateDiagTailX0RatChunk000Sub000Block040Part023
    + surrogateDiagTailX0RatChunk000Sub000Block040Part024

def surrogateDiagonalTailChunk000Sub000Block040Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub000Block040HeadSum X0
    + surrogateDiagonalTailChunk000Sub000Block040MidSum X0
    + surrogateDiagonalTailChunk000Sub000Block040TailSum X0

def surrogateDiagTailX0RatChunk000Sub000Block040 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block040Part000
    + surrogateDiagTailX0RatChunk000Sub000Block040Part001
    + surrogateDiagTailX0RatChunk000Sub000Block040Part002
    + surrogateDiagTailX0RatChunk000Sub000Block040Part003
    + surrogateDiagTailX0RatChunk000Sub000Block040Part004
    + surrogateDiagTailX0RatChunk000Sub000Block040Part005
    + surrogateDiagTailX0RatChunk000Sub000Block040Part006
    + surrogateDiagTailX0RatChunk000Sub000Block040Part007
    + surrogateDiagTailX0RatChunk000Sub000Block040Part008
    + surrogateDiagTailX0RatChunk000Sub000Block040Part009
    + surrogateDiagTailX0RatChunk000Sub000Block040Part010
    + surrogateDiagTailX0RatChunk000Sub000Block040Part011
    + surrogateDiagTailX0RatChunk000Sub000Block040Part012
    + surrogateDiagTailX0RatChunk000Sub000Block040Part013
    + surrogateDiagTailX0RatChunk000Sub000Block040Part014
    + surrogateDiagTailX0RatChunk000Sub000Block040Part015
    + surrogateDiagTailX0RatChunk000Sub000Block040Part016
    + surrogateDiagTailX0RatChunk000Sub000Block040Part017
    + surrogateDiagTailX0RatChunk000Sub000Block040Part018
    + surrogateDiagTailX0RatChunk000Sub000Block040Part019
    + surrogateDiagTailX0RatChunk000Sub000Block040Part020
    + surrogateDiagTailX0RatChunk000Sub000Block040Part021
    + surrogateDiagTailX0RatChunk000Sub000Block040Part022
    + surrogateDiagTailX0RatChunk000Sub000Block040Part023
    + surrogateDiagTailX0RatChunk000Sub000Block040Part024

theorem surrogateDiagTailX0RatChunk000Sub000Block040_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk000Sub000Block040Head + surrogateDiagTailX0RatChunk000Sub000Block040Mid + surrogateDiagTailX0RatChunk000Sub000Block040Tail =
      surrogateDiagTailX0RatChunk000Sub000Block040 := by
  unfold surrogateDiagTailX0RatChunk000Sub000Block040Head surrogateDiagTailX0RatChunk000Sub000Block040Mid surrogateDiagTailX0RatChunk000Sub000Block040Tail surrogateDiagTailX0RatChunk000Sub000Block040
  ring

def SurrogateDiagonalTailChunk000Sub000Block040HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block040HeadSum X0 = surrogateDiagTailX0RatChunk000Sub000Block040Head

def SurrogateDiagonalTailChunk000Sub000Block040MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block040MidSum X0 = surrogateDiagTailX0RatChunk000Sub000Block040Mid

def SurrogateDiagonalTailChunk000Sub000Block040TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block040TailSum X0 = surrogateDiagTailX0RatChunk000Sub000Block040Tail

theorem surrogateDiagonalTailChunk000Sub000Block040_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk000Sub000Block040HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk000Sub000Block040MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk000Sub000Block040TailCertificateAt X0) :
    surrogateDiagonalTailChunk000Sub000Block040Sum X0 = surrogateDiagTailX0RatChunk000Sub000Block040 := by
  unfold SurrogateDiagonalTailChunk000Sub000Block040HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk000Sub000Block040MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk000Sub000Block040TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk000Sub000Block040Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk000Sub000Block040_eq_head_add_mid_add_tail

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

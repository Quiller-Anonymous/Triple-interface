import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0TailPilot25

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

open scoped BigOperators

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

/- Generated direct-term certificate blocks for tail chunk 000, subchunk 000, blocks [38,39). -/

/- Block 038 covers tail-support indices [950,975) and q from 1607 to 1646. -/

def TailChunk000Sub000Block038Part000SupportExplicit : Finset ℕ :=
  ([1607] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block038Part000 : ℚ :=
  (161338501275 : ℚ) / 5544824029470616

def SurrogateDiagonalTailChunk000Sub000Block038Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1607
    = surrogateDiagTailX0RatChunk000Sub000Block038Part000

theorem surrogateDiagonalTailChunk000Sub000Block038Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block038Part000CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block038Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block038Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block038Part000CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block038Part000SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block038Part000] using hcert

def TailChunk000Sub000Block038Part001SupportExplicit : Finset ℕ :=
  ([1609] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block038Part001 : ℚ :=
  (53913446825 : ℚ) / 1857498736822272

def SurrogateDiagonalTailChunk000Sub000Block038Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1609
    = surrogateDiagTailX0RatChunk000Sub000Block038Part001

theorem surrogateDiagonalTailChunk000Sub000Block038Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block038Part001CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block038Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block038Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block038Part001CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block038Part001SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block038Part001] using hcert

def TailChunk000Sub000Block038Part002SupportExplicit : Finset ℕ :=
  ([1610] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block038Part002 : ℚ :=
  (20231906075 : ℚ) / 24292519612416

def SurrogateDiagonalTailChunk000Sub000Block038Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1610
    = surrogateDiagTailX0RatChunk000Sub000Block038Part002

theorem surrogateDiagonalTailChunk000Sub000Block038Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block038Part002CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block038Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block038Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block038Part002CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block038Part002SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block038Part002] using hcert

def TailChunk000Sub000Block038Part003SupportExplicit : Finset ℕ :=
  ([1613] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block038Part003 : ℚ :=
  (325025992325 : ℚ) / 8442226757649984

def SurrogateDiagonalTailChunk000Sub000Block038Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1613
    = surrogateDiagTailX0RatChunk000Sub000Block038Part003

theorem surrogateDiagonalTailChunk000Sub000Block038Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block038Part003CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block038Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block038Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block038Part003CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block038Part003SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block038Part003] using hcert

def TailChunk000Sub000Block038Part004SupportExplicit : Finset ℕ :=
  ([1614] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block038Part004 : ℚ :=
  (83374125575 : ℚ) / 103194374267904

def SurrogateDiagonalTailChunk000Sub000Block038Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1614
    = surrogateDiagTailX0RatChunk000Sub000Block038Part004

theorem surrogateDiagonalTailChunk000Sub000Block038Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block038Part004CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block038Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block038Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block038Part004CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block038Part004SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block038Part004] using hcert

def TailChunk000Sub000Block038Part005SupportExplicit : Finset ℕ :=
  ([1615] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block038Part005 : ℚ :=
  (118394495725 : ℚ) / 1467964389851136

def SurrogateDiagonalTailChunk000Sub000Block038Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1615
    = surrogateDiagTailX0RatChunk000Sub000Block038Part005

theorem surrogateDiagonalTailChunk000Sub000Block038Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block038Part005CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block038Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block038Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block038Part005CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block038Part005SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block038Part005] using hcert

def TailChunk000Sub000Block038Part006SupportExplicit : Finset ℕ :=
  ([1618] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block038Part006 : ℚ :=
  (81728314875 : ℚ) / 355263873980416

def SurrogateDiagonalTailChunk000Sub000Block038Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1618
    = surrogateDiagTailX0RatChunk000Sub000Block038Part006

theorem surrogateDiagonalTailChunk000Sub000Block038Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block038Part006CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block038Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block038Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block038Part006CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block038Part006SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block038Part006] using hcert

def TailChunk000Sub000Block038Part007SupportExplicit : Finset ℕ :=
  ([1619] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block038Part007 : ℚ :=
  (163757033475 : ℚ) / 5712413979158296

def SurrogateDiagonalTailChunk000Sub000Block038Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1619
    = surrogateDiagTailX0RatChunk000Sub000Block038Part007

theorem surrogateDiagonalTailChunk000Sub000Block038Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block038Part007CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block038Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block038Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block038Part007CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block038Part007SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block038Part007] using hcert

def TailChunk000Sub000Block038Part008SupportExplicit : Finset ℕ :=
  ([1621] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block038Part008 : ℚ :=
  (2188824953 : ℚ) / 76542809500800

def SurrogateDiagonalTailChunk000Sub000Block038Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1621
    = surrogateDiagTailX0RatChunk000Sub000Block038Part008

theorem surrogateDiagonalTailChunk000Sub000Block038Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block038Part008CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block038Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block038Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block038Part008CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block038Part008SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block038Part008] using hcert

def TailChunk000Sub000Block038Part009SupportExplicit : Finset ℕ :=
  ([1622] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block038Part009 : ℚ :=
  (24335677 : ℚ) / 106309457640

def SurrogateDiagonalTailChunk000Sub000Block038Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1622
    = surrogateDiagTailX0RatChunk000Sub000Block038Part009

theorem surrogateDiagonalTailChunk000Sub000Block038Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block038Part009CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block038Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block038Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block038Part009CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block038Part009SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block038Part009] using hcert

def TailChunk000Sub000Block038Part010SupportExplicit : Finset ℕ :=
  ([1623] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block038Part010 : ℚ :=
  (54779 : ℚ) / 566870400

def SurrogateDiagonalTailChunk000Sub000Block038Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1623
    = surrogateDiagTailX0RatChunk000Sub000Block038Part010

theorem surrogateDiagonalTailChunk000Sub000Block038Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block038Part010CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block038Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block038Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block038Part010CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block038Part010SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block038Part010] using hcert

def TailChunk000Sub000Block038Part011SupportExplicit : Finset ℕ :=
  ([1626] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block038Part011 : ℚ :=
  (439061 : ℚ) / 566870400

def SurrogateDiagonalTailChunk000Sub000Block038Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1626
    = surrogateDiagTailX0RatChunk000Sub000Block038Part011

theorem surrogateDiagonalTailChunk000Sub000Block038Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block038Part011CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block038Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block038Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block038Part011CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block038Part011SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block038Part011] using hcert

def TailChunk000Sub000Block038Part012SupportExplicit : Finset ℕ :=
  ([1627] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block038Part012 : ℚ :=
  (55126461425 : ℚ) / 1942077310954632

def SurrogateDiagonalTailChunk000Sub000Block038Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1627
    = surrogateDiagTailX0RatChunk000Sub000Block038Part012

theorem surrogateDiagonalTailChunk000Sub000Block038Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block038Part012CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block038Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block038Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block038Part012CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block038Part012SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block038Part012] using hcert

def TailChunk000Sub000Block038Part013SupportExplicit : Finset ℕ :=
  ([1630] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block038Part013 : ℚ :=
  (199753281625 : ℚ) / 440886582724608

def SurrogateDiagonalTailChunk000Sub000Block038Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1630
    = surrogateDiagTailX0RatChunk000Sub000Block038Part013

theorem surrogateDiagonalTailChunk000Sub000Block038Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block038Part013CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block038Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block038Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block038Part013CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block038Part013SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block038Part013] using hcert

def TailChunk000Sub000Block038Part014SupportExplicit : Finset ℕ :=
  ([1631] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block038Part014 : ℚ :=
  (214589828825 : ℚ) / 4694115856564224

def SurrogateDiagonalTailChunk000Sub000Block038Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1631
    = surrogateDiagTailX0RatChunk000Sub000Block038Part014

theorem surrogateDiagonalTailChunk000Sub000Block038Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block038Part014CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block038Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block038Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block038Part014CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block038Part014SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block038Part014] using hcert

def TailChunk000Sub000Block038Part015SupportExplicit : Finset ℕ :=
  ([1633] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block038Part015 : ℚ :=
  (1180141021 : ℚ) / 35160071608200

def SurrogateDiagonalTailChunk000Sub000Block038Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1633
    = surrogateDiagTailX0RatChunk000Sub000Block038Part015

theorem surrogateDiagonalTailChunk000Sub000Block038Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block038Part015CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block038Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block038Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block038Part015CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block038Part015SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block038Part015] using hcert

def TailChunk000Sub000Block038Part016SupportExplicit : Finset ℕ :=
  ([1634] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block038Part016 : ℚ :=
  (133847646875 : ℚ) / 408398412469824

def SurrogateDiagonalTailChunk000Sub000Block038Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1634
    = surrogateDiagTailX0RatChunk000Sub000Block038Part016

theorem surrogateDiagonalTailChunk000Sub000Block038Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block038Part016CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block038Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block038Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block038Part016CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block038Part016SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block038Part016] using hcert

def TailChunk000Sub000Block038Part017SupportExplicit : Finset ℕ :=
  ([1635] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block038Part017 : ℚ :=
  (16606219675 : ℚ) / 87088707698688

def SurrogateDiagonalTailChunk000Sub000Block038Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1635
    = surrogateDiagTailX0RatChunk000Sub000Block038Part017

theorem surrogateDiagonalTailChunk000Sub000Block038Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block038Part017CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block038Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block038Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block038Part017CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block038Part017SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block038Part017] using hcert

def TailChunk000Sub000Block038Part018SupportExplicit : Finset ℕ :=
  ([1637] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block038Part018 : ℚ :=
  (167418568275 : ℚ) / 5970886303486336

def SurrogateDiagonalTailChunk000Sub000Block038Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1637
    = surrogateDiagTailX0RatChunk000Sub000Block038Part018

theorem surrogateDiagonalTailChunk000Sub000Block038Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block038Part018CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block038Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block038Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block038Part018CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block038Part018SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block038Part018] using hcert

def TailChunk000Sub000Block038Part019SupportExplicit : Finset ℕ :=
  ([1639] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block038Part019 : ℚ :=
  (1216899051 : ℚ) / 31992078202880

def SurrogateDiagonalTailChunk000Sub000Block038Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1639
    = surrogateDiagTailX0RatChunk000Sub000Block038Part019

theorem surrogateDiagonalTailChunk000Sub000Block038Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block038Part019CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block038Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block038Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block038Part019CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block038Part019SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block038Part019] using hcert

def TailChunk000Sub000Block038Part020SupportExplicit : Finset ℕ :=
  ([1641] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block038Part020 : ℚ :=
  (430775 : ℚ) / 4557597408

def SurrogateDiagonalTailChunk000Sub000Block038Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1641
    = surrogateDiagTailX0RatChunk000Sub000Block038Part020

theorem surrogateDiagonalTailChunk000Sub000Block038Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block038Part020CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block038Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block038Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block038Part020CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block038Part020SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block038Part020] using hcert

def TailChunk000Sub000Block038Part021SupportExplicit : Finset ℕ :=
  ([1642] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block038Part021 : ℚ :=
  (673366959 : ℚ) / 3014747895680

def SurrogateDiagonalTailChunk000Sub000Block038Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1642
    = surrogateDiagTailX0RatChunk000Sub000Block038Part021

theorem surrogateDiagonalTailChunk000Sub000Block038Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block038Part021CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block038Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block038Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block038Part021CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block038Part021SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block038Part021] using hcert

def TailChunk000Sub000Block038Part022SupportExplicit : Finset ℕ :=
  ([1643] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block038Part022 : ℚ :=
  (128300891 : ℚ) / 3949062294528

def SurrogateDiagonalTailChunk000Sub000Block038Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1643
    = surrogateDiagTailX0RatChunk000Sub000Block038Part022

theorem surrogateDiagonalTailChunk000Sub000Block038Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block038Part022CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block038Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block038Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block038Part022CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block038Part022SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block038Part022] using hcert

def TailChunk000Sub000Block038Part023SupportExplicit : Finset ℕ :=
  ([1645] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block038Part023 : ℚ :=
  (170408937875 : ℚ) / 1857261930430464

def SurrogateDiagonalTailChunk000Sub000Block038Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1645
    = surrogateDiagTailX0RatChunk000Sub000Block038Part023

theorem surrogateDiagonalTailChunk000Sub000Block038Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block038Part023CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block038Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block038Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block038Part023CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block038Part023SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block038Part023] using hcert

def TailChunk000Sub000Block038Part024SupportExplicit : Finset ℕ :=
  ([1646] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block038Part024 : ℚ :=
  (3132646625 : ℚ) / 14093832642888

def SurrogateDiagonalTailChunk000Sub000Block038Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1646
    = surrogateDiagTailX0RatChunk000Sub000Block038Part024

theorem surrogateDiagonalTailChunk000Sub000Block038Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block038Part024CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block038Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block038Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block038Part024CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block038Part024SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block038Part024] using hcert

def surrogateDiagonalTailChunk000Sub000Block038HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block038Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block038Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block038Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block038Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block038Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block038Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block038Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block038Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block038Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block038Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block038Head : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block038Part000
    + surrogateDiagTailX0RatChunk000Sub000Block038Part001
    + surrogateDiagTailX0RatChunk000Sub000Block038Part002
    + surrogateDiagTailX0RatChunk000Sub000Block038Part003
    + surrogateDiagTailX0RatChunk000Sub000Block038Part004
    + surrogateDiagTailX0RatChunk000Sub000Block038Part005
    + surrogateDiagTailX0RatChunk000Sub000Block038Part006
    + surrogateDiagTailX0RatChunk000Sub000Block038Part007
    + surrogateDiagTailX0RatChunk000Sub000Block038Part008
    + surrogateDiagTailX0RatChunk000Sub000Block038Part009

def surrogateDiagonalTailChunk000Sub000Block038MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block038Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block038Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block038Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block038Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block038Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block038Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block038Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block038Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block038Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block038Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block038Mid : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block038Part010
    + surrogateDiagTailX0RatChunk000Sub000Block038Part011
    + surrogateDiagTailX0RatChunk000Sub000Block038Part012
    + surrogateDiagTailX0RatChunk000Sub000Block038Part013
    + surrogateDiagTailX0RatChunk000Sub000Block038Part014
    + surrogateDiagTailX0RatChunk000Sub000Block038Part015
    + surrogateDiagTailX0RatChunk000Sub000Block038Part016
    + surrogateDiagTailX0RatChunk000Sub000Block038Part017
    + surrogateDiagTailX0RatChunk000Sub000Block038Part018
    + surrogateDiagTailX0RatChunk000Sub000Block038Part019

def surrogateDiagonalTailChunk000Sub000Block038TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block038Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block038Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block038Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block038Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block038Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block038Tail : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block038Part020
    + surrogateDiagTailX0RatChunk000Sub000Block038Part021
    + surrogateDiagTailX0RatChunk000Sub000Block038Part022
    + surrogateDiagTailX0RatChunk000Sub000Block038Part023
    + surrogateDiagTailX0RatChunk000Sub000Block038Part024

def surrogateDiagonalTailChunk000Sub000Block038Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub000Block038HeadSum X0
    + surrogateDiagonalTailChunk000Sub000Block038MidSum X0
    + surrogateDiagonalTailChunk000Sub000Block038TailSum X0

def surrogateDiagTailX0RatChunk000Sub000Block038 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block038Part000
    + surrogateDiagTailX0RatChunk000Sub000Block038Part001
    + surrogateDiagTailX0RatChunk000Sub000Block038Part002
    + surrogateDiagTailX0RatChunk000Sub000Block038Part003
    + surrogateDiagTailX0RatChunk000Sub000Block038Part004
    + surrogateDiagTailX0RatChunk000Sub000Block038Part005
    + surrogateDiagTailX0RatChunk000Sub000Block038Part006
    + surrogateDiagTailX0RatChunk000Sub000Block038Part007
    + surrogateDiagTailX0RatChunk000Sub000Block038Part008
    + surrogateDiagTailX0RatChunk000Sub000Block038Part009
    + surrogateDiagTailX0RatChunk000Sub000Block038Part010
    + surrogateDiagTailX0RatChunk000Sub000Block038Part011
    + surrogateDiagTailX0RatChunk000Sub000Block038Part012
    + surrogateDiagTailX0RatChunk000Sub000Block038Part013
    + surrogateDiagTailX0RatChunk000Sub000Block038Part014
    + surrogateDiagTailX0RatChunk000Sub000Block038Part015
    + surrogateDiagTailX0RatChunk000Sub000Block038Part016
    + surrogateDiagTailX0RatChunk000Sub000Block038Part017
    + surrogateDiagTailX0RatChunk000Sub000Block038Part018
    + surrogateDiagTailX0RatChunk000Sub000Block038Part019
    + surrogateDiagTailX0RatChunk000Sub000Block038Part020
    + surrogateDiagTailX0RatChunk000Sub000Block038Part021
    + surrogateDiagTailX0RatChunk000Sub000Block038Part022
    + surrogateDiagTailX0RatChunk000Sub000Block038Part023
    + surrogateDiagTailX0RatChunk000Sub000Block038Part024

theorem surrogateDiagTailX0RatChunk000Sub000Block038_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk000Sub000Block038Head + surrogateDiagTailX0RatChunk000Sub000Block038Mid + surrogateDiagTailX0RatChunk000Sub000Block038Tail =
      surrogateDiagTailX0RatChunk000Sub000Block038 := by
  unfold surrogateDiagTailX0RatChunk000Sub000Block038Head surrogateDiagTailX0RatChunk000Sub000Block038Mid surrogateDiagTailX0RatChunk000Sub000Block038Tail surrogateDiagTailX0RatChunk000Sub000Block038
  ring

def SurrogateDiagonalTailChunk000Sub000Block038HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block038HeadSum X0 = surrogateDiagTailX0RatChunk000Sub000Block038Head

def SurrogateDiagonalTailChunk000Sub000Block038MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block038MidSum X0 = surrogateDiagTailX0RatChunk000Sub000Block038Mid

def SurrogateDiagonalTailChunk000Sub000Block038TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block038TailSum X0 = surrogateDiagTailX0RatChunk000Sub000Block038Tail

theorem surrogateDiagonalTailChunk000Sub000Block038_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk000Sub000Block038HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk000Sub000Block038MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk000Sub000Block038TailCertificateAt X0) :
    surrogateDiagonalTailChunk000Sub000Block038Sum X0 = surrogateDiagTailX0RatChunk000Sub000Block038 := by
  unfold SurrogateDiagonalTailChunk000Sub000Block038HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk000Sub000Block038MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk000Sub000Block038TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk000Sub000Block038Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk000Sub000Block038_eq_head_add_mid_add_tail

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

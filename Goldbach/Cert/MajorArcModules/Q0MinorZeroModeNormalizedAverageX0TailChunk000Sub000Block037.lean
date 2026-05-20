import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0TailPilot25

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

open scoped BigOperators

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

/- Generated direct-term certificate blocks for tail chunk 000, subchunk 000, blocks [37,38). -/

/- Block 037 covers tail-support indices [925,950) and q from 1567 to 1606. -/

def TailChunk000Sub000Block037Part000SupportExplicit : Finset ℕ :=
  ([1567] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block037Part000 : ℚ :=
  (51135558425 : ℚ) / 1670903544646152

def SurrogateDiagonalTailChunk000Sub000Block037Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1567
    = surrogateDiagTailX0RatChunk000Sub000Block037Part000

theorem surrogateDiagonalTailChunk000Sub000Block037Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block037Part000CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block037Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block037Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block037Part000CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block037Part000SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block037Part000] using hcert

def TailChunk000Sub000Block037Part001SupportExplicit : Finset ℕ :=
  ([1569] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block037Part001 : ℚ :=
  (5119475 : ℚ) / 49498353504

def SurrogateDiagonalTailChunk000Sub000Block037Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1569
    = surrogateDiagTailX0RatChunk000Sub000Block037Part001

theorem surrogateDiagonalTailChunk000Sub000Block037Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block037Part001CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block037Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block037Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block037Part001CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block037Part001SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block037Part001] using hcert

def TailChunk000Sub000Block037Part002SupportExplicit : Finset ℕ :=
  ([1570] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block037Part002 : ℚ :=
  (209658635275 : ℚ) / 379109980274688

def SurrogateDiagonalTailChunk000Sub000Block037Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1570
    = surrogateDiagTailX0RatChunk000Sub000Block037Part002

theorem surrogateDiagonalTailChunk000Sub000Block037Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block037Part002CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block037Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block037Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block037Part002CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block037Part002SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block037Part002] using hcert

def TailChunk000Sub000Block037Part003SupportExplicit : Finset ℕ :=
  ([1571] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block037Part003 : ℚ :=
  (6167634459 : ℚ) / 202564905213400

def SurrogateDiagonalTailChunk000Sub000Block037Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1571
    = surrogateDiagTailX0RatChunk000Sub000Block037Part003

theorem surrogateDiagonalTailChunk000Sub000Block037Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block037Part003CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block037Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block037Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block037Part003CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block037Part003SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block037Part003] using hcert

def TailChunk000Sub000Block037Part004SupportExplicit : Finset ℕ :=
  ([1574] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block037Part004 : ℚ :=
  (2864581625 : ℚ) / 11782352839368

def SurrogateDiagonalTailChunk000Sub000Block037Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1574
    = surrogateDiagTailX0RatChunk000Sub000Block037Part004

theorem surrogateDiagonalTailChunk000Sub000Block037Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block037Part004CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block037Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block037Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block037Part004CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block037Part004SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block037Part004] using hcert

def TailChunk000Sub000Block037Part005SupportExplicit : Finset ℕ :=
  ([1577] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block037Part005 : ℚ :=
  (219040830575 : ℚ) / 5933928283066944

def SurrogateDiagonalTailChunk000Sub000Block037Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1577
    = surrogateDiagTailX0RatChunk000Sub000Block037Part005

theorem surrogateDiagonalTailChunk000Sub000Block037Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block037Part005CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block037Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block037Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block037Part005CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block037Part005SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block037Part005] using hcert

def TailChunk000Sub000Block037Part006SupportExplicit : Finset ℕ :=
  ([1578] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block037Part006 : ℚ :=
  (172263613075 : ℚ) / 188517645429888

def SurrogateDiagonalTailChunk000Sub000Block037Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1578
    = surrogateDiagTailX0RatChunk000Sub000Block037Part006

theorem surrogateDiagonalTailChunk000Sub000Block037Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block037Part006CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block037Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block037Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block037Part006CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block037Part006SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block037Part006] using hcert

def TailChunk000Sub000Block037Part007SupportExplicit : Finset ℕ :=
  ([1579] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block037Part007 : ℚ :=
  (51921743825 : ℚ) / 1722710675200392

def SurrogateDiagonalTailChunk000Sub000Block037Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1579
    = surrogateDiagTailX0RatChunk000Sub000Block037Part007

theorem surrogateDiagonalTailChunk000Sub000Block037Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block037Part007CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block037Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block037Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block037Part007CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block037Part007SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block037Part007] using hcert

def TailChunk000Sub000Block037Part008SupportExplicit : Finset ℕ :=
  ([1581] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block037Part008 : ℚ :=
  (801145487 : ℚ) / 5663442862080

def SurrogateDiagonalTailChunk000Sub000Block037Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1581
    = surrogateDiagTailX0RatChunk000Sub000Block037Part008

theorem surrogateDiagonalTailChunk000Sub000Block037Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block037Part008CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block037Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block037Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block037Part008CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block037Part008SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block037Part008] using hcert

def TailChunk000Sub000Block037Part009SupportExplicit : Finset ℕ :=
  ([1582] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block037Part009 : ℚ :=
  (800862875 : ℚ) / 2023500939264

def SurrogateDiagonalTailChunk000Sub000Block037Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1582
    = surrogateDiagTailX0RatChunk000Sub000Block037Part009

theorem surrogateDiagonalTailChunk000Sub000Block037Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block037Part009CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block037Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block037Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block037Part009CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block037Part009SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block037Part009] using hcert

def TailChunk000Sub000Block037Part010SupportExplicit : Finset ℕ :=
  ([1583] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block037Part010 : ℚ :=
  (313048183325 : ℚ) / 7831100182075044

def SurrogateDiagonalTailChunk000Sub000Block037Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1583
    = surrogateDiagTailX0RatChunk000Sub000Block037Part010

theorem surrogateDiagonalTailChunk000Sub000Block037Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block037Part010CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block037Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block037Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block037Part010CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block037Part010SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block037Part010] using hcert

def TailChunk000Sub000Block037Part011SupportExplicit : Finset ℕ :=
  ([1585] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block037Part011 : ℚ :=
  (127341096375 : ℚ) / 2127619195764736

def SurrogateDiagonalTailChunk000Sub000Block037Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1585
    = surrogateDiagTailX0RatChunk000Sub000Block037Part011

theorem surrogateDiagonalTailChunk000Sub000Block037Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block037Part011CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block037Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block037Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block037Part011CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block037Part011SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block037Part011] using hcert

def TailChunk000Sub000Block037Part012SupportExplicit : Finset ℕ :=
  ([1586] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block037Part012 : ℚ :=
  (4304740403 : ℚ) / 13439615385600

def SurrogateDiagonalTailChunk000Sub000Block037Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1586
    = surrogateDiagTailX0RatChunk000Sub000Block037Part012

theorem surrogateDiagonalTailChunk000Sub000Block037Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block037Part012CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block037Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block037Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block037Part012CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block037Part012SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block037Part012] using hcert

def TailChunk000Sub000Block037Part013SupportExplicit : Finset ℕ :=
  ([1589] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block037Part013 : ℚ :=
  (203681539625 : ℚ) / 4227032834639424

def SurrogateDiagonalTailChunk000Sub000Block037Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1589
    = surrogateDiagTailX0RatChunk000Sub000Block037Part013

theorem surrogateDiagonalTailChunk000Sub000Block037Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block037Part013CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block037Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block037Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block037Part013CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block037Part013SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block037Part013] using hcert

def TailChunk000Sub000Block037Part014SupportExplicit : Finset ℕ :=
  ([1590] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block037Part014 : ℚ :=
  (136153948825 : ℚ) / 74885922029568

def SurrogateDiagonalTailChunk000Sub000Block037Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1590
    = surrogateDiagTailX0RatChunk000Sub000Block037Part014

theorem surrogateDiagonalTailChunk000Sub000Block037Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block037Part014CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block037Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block037Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block037Part014CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block037Part014SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block037Part014] using hcert

def TailChunk000Sub000Block037Part015SupportExplicit : Finset ℕ :=
  ([1591] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block037Part015 : ℚ :=
  (1395985025 : ℚ) / 40335645676032

def SurrogateDiagonalTailChunk000Sub000Block037Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1591
    = surrogateDiagTailX0RatChunk000Sub000Block037Part015

theorem surrogateDiagonalTailChunk000Sub000Block037Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block037Part015CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block037Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block037Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block037Part015CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block037Part015SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block037Part015] using hcert

def TailChunk000Sub000Block037Part016SupportExplicit : Finset ℕ :=
  ([1594] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block037Part016 : ℚ :=
  (79321723875 : ℚ) / 334624607752576

def SurrogateDiagonalTailChunk000Sub000Block037Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1594
    = surrogateDiagTailX0RatChunk000Sub000Block037Part016

theorem surrogateDiagonalTailChunk000Sub000Block037Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block037Part016CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block037Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block037Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block037Part016CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block037Part016SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block037Part016] using hcert

def TailChunk000Sub000Block037Part017SupportExplicit : Finset ℕ :=
  ([1595] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block037Part017 : ℚ :=
  (2731909169 : ℚ) / 31476681277440

def SurrogateDiagonalTailChunk000Sub000Block037Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1595
    = surrogateDiagTailX0RatChunk000Sub000Block037Part017

theorem surrogateDiagonalTailChunk000Sub000Block037Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block037Part017CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block037Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block037Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block037Part017CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block037Part017SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block037Part017] using hcert

def TailChunk000Sub000Block037Part018SupportExplicit : Finset ℕ :=
  ([1597] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block037Part018 : ℚ :=
  (1083923825 : ℚ) / 36789155399808

def SurrogateDiagonalTailChunk000Sub000Block037Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1597
    = surrogateDiagTailX0RatChunk000Sub000Block037Part018

theorem surrogateDiagonalTailChunk000Sub000Block037Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block037Part018CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block037Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block037Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block037Part018CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block037Part018SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block037Part018] using hcert

def TailChunk000Sub000Block037Part019SupportExplicit : Finset ℕ :=
  ([1598] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block037Part019 : ℚ :=
  (63752757625 : ℚ) / 183433277079552

def SurrogateDiagonalTailChunk000Sub000Block037Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1598
    = surrogateDiagTailX0RatChunk000Sub000Block037Part019

theorem surrogateDiagonalTailChunk000Sub000Block037Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block037Part019CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block037Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block037Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block037Part019CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block037Part019SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block037Part019] using hcert

def TailChunk000Sub000Block037Part020SupportExplicit : Finset ℕ :=
  ([1599] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block037Part020 : ℚ :=
  (2889797341 : ℚ) / 21237910732800

def SurrogateDiagonalTailChunk000Sub000Block037Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1599
    = surrogateDiagTailX0RatChunk000Sub000Block037Part020

theorem surrogateDiagonalTailChunk000Sub000Block037Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block037Part020CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block037Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block037Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block037Part020CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block037Part020SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block037Part020] using hcert

def TailChunk000Sub000Block037Part021SupportExplicit : Finset ℕ :=
  ([1601] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block037Part021 : ℚ :=
  (6405439299 : ℚ) / 218497024000000

def SurrogateDiagonalTailChunk000Sub000Block037Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1601
    = surrogateDiagTailX0RatChunk000Sub000Block037Part021

theorem surrogateDiagonalTailChunk000Sub000Block037Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block037Part021CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block037Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block037Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block037Part021CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block037Part021SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block037Part021] using hcert

def TailChunk000Sub000Block037Part022SupportExplicit : Finset ℕ :=
  ([1603] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block037Part022 : ℚ :=
  (29349125075 : ℚ) / 486517810185216

def SurrogateDiagonalTailChunk000Sub000Block037Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1603
    = surrogateDiagTailX0RatChunk000Sub000Block037Part022

theorem surrogateDiagonalTailChunk000Sub000Block037Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block037Part022CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block037Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block037Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block037Part022CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block037Part022SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block037Part022] using hcert

def TailChunk000Sub000Block037Part023SupportExplicit : Finset ℕ :=
  ([1605] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block037Part023 : ℚ :=
  (32356275575 : ℚ) / 161629370290176

def SurrogateDiagonalTailChunk000Sub000Block037Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1605
    = surrogateDiagTailX0RatChunk000Sub000Block037Part023

theorem surrogateDiagonalTailChunk000Sub000Block037Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block037Part023CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block037Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block037Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block037Part023CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block037Part023SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block037Part023] using hcert

def TailChunk000Sub000Block037Part024SupportExplicit : Finset ℕ :=
  ([1606] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block037Part024 : ℚ :=
  (1450784891 : ℚ) / 4479871795200

def SurrogateDiagonalTailChunk000Sub000Block037Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1606
    = surrogateDiagTailX0RatChunk000Sub000Block037Part024

theorem surrogateDiagonalTailChunk000Sub000Block037Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block037Part024CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block037Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block037Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block037Part024CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block037Part024SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block037Part024] using hcert

def surrogateDiagonalTailChunk000Sub000Block037HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block037Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block037Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block037Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block037Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block037Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block037Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block037Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block037Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block037Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block037Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block037Head : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block037Part000
    + surrogateDiagTailX0RatChunk000Sub000Block037Part001
    + surrogateDiagTailX0RatChunk000Sub000Block037Part002
    + surrogateDiagTailX0RatChunk000Sub000Block037Part003
    + surrogateDiagTailX0RatChunk000Sub000Block037Part004
    + surrogateDiagTailX0RatChunk000Sub000Block037Part005
    + surrogateDiagTailX0RatChunk000Sub000Block037Part006
    + surrogateDiagTailX0RatChunk000Sub000Block037Part007
    + surrogateDiagTailX0RatChunk000Sub000Block037Part008
    + surrogateDiagTailX0RatChunk000Sub000Block037Part009

def surrogateDiagonalTailChunk000Sub000Block037MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block037Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block037Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block037Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block037Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block037Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block037Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block037Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block037Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block037Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block037Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block037Mid : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block037Part010
    + surrogateDiagTailX0RatChunk000Sub000Block037Part011
    + surrogateDiagTailX0RatChunk000Sub000Block037Part012
    + surrogateDiagTailX0RatChunk000Sub000Block037Part013
    + surrogateDiagTailX0RatChunk000Sub000Block037Part014
    + surrogateDiagTailX0RatChunk000Sub000Block037Part015
    + surrogateDiagTailX0RatChunk000Sub000Block037Part016
    + surrogateDiagTailX0RatChunk000Sub000Block037Part017
    + surrogateDiagTailX0RatChunk000Sub000Block037Part018
    + surrogateDiagTailX0RatChunk000Sub000Block037Part019

def surrogateDiagonalTailChunk000Sub000Block037TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block037Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block037Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block037Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block037Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block037Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block037Tail : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block037Part020
    + surrogateDiagTailX0RatChunk000Sub000Block037Part021
    + surrogateDiagTailX0RatChunk000Sub000Block037Part022
    + surrogateDiagTailX0RatChunk000Sub000Block037Part023
    + surrogateDiagTailX0RatChunk000Sub000Block037Part024

def surrogateDiagonalTailChunk000Sub000Block037Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub000Block037HeadSum X0
    + surrogateDiagonalTailChunk000Sub000Block037MidSum X0
    + surrogateDiagonalTailChunk000Sub000Block037TailSum X0

def surrogateDiagTailX0RatChunk000Sub000Block037 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block037Part000
    + surrogateDiagTailX0RatChunk000Sub000Block037Part001
    + surrogateDiagTailX0RatChunk000Sub000Block037Part002
    + surrogateDiagTailX0RatChunk000Sub000Block037Part003
    + surrogateDiagTailX0RatChunk000Sub000Block037Part004
    + surrogateDiagTailX0RatChunk000Sub000Block037Part005
    + surrogateDiagTailX0RatChunk000Sub000Block037Part006
    + surrogateDiagTailX0RatChunk000Sub000Block037Part007
    + surrogateDiagTailX0RatChunk000Sub000Block037Part008
    + surrogateDiagTailX0RatChunk000Sub000Block037Part009
    + surrogateDiagTailX0RatChunk000Sub000Block037Part010
    + surrogateDiagTailX0RatChunk000Sub000Block037Part011
    + surrogateDiagTailX0RatChunk000Sub000Block037Part012
    + surrogateDiagTailX0RatChunk000Sub000Block037Part013
    + surrogateDiagTailX0RatChunk000Sub000Block037Part014
    + surrogateDiagTailX0RatChunk000Sub000Block037Part015
    + surrogateDiagTailX0RatChunk000Sub000Block037Part016
    + surrogateDiagTailX0RatChunk000Sub000Block037Part017
    + surrogateDiagTailX0RatChunk000Sub000Block037Part018
    + surrogateDiagTailX0RatChunk000Sub000Block037Part019
    + surrogateDiagTailX0RatChunk000Sub000Block037Part020
    + surrogateDiagTailX0RatChunk000Sub000Block037Part021
    + surrogateDiagTailX0RatChunk000Sub000Block037Part022
    + surrogateDiagTailX0RatChunk000Sub000Block037Part023
    + surrogateDiagTailX0RatChunk000Sub000Block037Part024

theorem surrogateDiagTailX0RatChunk000Sub000Block037_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk000Sub000Block037Head + surrogateDiagTailX0RatChunk000Sub000Block037Mid + surrogateDiagTailX0RatChunk000Sub000Block037Tail =
      surrogateDiagTailX0RatChunk000Sub000Block037 := by
  unfold surrogateDiagTailX0RatChunk000Sub000Block037Head surrogateDiagTailX0RatChunk000Sub000Block037Mid surrogateDiagTailX0RatChunk000Sub000Block037Tail surrogateDiagTailX0RatChunk000Sub000Block037
  ring

def SurrogateDiagonalTailChunk000Sub000Block037HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block037HeadSum X0 = surrogateDiagTailX0RatChunk000Sub000Block037Head

def SurrogateDiagonalTailChunk000Sub000Block037MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block037MidSum X0 = surrogateDiagTailX0RatChunk000Sub000Block037Mid

def SurrogateDiagonalTailChunk000Sub000Block037TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block037TailSum X0 = surrogateDiagTailX0RatChunk000Sub000Block037Tail

theorem surrogateDiagonalTailChunk000Sub000Block037_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk000Sub000Block037HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk000Sub000Block037MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk000Sub000Block037TailCertificateAt X0) :
    surrogateDiagonalTailChunk000Sub000Block037Sum X0 = surrogateDiagTailX0RatChunk000Sub000Block037 := by
  unfold SurrogateDiagonalTailChunk000Sub000Block037HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk000Sub000Block037MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk000Sub000Block037TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk000Sub000Block037Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk000Sub000Block037_eq_head_add_mid_add_tail

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

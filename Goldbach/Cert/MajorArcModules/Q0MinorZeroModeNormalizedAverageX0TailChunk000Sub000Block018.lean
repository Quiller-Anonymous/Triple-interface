import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0TailPilot25

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

open scoped BigOperators

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

/- Generated direct-term certificate blocks for tail chunk 000, subchunk 000, blocks [18,19). -/

/- Block 018 covers tail-support indices [450,475) and q from 790 to 827. -/

def TailChunk000Sub000Block018Part000SupportExplicit : Finset ℕ :=
  ([790] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block018Part000 : ℚ :=
  (99358946425 : ℚ) / 23694373767168

def SurrogateDiagonalTailChunk000Sub000Block018Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 790
    = surrogateDiagTailX0RatChunk000Sub000Block018Part000

theorem surrogateDiagonalTailChunk000Sub000Block018Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block018Part000CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block018Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block018Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block018Part000CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block018Part000SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block018Part000] using hcert

def TailChunk000Sub000Block018Part001SupportExplicit : Finset ℕ :=
  ([791] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block018Part001 : ℚ :=
  (800862875 : ℚ) / 2023500939264

def SurrogateDiagonalTailChunk000Sub000Block018Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 791
    = surrogateDiagTailX0RatChunk000Sub000Block018Part001

theorem surrogateDiagonalTailChunk000Sub000Block018Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block018Part001CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block018Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block018Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block018Part001CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block018Part001SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block018Part001] using hcert

def TailChunk000Sub000Block018Part002SupportExplicit : Finset ℕ :=
  ([793] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block018Part002 : ℚ :=
  (4304740403 : ℚ) / 13439615385600

def SurrogateDiagonalTailChunk000Sub000Block018Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 793
    = surrogateDiagTailX0RatChunk000Sub000Block018Part002

theorem surrogateDiagonalTailChunk000Sub000Block018Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block018Part002CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block018Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block018Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block018Part002CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block018Part002SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block018Part002] using hcert

def TailChunk000Sub000Block018Part003SupportExplicit : Finset ℕ :=
  ([794] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block018Part003 : ℚ :=
  (63874987475 : ℚ) / 30745220134464

def SurrogateDiagonalTailChunk000Sub000Block018Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 794
    = surrogateDiagTailX0RatChunk000Sub000Block018Part003

theorem surrogateDiagonalTailChunk000Sub000Block018Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block018Part003CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block018Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block018Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block018Part003CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block018Part003SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block018Part003] using hcert

def TailChunk000Sub000Block018Part004SupportExplicit : Finset ℕ :=
  ([795] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block018Part004 : ℚ :=
  (136153948825 : ℚ) / 74885922029568

def SurrogateDiagonalTailChunk000Sub000Block018Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 795
    = surrogateDiagTailX0RatChunk000Sub000Block018Part004

theorem surrogateDiagonalTailChunk000Sub000Block018Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block018Part004CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block018Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block018Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block018Part004CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block018Part004SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block018Part004] using hcert

def TailChunk000Sub000Block018Part005SupportExplicit : Finset ℕ :=
  ([797] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block018Part005 : ℚ :=
  (79321723875 : ℚ) / 334624607752576

def SurrogateDiagonalTailChunk000Sub000Block018Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 797
    = surrogateDiagTailX0RatChunk000Sub000Block018Part005

theorem surrogateDiagonalTailChunk000Sub000Block018Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block018Part005CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block018Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block018Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block018Part005CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block018Part005SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block018Part005] using hcert

def TailChunk000Sub000Block018Part006SupportExplicit : Finset ℕ :=
  ([798] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block018Part006 : ℚ :=
  (32989827275 : ℚ) / 2721522115584

def SurrogateDiagonalTailChunk000Sub000Block018Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 798
    = surrogateDiagTailX0RatChunk000Sub000Block018Part006

theorem surrogateDiagonalTailChunk000Sub000Block018Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block018Part006CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block018Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block018Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block018Part006CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block018Part006SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block018Part006] using hcert

def TailChunk000Sub000Block018Part007SupportExplicit : Finset ℕ :=
  ([799] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block018Part007 : ℚ :=
  (63752757625 : ℚ) / 183433277079552

def SurrogateDiagonalTailChunk000Sub000Block018Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 799
    = surrogateDiagTailX0RatChunk000Sub000Block018Part007

theorem surrogateDiagonalTailChunk000Sub000Block018Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block018Part007CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block018Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block018Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block018Part007CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block018Part007SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block018Part007] using hcert

def TailChunk000Sub000Block018Part008SupportExplicit : Finset ℕ :=
  ([802] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block018Part008 : ℚ :=
  (2606745011 : ℚ) / 1280256000000

def SurrogateDiagonalTailChunk000Sub000Block018Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 802
    = surrogateDiagTailX0RatChunk000Sub000Block018Part008

theorem surrogateDiagonalTailChunk000Sub000Block018Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block018Part008CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block018Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block018Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block018Part008CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block018Part008SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block018Part008] using hcert

def TailChunk000Sub000Block018Part009SupportExplicit : Finset ℕ :=
  ([803] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block018Part009 : ℚ :=
  (1450784891 : ℚ) / 4479871795200

def SurrogateDiagonalTailChunk000Sub000Block018Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 803
    = surrogateDiagTailX0RatChunk000Sub000Block018Part009

theorem surrogateDiagonalTailChunk000Sub000Block018Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block018Part009CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block018Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block018Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block018Part009CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block018Part009SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block018Part009] using hcert

def TailChunk000Sub000Block018Part010SupportExplicit : Finset ℕ :=
  ([805] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block018Part010 : ℚ :=
  (20231906075 : ℚ) / 24292519612416

def SurrogateDiagonalTailChunk000Sub000Block018Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 805
    = surrogateDiagTailX0RatChunk000Sub000Block018Part010

theorem surrogateDiagonalTailChunk000Sub000Block018Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block018Part010CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block018Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block018Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block018Part010CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block018Part010SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block018Part010] using hcert

def TailChunk000Sub000Block018Part011SupportExplicit : Finset ℕ :=
  ([806] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block018Part011 : ℚ :=
  (93819965 : ℚ) / 33599038464

def SurrogateDiagonalTailChunk000Sub000Block018Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 806
    = surrogateDiagTailX0RatChunk000Sub000Block018Part011

theorem surrogateDiagonalTailChunk000Sub000Block018Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block018Part011CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block018Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block018Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block018Part011CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block018Part011SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block018Part011] using hcert

def TailChunk000Sub000Block018Part012SupportExplicit : Finset ℕ :=
  ([807] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block018Part012 : ℚ :=
  (83374125575 : ℚ) / 103194374267904

def SurrogateDiagonalTailChunk000Sub000Block018Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 807
    = surrogateDiagTailX0RatChunk000Sub000Block018Part012

theorem surrogateDiagonalTailChunk000Sub000Block018Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block018Part012CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block018Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block018Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block018Part012CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block018Part012SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block018Part012] using hcert

def TailChunk000Sub000Block018Part013SupportExplicit : Finset ℕ :=
  ([809] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block018Part013 : ℚ :=
  (81728314875 : ℚ) / 355263873980416

def SurrogateDiagonalTailChunk000Sub000Block018Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 809
    = surrogateDiagTailX0RatChunk000Sub000Block018Part013

theorem surrogateDiagonalTailChunk000Sub000Block018Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block018Part013CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block018Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block018Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block018Part013CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block018Part013SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block018Part013] using hcert

def TailChunk000Sub000Block018Part014SupportExplicit : Finset ℕ :=
  ([811] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block018Part014 : ℚ :=
  (24335677 : ℚ) / 106309457640

def SurrogateDiagonalTailChunk000Sub000Block018Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 811
    = surrogateDiagTailX0RatChunk000Sub000Block018Part014

theorem surrogateDiagonalTailChunk000Sub000Block018Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block018Part014CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block018Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block018Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block018Part014CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block018Part014SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block018Part014] using hcert

def TailChunk000Sub000Block018Part015SupportExplicit : Finset ℕ :=
  ([813] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block018Part015 : ℚ :=
  (439061 : ℚ) / 566870400

def SurrogateDiagonalTailChunk000Sub000Block018Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 813
    = surrogateDiagTailX0RatChunk000Sub000Block018Part015

theorem surrogateDiagonalTailChunk000Sub000Block018Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block018Part015CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block018Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block018Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block018Part015CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block018Part015SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block018Part015] using hcert

def TailChunk000Sub000Block018Part016SupportExplicit : Finset ℕ :=
  ([814] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block018Part016 : ℚ :=
  (4409202553 : ℚ) / 1679951923200

def SurrogateDiagonalTailChunk000Sub000Block018Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 814
    = surrogateDiagTailX0RatChunk000Sub000Block018Part016

theorem surrogateDiagonalTailChunk000Sub000Block018Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block018Part016CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block018Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block018Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block018Part016CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block018Part016SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block018Part016] using hcert

def TailChunk000Sub000Block018Part017SupportExplicit : Finset ℕ :=
  ([815] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block018Part017 : ℚ :=
  (199753281625 : ℚ) / 440886582724608

def SurrogateDiagonalTailChunk000Sub000Block018Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 815
    = surrogateDiagTailX0RatChunk000Sub000Block018Part017

theorem surrogateDiagonalTailChunk000Sub000Block018Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block018Part017CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block018Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block018Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block018Part017CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block018Part017SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block018Part017] using hcert

def TailChunk000Sub000Block018Part018SupportExplicit : Finset ℕ :=
  ([817] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block018Part018 : ℚ :=
  (133847646875 : ℚ) / 408398412469824

def SurrogateDiagonalTailChunk000Sub000Block018Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 817
    = surrogateDiagTailX0RatChunk000Sub000Block018Part018

theorem surrogateDiagonalTailChunk000Sub000Block018Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block018Part018CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block018Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block018Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block018Part018CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block018Part018SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block018Part018] using hcert

def TailChunk000Sub000Block018Part019SupportExplicit : Finset ℕ :=
  ([818] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block018Part019 : ℚ :=
  (6954707575 : ℚ) / 3849417409536

def SurrogateDiagonalTailChunk000Sub000Block018Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 818
    = surrogateDiagTailX0RatChunk000Sub000Block018Part019

theorem surrogateDiagonalTailChunk000Sub000Block018Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block018Part019CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block018Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block018Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block018Part019CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block018Part019SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block018Part019] using hcert

def TailChunk000Sub000Block018Part020SupportExplicit : Finset ℕ :=
  ([821] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block018Part020 : ℚ :=
  (673366959 : ℚ) / 3014747895680

def SurrogateDiagonalTailChunk000Sub000Block018Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 821
    = surrogateDiagTailX0RatChunk000Sub000Block018Part020

theorem surrogateDiagonalTailChunk000Sub000Block018Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block018Part020CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block018Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block018Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block018Part020CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block018Part020SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block018Part020] using hcert

def TailChunk000Sub000Block018Part021SupportExplicit : Finset ℕ :=
  ([822] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block018Part021 : ℚ :=
  (1328520775 : ℚ) / 213856522752

def SurrogateDiagonalTailChunk000Sub000Block018Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 822
    = surrogateDiagTailX0RatChunk000Sub000Block018Part021

theorem surrogateDiagonalTailChunk000Sub000Block018Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block018Part021CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block018Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block018Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block018Part021CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block018Part021SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block018Part021] using hcert

def TailChunk000Sub000Block018Part022SupportExplicit : Finset ℕ :=
  ([823] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block018Part022 : ℚ :=
  (3132646625 : ℚ) / 14093832642888

def SurrogateDiagonalTailChunk000Sub000Block018Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 823
    = surrogateDiagTailX0RatChunk000Sub000Block018Part022

theorem surrogateDiagonalTailChunk000Sub000Block018Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block018Part022CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block018Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block018Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block018Part022CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block018Part022SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block018Part022] using hcert

def TailChunk000Sub000Block018Part023SupportExplicit : Finset ℕ :=
  ([826] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block018Part023 : ℚ :=
  (108040689625 : ℚ) / 36672780129408

def SurrogateDiagonalTailChunk000Sub000Block018Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 826
    = surrogateDiagTailX0RatChunk000Sub000Block018Part023

theorem surrogateDiagonalTailChunk000Sub000Block018Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block018Part023CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block018Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block018Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block018Part023CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block018Part023SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block018Part023] using hcert

def TailChunk000Sub000Block018Part024SupportExplicit : Finset ℕ :=
  ([827] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block018Part024 : ℚ :=
  (85405633875 : ℚ) / 387994700236696

def SurrogateDiagonalTailChunk000Sub000Block018Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 827
    = surrogateDiagTailX0RatChunk000Sub000Block018Part024

theorem surrogateDiagonalTailChunk000Sub000Block018Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block018Part024CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block018Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block018Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block018Part024CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block018Part024SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block018Part024] using hcert

def surrogateDiagonalTailChunk000Sub000Block018HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block018Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block018Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block018Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block018Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block018Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block018Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block018Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block018Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block018Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block018Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block018Head : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block018Part000
    + surrogateDiagTailX0RatChunk000Sub000Block018Part001
    + surrogateDiagTailX0RatChunk000Sub000Block018Part002
    + surrogateDiagTailX0RatChunk000Sub000Block018Part003
    + surrogateDiagTailX0RatChunk000Sub000Block018Part004
    + surrogateDiagTailX0RatChunk000Sub000Block018Part005
    + surrogateDiagTailX0RatChunk000Sub000Block018Part006
    + surrogateDiagTailX0RatChunk000Sub000Block018Part007
    + surrogateDiagTailX0RatChunk000Sub000Block018Part008
    + surrogateDiagTailX0RatChunk000Sub000Block018Part009

def surrogateDiagonalTailChunk000Sub000Block018MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block018Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block018Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block018Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block018Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block018Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block018Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block018Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block018Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block018Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block018Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block018Mid : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block018Part010
    + surrogateDiagTailX0RatChunk000Sub000Block018Part011
    + surrogateDiagTailX0RatChunk000Sub000Block018Part012
    + surrogateDiagTailX0RatChunk000Sub000Block018Part013
    + surrogateDiagTailX0RatChunk000Sub000Block018Part014
    + surrogateDiagTailX0RatChunk000Sub000Block018Part015
    + surrogateDiagTailX0RatChunk000Sub000Block018Part016
    + surrogateDiagTailX0RatChunk000Sub000Block018Part017
    + surrogateDiagTailX0RatChunk000Sub000Block018Part018
    + surrogateDiagTailX0RatChunk000Sub000Block018Part019

def surrogateDiagonalTailChunk000Sub000Block018TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block018Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block018Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block018Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block018Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block018Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block018Tail : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block018Part020
    + surrogateDiagTailX0RatChunk000Sub000Block018Part021
    + surrogateDiagTailX0RatChunk000Sub000Block018Part022
    + surrogateDiagTailX0RatChunk000Sub000Block018Part023
    + surrogateDiagTailX0RatChunk000Sub000Block018Part024

def surrogateDiagonalTailChunk000Sub000Block018Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub000Block018HeadSum X0
    + surrogateDiagonalTailChunk000Sub000Block018MidSum X0
    + surrogateDiagonalTailChunk000Sub000Block018TailSum X0

def surrogateDiagTailX0RatChunk000Sub000Block018 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block018Part000
    + surrogateDiagTailX0RatChunk000Sub000Block018Part001
    + surrogateDiagTailX0RatChunk000Sub000Block018Part002
    + surrogateDiagTailX0RatChunk000Sub000Block018Part003
    + surrogateDiagTailX0RatChunk000Sub000Block018Part004
    + surrogateDiagTailX0RatChunk000Sub000Block018Part005
    + surrogateDiagTailX0RatChunk000Sub000Block018Part006
    + surrogateDiagTailX0RatChunk000Sub000Block018Part007
    + surrogateDiagTailX0RatChunk000Sub000Block018Part008
    + surrogateDiagTailX0RatChunk000Sub000Block018Part009
    + surrogateDiagTailX0RatChunk000Sub000Block018Part010
    + surrogateDiagTailX0RatChunk000Sub000Block018Part011
    + surrogateDiagTailX0RatChunk000Sub000Block018Part012
    + surrogateDiagTailX0RatChunk000Sub000Block018Part013
    + surrogateDiagTailX0RatChunk000Sub000Block018Part014
    + surrogateDiagTailX0RatChunk000Sub000Block018Part015
    + surrogateDiagTailX0RatChunk000Sub000Block018Part016
    + surrogateDiagTailX0RatChunk000Sub000Block018Part017
    + surrogateDiagTailX0RatChunk000Sub000Block018Part018
    + surrogateDiagTailX0RatChunk000Sub000Block018Part019
    + surrogateDiagTailX0RatChunk000Sub000Block018Part020
    + surrogateDiagTailX0RatChunk000Sub000Block018Part021
    + surrogateDiagTailX0RatChunk000Sub000Block018Part022
    + surrogateDiagTailX0RatChunk000Sub000Block018Part023
    + surrogateDiagTailX0RatChunk000Sub000Block018Part024

theorem surrogateDiagTailX0RatChunk000Sub000Block018_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk000Sub000Block018Head + surrogateDiagTailX0RatChunk000Sub000Block018Mid + surrogateDiagTailX0RatChunk000Sub000Block018Tail =
      surrogateDiagTailX0RatChunk000Sub000Block018 := by
  unfold surrogateDiagTailX0RatChunk000Sub000Block018Head surrogateDiagTailX0RatChunk000Sub000Block018Mid surrogateDiagTailX0RatChunk000Sub000Block018Tail surrogateDiagTailX0RatChunk000Sub000Block018
  ring

def SurrogateDiagonalTailChunk000Sub000Block018HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block018HeadSum X0 = surrogateDiagTailX0RatChunk000Sub000Block018Head

def SurrogateDiagonalTailChunk000Sub000Block018MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block018MidSum X0 = surrogateDiagTailX0RatChunk000Sub000Block018Mid

def SurrogateDiagonalTailChunk000Sub000Block018TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block018TailSum X0 = surrogateDiagTailX0RatChunk000Sub000Block018Tail

theorem surrogateDiagonalTailChunk000Sub000Block018_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk000Sub000Block018HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk000Sub000Block018MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk000Sub000Block018TailCertificateAt X0) :
    surrogateDiagonalTailChunk000Sub000Block018Sum X0 = surrogateDiagTailX0RatChunk000Sub000Block018 := by
  unfold SurrogateDiagonalTailChunk000Sub000Block018HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk000Sub000Block018MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk000Sub000Block018TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk000Sub000Block018Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk000Sub000Block018_eq_head_add_mid_add_tail

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

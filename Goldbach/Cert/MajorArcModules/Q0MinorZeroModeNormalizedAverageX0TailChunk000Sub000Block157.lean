import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0TailPilot25

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

open scoped BigOperators

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

/- Generated direct-term certificate blocks for tail chunk 000, subchunk 000, blocks [157,158). -/

/- Block 157 covers tail-support indices [3925,3950) and q from 6506 to 6545. -/

def TailChunk000Sub000Block157Part000SupportExplicit : Finset ℕ :=
  ([6506] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block157Part000 : ℚ :=
  (1322486574775 : ℚ) / 279659132777467008

def SurrogateDiagonalTailChunk000Sub000Block157Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6506
    = surrogateDiagTailX0RatChunk000Sub000Block157Part000

theorem surrogateDiagonalTailChunk000Sub000Block157Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block157Part000CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block157Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block157Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block157Part000CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block157Part000SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block157Part000] using hcert

def TailChunk000Sub000Block157Part001SupportExplicit : Finset ℕ :=
  ([6509] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block157Part001 : ℚ :=
  (92496340375 : ℚ) / 137198780549576064

def SurrogateDiagonalTailChunk000Sub000Block157Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6509
    = surrogateDiagTailX0RatChunk000Sub000Block157Part001

theorem surrogateDiagonalTailChunk000Sub000Block157Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block157Part001CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block157Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block157Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block157Part001CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block157Part001SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block157Part001] using hcert

def TailChunk000Sub000Block157Part002SupportExplicit : Finset ℕ :=
  ([6510] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block157Part002 : ℚ :=
  (9997969301 : ℚ) / 215033846169600

def SurrogateDiagonalTailChunk000Sub000Block157Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6510
    = surrogateDiagTailX0RatChunk000Sub000Block157Part002

theorem surrogateDiagonalTailChunk000Sub000Block157Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block157Part002CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block157Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block157Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block157Part002CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block157Part002SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block157Part002] using hcert

def TailChunk000Sub000Block157Part003SupportExplicit : Finset ℕ :=
  ([6511] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block157Part003 : ℚ :=
  (2449668826375 : ℚ) / 3489476204749651968

def SurrogateDiagonalTailChunk000Sub000Block157Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6511
    = surrogateDiagTailX0RatChunk000Sub000Block157Part003

theorem surrogateDiagonalTailChunk000Sub000Block157Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block157Part003CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block157Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block157Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block157Part003CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block157Part003SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block157Part003] using hcert

def TailChunk000Sub000Block157Part004SupportExplicit : Finset ℕ :=
  ([6513] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block157Part004 : ℚ :=
  (1335492431875 : ℚ) / 629947240579104768

def SurrogateDiagonalTailChunk000Sub000Block157Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6513
    = surrogateDiagTailX0RatChunk000Sub000Block157Part004

theorem surrogateDiagonalTailChunk000Sub000Block157Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block157Part004CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block157Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block157Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block157Part004CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block157Part004SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block157Part004] using hcert

def TailChunk000Sub000Block157Part005SupportExplicit : Finset ℕ :=
  ([6514] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block157Part005 : ℚ :=
  (1325740923775 : ℚ) / 281037610181019648

def SurrogateDiagonalTailChunk000Sub000Block157Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6514
    = surrogateDiagTailX0RatChunk000Sub000Block157Part005

theorem surrogateDiagonalTailChunk000Sub000Block157Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block157Part005CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block157Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block157Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block157Part005CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block157Part005SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block157Part005] using hcert

def TailChunk000Sub000Block157Part006SupportExplicit : Finset ℕ :=
  ([6515] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block157Part006 : ℚ :=
  (167890527575 : ℚ) / 153295538396603904

def SurrogateDiagonalTailChunk000Sub000Block157Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6515
    = surrogateDiagTailX0RatChunk000Sub000Block157Part006

theorem surrogateDiagonalTailChunk000Sub000Block157Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block157Part006CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block157Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block157Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block157Part006CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block157Part006SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block157Part006] using hcert

def TailChunk000Sub000Block157Part007SupportExplicit : Finset ℕ :=
  ([6518] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block157Part007 : ℚ :=
  (165954390625 : ℚ) / 70432189189923762

def SurrogateDiagonalTailChunk000Sub000Block157Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6518
    = surrogateDiagTailX0RatChunk000Sub000Block157Part007

theorem surrogateDiagonalTailChunk000Sub000Block157Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block157Part007CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block157Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block157Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block157Part007CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block157Part007SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block157Part007] using hcert

def TailChunk000Sub000Block157Part008SupportExplicit : Finset ℕ :=
  ([6519] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block157Part008 : ℚ :=
  (18772710819 : ℚ) / 9984789603942400

def SurrogateDiagonalTailChunk000Sub000Block157Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6519
    = surrogateDiagTailX0RatChunk000Sub000Block157Part008

theorem surrogateDiagonalTailChunk000Sub000Block157Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block157Part008CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block157Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block157Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block157Part008CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block157Part008SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block157Part008] using hcert

def TailChunk000Sub000Block157Part009SupportExplicit : Finset ℕ :=
  ([6521] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block157Part009 : ℚ :=
  (1063086025 : ℚ) / 1807495534981632

def SurrogateDiagonalTailChunk000Sub000Block157Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6521
    = surrogateDiagTailX0RatChunk000Sub000Block157Part009

theorem surrogateDiagonalTailChunk000Sub000Block157Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block157Part009CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block157Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block157Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block157Part009CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block157Part009SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block157Part009] using hcert

def TailChunk000Sub000Block157Part010SupportExplicit : Finset ℕ :=
  ([6522] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block157Part010 : ℚ :=
  (590381611075 : ℚ) / 55650124792038528

def SurrogateDiagonalTailChunk000Sub000Block157Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6522
    = surrogateDiagTailX0RatChunk000Sub000Block157Part010

theorem surrogateDiagonalTailChunk000Sub000Block157Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block157Part010CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block157Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block157Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block157Part010CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block157Part010SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block157Part010] using hcert

def TailChunk000Sub000Block157Part011SupportExplicit : Finset ℕ :=
  ([6523] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block157Part011 : ℚ :=
  (93891166981 : ℚ) / 122849580299059200

def SurrogateDiagonalTailChunk000Sub000Block157Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6523
    = surrogateDiagTailX0RatChunk000Sub000Block157Part011

theorem surrogateDiagonalTailChunk000Sub000Block157Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block157Part011CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block157Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block157Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block157Part011CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block157Part011SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block157Part011] using hcert

def TailChunk000Sub000Block157Part012SupportExplicit : Finset ℕ :=
  ([6526] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block157Part012 : ℚ :=
  (25466187397 : ℚ) / 8101620000000000

def SurrogateDiagonalTailChunk000Sub000Block157Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6526
    = surrogateDiagTailX0RatChunk000Sub000Block157Part012

theorem surrogateDiagonalTailChunk000Sub000Block157Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block157Part012CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block157Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block157Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block157Part012CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block157Part012SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block157Part012] using hcert

def TailChunk000Sub000Block157Part013SupportExplicit : Finset ℕ :=
  ([6527] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block157Part013 : ℚ :=
  (1719613891 : ℚ) / 2727495623646720

def SurrogateDiagonalTailChunk000Sub000Block157Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6527
    = surrogateDiagTailX0RatChunk000Sub000Block157Part013

theorem surrogateDiagonalTailChunk000Sub000Block157Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block157Part013CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block157Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block157Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block157Part013CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block157Part013SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block157Part013] using hcert

def TailChunk000Sub000Block157Part014SupportExplicit : Finset ℕ :=
  ([6529] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block157Part014 : ℚ :=
  (666060015625 : ℚ) / 1135239387081080832

def SurrogateDiagonalTailChunk000Sub000Block157Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6529
    = surrogateDiagTailX0RatChunk000Sub000Block157Part014

theorem surrogateDiagonalTailChunk000Sub000Block157Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block157Part014CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block157Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block157Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block157Part014CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block157Part014SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block157Part014] using hcert

def TailChunk000Sub000Block157Part015SupportExplicit : Finset ℕ :=
  ([6530] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block157Part015 : ℚ :=
  (153102715675 : ℚ) / 28919928559706112

def SurrogateDiagonalTailChunk000Sub000Block157Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6530
    = surrogateDiagTailX0RatChunk000Sub000Block157Part015

theorem surrogateDiagonalTailChunk000Sub000Block157Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block157Part015CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block157Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block157Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block157Part015CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block157Part015SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block157Part015] using hcert

def TailChunk000Sub000Block157Part016SupportExplicit : Finset ℕ :=
  ([6531] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block157Part016 : ℚ :=
  (1574079557 : ℚ) / 598561296321600

def SurrogateDiagonalTailChunk000Sub000Block157Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6531
    = surrogateDiagTailX0RatChunk000Sub000Block157Part016

theorem surrogateDiagonalTailChunk000Sub000Block157Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block157Part016CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block157Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block157Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block157Part016CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block157Part016SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block157Part016] using hcert

def TailChunk000Sub000Block157Part017SupportExplicit : Finset ℕ :=
  ([6533] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block157Part017 : ℚ :=
  (143050148875 : ℚ) / 225580744736801856

def SurrogateDiagonalTailChunk000Sub000Block157Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6533
    = surrogateDiagTailX0RatChunk000Sub000Block157Part017

theorem surrogateDiagonalTailChunk000Sub000Block157Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block157Part017CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block157Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block157Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block157Part017CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block157Part017SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block157Part017] using hcert

def TailChunk000Sub000Block157Part018SupportExplicit : Finset ℕ :=
  ([6535] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block157Part018 : ℚ :=
  (7918268275 : ℚ) / 7274440008322248

def SurrogateDiagonalTailChunk000Sub000Block157Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6535
    = surrogateDiagTailX0RatChunk000Sub000Block157Part018

theorem surrogateDiagonalTailChunk000Sub000Block157Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block157Part018CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block157Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block157Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block157Part018CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block157Part018SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block157Part018] using hcert

def TailChunk000Sub000Block157Part019SupportExplicit : Finset ℕ :=
  ([6537] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block157Part019 : ℚ :=
  (92703957325 : ℚ) / 56267595998585928

def SurrogateDiagonalTailChunk000Sub000Block157Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6537
    = surrogateDiagTailX0RatChunk000Sub000Block157Part019

theorem surrogateDiagonalTailChunk000Sub000Block157Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block157Part019CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block157Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block157Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block157Part019CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block157Part019SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block157Part019] using hcert

def TailChunk000Sub000Block157Part020SupportExplicit : Finset ℕ :=
  ([6538] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block157Part020 : ℚ :=
  (122379692125 : ℚ) / 16979817485400192

def SurrogateDiagonalTailChunk000Sub000Block157Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6538
    = surrogateDiagTailX0RatChunk000Sub000Block157Part020

theorem surrogateDiagonalTailChunk000Sub000Block157Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block157Part020CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block157Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block157Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block157Part020CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block157Part020SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block157Part020] using hcert

def TailChunk000Sub000Block157Part021SupportExplicit : Finset ℕ :=
  ([6539] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block157Part021 : ℚ :=
  (149888197225 : ℚ) / 205800643790218368

def SurrogateDiagonalTailChunk000Sub000Block157Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6539
    = surrogateDiagTailX0RatChunk000Sub000Block157Part021

theorem surrogateDiagonalTailChunk000Sub000Block157Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block157Part021CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block157Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block157Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block157Part021CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block157Part021SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block157Part021] using hcert

def TailChunk000Sub000Block157Part022SupportExplicit : Finset ℕ :=
  ([6541] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block157Part022 : ℚ :=
  (51076056737 : ℚ) / 78780557961000000

def SurrogateDiagonalTailChunk000Sub000Block157Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6541
    = surrogateDiagTailX0RatChunk000Sub000Block157Part022

theorem surrogateDiagonalTailChunk000Sub000Block157Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block157Part022CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block157Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block157Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block157Part022CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block157Part022SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block157Part022] using hcert

def TailChunk000Sub000Block157Part023SupportExplicit : Finset ℕ :=
  ([6542] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block157Part023 : ℚ :=
  (53486505559 : ℚ) / 11436097803208200

def SurrogateDiagonalTailChunk000Sub000Block157Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6542
    = surrogateDiagTailX0RatChunk000Sub000Block157Part023

theorem surrogateDiagonalTailChunk000Sub000Block157Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block157Part023CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block157Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block157Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block157Part023CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block157Part023SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block157Part023] using hcert

def TailChunk000Sub000Block157Part024SupportExplicit : Finset ℕ :=
  ([6545] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block157Part024 : ℚ :=
  (11346790721 : ℚ) / 4349524118077440

def SurrogateDiagonalTailChunk000Sub000Block157Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6545
    = surrogateDiagTailX0RatChunk000Sub000Block157Part024

theorem surrogateDiagonalTailChunk000Sub000Block157Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block157Part024CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block157Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block157Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block157Part024CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block157Part024SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block157Part024] using hcert

def surrogateDiagonalTailChunk000Sub000Block157HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block157Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block157Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block157Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block157Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block157Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block157Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block157Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block157Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block157Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block157Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block157Head : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block157Part000
    + surrogateDiagTailX0RatChunk000Sub000Block157Part001
    + surrogateDiagTailX0RatChunk000Sub000Block157Part002
    + surrogateDiagTailX0RatChunk000Sub000Block157Part003
    + surrogateDiagTailX0RatChunk000Sub000Block157Part004
    + surrogateDiagTailX0RatChunk000Sub000Block157Part005
    + surrogateDiagTailX0RatChunk000Sub000Block157Part006
    + surrogateDiagTailX0RatChunk000Sub000Block157Part007
    + surrogateDiagTailX0RatChunk000Sub000Block157Part008
    + surrogateDiagTailX0RatChunk000Sub000Block157Part009

def surrogateDiagonalTailChunk000Sub000Block157MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block157Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block157Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block157Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block157Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block157Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block157Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block157Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block157Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block157Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block157Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block157Mid : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block157Part010
    + surrogateDiagTailX0RatChunk000Sub000Block157Part011
    + surrogateDiagTailX0RatChunk000Sub000Block157Part012
    + surrogateDiagTailX0RatChunk000Sub000Block157Part013
    + surrogateDiagTailX0RatChunk000Sub000Block157Part014
    + surrogateDiagTailX0RatChunk000Sub000Block157Part015
    + surrogateDiagTailX0RatChunk000Sub000Block157Part016
    + surrogateDiagTailX0RatChunk000Sub000Block157Part017
    + surrogateDiagTailX0RatChunk000Sub000Block157Part018
    + surrogateDiagTailX0RatChunk000Sub000Block157Part019

def surrogateDiagonalTailChunk000Sub000Block157TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block157Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block157Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block157Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block157Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block157Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block157Tail : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block157Part020
    + surrogateDiagTailX0RatChunk000Sub000Block157Part021
    + surrogateDiagTailX0RatChunk000Sub000Block157Part022
    + surrogateDiagTailX0RatChunk000Sub000Block157Part023
    + surrogateDiagTailX0RatChunk000Sub000Block157Part024

def surrogateDiagonalTailChunk000Sub000Block157Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub000Block157HeadSum X0
    + surrogateDiagonalTailChunk000Sub000Block157MidSum X0
    + surrogateDiagonalTailChunk000Sub000Block157TailSum X0

def surrogateDiagTailX0RatChunk000Sub000Block157 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block157Part000
    + surrogateDiagTailX0RatChunk000Sub000Block157Part001
    + surrogateDiagTailX0RatChunk000Sub000Block157Part002
    + surrogateDiagTailX0RatChunk000Sub000Block157Part003
    + surrogateDiagTailX0RatChunk000Sub000Block157Part004
    + surrogateDiagTailX0RatChunk000Sub000Block157Part005
    + surrogateDiagTailX0RatChunk000Sub000Block157Part006
    + surrogateDiagTailX0RatChunk000Sub000Block157Part007
    + surrogateDiagTailX0RatChunk000Sub000Block157Part008
    + surrogateDiagTailX0RatChunk000Sub000Block157Part009
    + surrogateDiagTailX0RatChunk000Sub000Block157Part010
    + surrogateDiagTailX0RatChunk000Sub000Block157Part011
    + surrogateDiagTailX0RatChunk000Sub000Block157Part012
    + surrogateDiagTailX0RatChunk000Sub000Block157Part013
    + surrogateDiagTailX0RatChunk000Sub000Block157Part014
    + surrogateDiagTailX0RatChunk000Sub000Block157Part015
    + surrogateDiagTailX0RatChunk000Sub000Block157Part016
    + surrogateDiagTailX0RatChunk000Sub000Block157Part017
    + surrogateDiagTailX0RatChunk000Sub000Block157Part018
    + surrogateDiagTailX0RatChunk000Sub000Block157Part019
    + surrogateDiagTailX0RatChunk000Sub000Block157Part020
    + surrogateDiagTailX0RatChunk000Sub000Block157Part021
    + surrogateDiagTailX0RatChunk000Sub000Block157Part022
    + surrogateDiagTailX0RatChunk000Sub000Block157Part023
    + surrogateDiagTailX0RatChunk000Sub000Block157Part024

theorem surrogateDiagTailX0RatChunk000Sub000Block157_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk000Sub000Block157Head + surrogateDiagTailX0RatChunk000Sub000Block157Mid + surrogateDiagTailX0RatChunk000Sub000Block157Tail =
      surrogateDiagTailX0RatChunk000Sub000Block157 := by
  unfold surrogateDiagTailX0RatChunk000Sub000Block157Head surrogateDiagTailX0RatChunk000Sub000Block157Mid surrogateDiagTailX0RatChunk000Sub000Block157Tail surrogateDiagTailX0RatChunk000Sub000Block157
  ring

def SurrogateDiagonalTailChunk000Sub000Block157HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block157HeadSum X0 = surrogateDiagTailX0RatChunk000Sub000Block157Head

def SurrogateDiagonalTailChunk000Sub000Block157MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block157MidSum X0 = surrogateDiagTailX0RatChunk000Sub000Block157Mid

def SurrogateDiagonalTailChunk000Sub000Block157TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block157TailSum X0 = surrogateDiagTailX0RatChunk000Sub000Block157Tail

theorem surrogateDiagonalTailChunk000Sub000Block157_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk000Sub000Block157HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk000Sub000Block157MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk000Sub000Block157TailCertificateAt X0) :
    surrogateDiagonalTailChunk000Sub000Block157Sum X0 = surrogateDiagTailX0RatChunk000Sub000Block157 := by
  unfold SurrogateDiagonalTailChunk000Sub000Block157HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk000Sub000Block157MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk000Sub000Block157TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk000Sub000Block157Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk000Sub000Block157_eq_head_add_mid_add_tail

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

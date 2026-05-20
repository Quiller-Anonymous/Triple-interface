import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0TailPilot25

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

open scoped BigOperators

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

/- Generated direct-term certificate blocks for tail chunk 000, subchunk 000, blocks [12,13). -/

/- Block 012 covers tail-support indices [300,325) and q from 543 to 583. -/

def TailChunk000Sub000Block012Part000SupportExplicit : Finset ℕ :=
  ([543] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block012Part000 : ℚ :=
  (94474781 : ℚ) / 33599038464

def SurrogateDiagonalTailChunk000Sub000Block012Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 543
    = surrogateDiagTailX0RatChunk000Sub000Block012Part000

theorem surrogateDiagonalTailChunk000Sub000Block012Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block012Part000CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block012Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block012Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block012Part000CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block012Part000SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block012Part000] using hcert

def TailChunk000Sub000Block012Part001SupportExplicit : Finset ℕ :=
  ([545] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block012Part001 : ℚ :=
  (133215165625 : ℚ) / 87088707698688

def SurrogateDiagonalTailChunk000Sub000Block012Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 545
    = surrogateDiagTailX0RatChunk000Sub000Block012Part001

theorem surrogateDiagonalTailChunk000Sub000Block012Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block012Part001CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block012Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block012Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block012Part001CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block012Part001SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block012Part001] using hcert

def TailChunk000Sub000Block012Part002SupportExplicit : Finset ℕ :=
  ([546] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block012Part002 : ℚ :=
  (4969693625 : ℚ) / 119463247872

def SurrogateDiagonalTailChunk000Sub000Block012Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 546
    = surrogateDiagTailX0RatChunk000Sub000Block012Part002

theorem surrogateDiagonalTailChunk000Sub000Block012Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block012Part002CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block012Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block012Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block012Part002CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block012Part002SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block012Part002] using hcert

def TailChunk000Sub000Block012Part003SupportExplicit : Finset ℕ :=
  ([547] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block012Part003 : ℚ :=
  (59841800 : ℚ) / 79140779991

def SurrogateDiagonalTailChunk000Sub000Block012Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 547
    = surrogateDiagTailX0RatChunk000Sub000Block012Part003

theorem surrogateDiagonalTailChunk000Sub000Block012Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block012Part003CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block012Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block012Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block012Part003CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block012Part003SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block012Part003] using hcert

def TailChunk000Sub000Block012Part004SupportExplicit : Finset ℕ :=
  ([551] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block012Part004 : ℚ :=
  (156331689775 : ℚ) / 161342582704128

def SurrogateDiagonalTailChunk000Sub000Block012Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 551
    = surrogateDiagTailX0RatChunk000Sub000Block012Part004

theorem surrogateDiagonalTailChunk000Sub000Block012Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block012Part004CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block012Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block012Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block012Part004CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block012Part004SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block012Part004] using hcert

def TailChunk000Sub000Block012Part005SupportExplicit : Finset ℕ :=
  ([553] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block012Part005 : ℚ :=
  (8089690525 : ℚ) / 6664042622016

def SurrogateDiagonalTailChunk000Sub000Block012Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 553
    = surrogateDiagTailX0RatChunk000Sub000Block012Part005

theorem surrogateDiagonalTailChunk000Sub000Block012Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block012Part005CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block012Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block012Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block012Part005CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block012Part005SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block012Part005] using hcert

def TailChunk000Sub000Block012Part006SupportExplicit : Finset ℕ :=
  ([554] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block012Part006 : ℚ :=
  (3186171725 : ℚ) / 537402178944

def SurrogateDiagonalTailChunk000Sub000Block012Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 554
    = surrogateDiagTailX0RatChunk000Sub000Block012Part006

theorem surrogateDiagonalTailChunk000Sub000Block012Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block012Part006CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block012Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block012Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block012Part006CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block012Part006SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block012Part006] using hcert

def TailChunk000Sub000Block012Part007SupportExplicit : Finset ℕ :=
  ([555] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block012Part007 : ℚ :=
  (89930606275 : ℚ) / 17202707693568

def SurrogateDiagonalTailChunk000Sub000Block012Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 555
    = surrogateDiagTailX0RatChunk000Sub000Block012Part007

theorem surrogateDiagonalTailChunk000Sub000Block012Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block012Part007CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block012Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block012Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block012Part007CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block012Part007SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block012Part007] using hcert

def TailChunk000Sub000Block012Part008SupportExplicit : Finset ℕ :=
  ([557] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block012Part008 : ℚ :=
  (907478325 : ℚ) / 1244585670694

def SurrogateDiagonalTailChunk000Sub000Block012Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 557
    = surrogateDiagTailX0RatChunk000Sub000Block012Part008

theorem surrogateDiagonalTailChunk000Sub000Block012Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block012Part008CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block012Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block012Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block012Part008CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block012Part008SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block012Part008] using hcert

def TailChunk000Sub000Block012Part009SupportExplicit : Finset ℕ :=
  ([559] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block012Part009 : ℚ :=
  (79244220575 : ℚ) / 80671291352064

def SurrogateDiagonalTailChunk000Sub000Block012Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 559
    = surrogateDiagTailX0RatChunk000Sub000Block012Part009

theorem surrogateDiagonalTailChunk000Sub000Block012Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block012Part009CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block012Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block012Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block012Part009CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block012Part009SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block012Part009] using hcert

def TailChunk000Sub000Block012Part010SupportExplicit : Finset ℕ :=
  ([561] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block012Part010 : ℚ :=
  (25213807 : ℚ) / 6554910720

def SurrogateDiagonalTailChunk000Sub000Block012Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 561
    = surrogateDiagTailX0RatChunk000Sub000Block012Part010

theorem surrogateDiagonalTailChunk000Sub000Block012Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block012Part010CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block012Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block012Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block012Part010CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block012Part010SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block012Part010] using hcert

def TailChunk000Sub000Block012Part011SupportExplicit : Finset ℕ :=
  ([562] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block012Part011 : ℚ :=
  (1180387989 : ℚ) / 204926310400

def SurrogateDiagonalTailChunk000Sub000Block012Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 562
    = surrogateDiagTailX0RatChunk000Sub000Block012Part011

theorem surrogateDiagonalTailChunk000Sub000Block012Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block012Part011CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block012Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block012Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block012Part011CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block012Part011SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block012Part011] using hcert

def TailChunk000Sub000Block012Part012SupportExplicit : Finset ℕ :=
  ([563] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block012Part012 : ℚ :=
  (39565655425 : ℚ) / 62360864889042

def SurrogateDiagonalTailChunk000Sub000Block012Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 563
    = surrogateDiagTailX0RatChunk000Sub000Block012Part012

theorem surrogateDiagonalTailChunk000Sub000Block012Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block012Part012CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block012Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block012Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block012Part012CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block012Part012SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block012Part012] using hcert

def TailChunk000Sub000Block012Part013SupportExplicit : Finset ℕ :=
  ([565] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block012Part013 : ℚ :=
  (71194110875 : ℚ) / 50362690043904

def SurrogateDiagonalTailChunk000Sub000Block012Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 565
    = surrogateDiagTailX0RatChunk000Sub000Block012Part013

theorem surrogateDiagonalTailChunk000Sub000Block012Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block012Part013CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block012Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block012Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block012Part013CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block012Part013SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block012Part013] using hcert

def TailChunk000Sub000Block012Part014SupportExplicit : Finset ℕ :=
  ([566] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block012Part014 : ℚ :=
  (3325695725 : ℚ) / 585678832344

def SurrogateDiagonalTailChunk000Sub000Block012Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 566
    = surrogateDiagTailX0RatChunk000Sub000Block012Part014

theorem surrogateDiagonalTailChunk000Sub000Block012Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block012Part014CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block012Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block012Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block012Part014CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block012Part014SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block012Part014] using hcert

def TailChunk000Sub000Block012Part015SupportExplicit : Finset ℕ :=
  ([569] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block012Part015 : ℚ :=
  (947000925 : ℚ) / 1355560711264

def SurrogateDiagonalTailChunk000Sub000Block012Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 569
    = surrogateDiagTailX0RatChunk000Sub000Block012Part015

theorem surrogateDiagonalTailChunk000Sub000Block012Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block012Part015CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block012Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block012Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block012Part015CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block012Part015SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block012Part015] using hcert

def TailChunk000Sub000Block012Part016SupportExplicit : Finset ℕ :=
  ([570] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block012Part016 : ℚ :=
  (44337355525 : ℚ) / 1075169230848

def SurrogateDiagonalTailChunk000Sub000Block012Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 570
    = surrogateDiagTailX0RatChunk000Sub000Block012Part016

theorem surrogateDiagonalTailChunk000Sub000Block012Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block012Part016CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block012Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block012Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block012Part016CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block012Part016SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block012Part016] using hcert

def TailChunk000Sub000Block012Part017SupportExplicit : Finset ℕ :=
  ([571] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block012Part017 : ℚ :=
  (33908264 : ℚ) / 48880149075

def SurrogateDiagonalTailChunk000Sub000Block012Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 571
    = surrogateDiagTailX0RatChunk000Sub000Block012Part017

theorem surrogateDiagonalTailChunk000Sub000Block012Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block012Part017CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block012Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block012Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block012Part017CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block012Part017SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block012Part017] using hcert

def TailChunk000Sub000Block012Part018SupportExplicit : Finset ℕ :=
  ([573] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block012Part018 : ℚ :=
  (1202266471 : ℚ) / 521388256800

def SurrogateDiagonalTailChunk000Sub000Block012Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 573
    = surrogateDiagTailX0RatChunk000Sub000Block012Part018

theorem surrogateDiagonalTailChunk000Sub000Block012Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block012Part018CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block012Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block012Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block012Part018CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block012Part018SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block012Part018] using hcert

def TailChunk000Sub000Block012Part019SupportExplicit : Finset ℕ :=
  ([574] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block012Part019 : ℚ :=
  (326862893 : ℚ) / 36871372800

def SurrogateDiagonalTailChunk000Sub000Block012Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 574
    = surrogateDiagTailX0RatChunk000Sub000Block012Part019

theorem surrogateDiagonalTailChunk000Sub000Block012Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block012Part019CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block012Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block012Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block012Part019CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block012Part019SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block012Part019] using hcert

def TailChunk000Sub000Block012Part020SupportExplicit : Finset ℕ :=
  ([577] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block012Part020 : ℚ :=
  (108201925 : ℚ) / 159284330496

def SurrogateDiagonalTailChunk000Sub000Block012Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 577
    = surrogateDiagTailX0RatChunk000Sub000Block012Part020

theorem surrogateDiagonalTailChunk000Sub000Block012Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block012Part020CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block012Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block012Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block012Part020CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block012Part020SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block012Part020] using hcert

def TailChunk000Sub000Block012Part021SupportExplicit : Finset ℕ :=
  ([579] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block012Part021 : ℚ :=
  (61378946825 : ℚ) / 27184525737984

def SurrogateDiagonalTailChunk000Sub000Block012Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 579
    = surrogateDiagTailX0RatChunk000Sub000Block012Part021

theorem surrogateDiagonalTailChunk000Sub000Block012Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block012Part021CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block012Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block012Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block012Part021CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block012Part021SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block012Part021] using hcert

def TailChunk000Sub000Block012Part022SupportExplicit : Finset ℕ :=
  ([581] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block012Part022 : ℚ :=
  (8859769175 : ℚ) / 8139819318336

def SurrogateDiagonalTailChunk000Sub000Block012Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 581
    = surrogateDiagTailX0RatChunk000Sub000Block012Part022

theorem surrogateDiagonalTailChunk000Sub000Block012Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block012Part022CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block012Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block012Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block012Part022CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block012Part022SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block012Part022] using hcert

def TailChunk000Sub000Block012Part023SupportExplicit : Finset ℕ :=
  ([582] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block012Part023 : ℚ :=
  (59958559225 : ℚ) / 3398065717248

def SurrogateDiagonalTailChunk000Sub000Block012Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 582
    = surrogateDiagTailX0RatChunk000Sub000Block012Part023

theorem surrogateDiagonalTailChunk000Sub000Block012Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block012Part023CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block012Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block012Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block012Part023CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block012Part023SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block012Part023] using hcert

def TailChunk000Sub000Block012Part024SupportExplicit : Finset ℕ :=
  ([583] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block012Part024 : ℚ :=
  (678934597 : ℚ) / 731307832320

def SurrogateDiagonalTailChunk000Sub000Block012Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 583
    = surrogateDiagTailX0RatChunk000Sub000Block012Part024

theorem surrogateDiagonalTailChunk000Sub000Block012Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block012Part024CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block012Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block012Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block012Part024CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block012Part024SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block012Part024] using hcert

def surrogateDiagonalTailChunk000Sub000Block012HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block012Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block012Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block012Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block012Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block012Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block012Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block012Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block012Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block012Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block012Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block012Head : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block012Part000
    + surrogateDiagTailX0RatChunk000Sub000Block012Part001
    + surrogateDiagTailX0RatChunk000Sub000Block012Part002
    + surrogateDiagTailX0RatChunk000Sub000Block012Part003
    + surrogateDiagTailX0RatChunk000Sub000Block012Part004
    + surrogateDiagTailX0RatChunk000Sub000Block012Part005
    + surrogateDiagTailX0RatChunk000Sub000Block012Part006
    + surrogateDiagTailX0RatChunk000Sub000Block012Part007
    + surrogateDiagTailX0RatChunk000Sub000Block012Part008
    + surrogateDiagTailX0RatChunk000Sub000Block012Part009

def surrogateDiagonalTailChunk000Sub000Block012MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block012Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block012Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block012Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block012Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block012Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block012Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block012Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block012Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block012Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block012Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block012Mid : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block012Part010
    + surrogateDiagTailX0RatChunk000Sub000Block012Part011
    + surrogateDiagTailX0RatChunk000Sub000Block012Part012
    + surrogateDiagTailX0RatChunk000Sub000Block012Part013
    + surrogateDiagTailX0RatChunk000Sub000Block012Part014
    + surrogateDiagTailX0RatChunk000Sub000Block012Part015
    + surrogateDiagTailX0RatChunk000Sub000Block012Part016
    + surrogateDiagTailX0RatChunk000Sub000Block012Part017
    + surrogateDiagTailX0RatChunk000Sub000Block012Part018
    + surrogateDiagTailX0RatChunk000Sub000Block012Part019

def surrogateDiagonalTailChunk000Sub000Block012TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block012Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block012Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block012Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block012Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block012Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block012Tail : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block012Part020
    + surrogateDiagTailX0RatChunk000Sub000Block012Part021
    + surrogateDiagTailX0RatChunk000Sub000Block012Part022
    + surrogateDiagTailX0RatChunk000Sub000Block012Part023
    + surrogateDiagTailX0RatChunk000Sub000Block012Part024

def surrogateDiagonalTailChunk000Sub000Block012Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub000Block012HeadSum X0
    + surrogateDiagonalTailChunk000Sub000Block012MidSum X0
    + surrogateDiagonalTailChunk000Sub000Block012TailSum X0

def surrogateDiagTailX0RatChunk000Sub000Block012 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block012Part000
    + surrogateDiagTailX0RatChunk000Sub000Block012Part001
    + surrogateDiagTailX0RatChunk000Sub000Block012Part002
    + surrogateDiagTailX0RatChunk000Sub000Block012Part003
    + surrogateDiagTailX0RatChunk000Sub000Block012Part004
    + surrogateDiagTailX0RatChunk000Sub000Block012Part005
    + surrogateDiagTailX0RatChunk000Sub000Block012Part006
    + surrogateDiagTailX0RatChunk000Sub000Block012Part007
    + surrogateDiagTailX0RatChunk000Sub000Block012Part008
    + surrogateDiagTailX0RatChunk000Sub000Block012Part009
    + surrogateDiagTailX0RatChunk000Sub000Block012Part010
    + surrogateDiagTailX0RatChunk000Sub000Block012Part011
    + surrogateDiagTailX0RatChunk000Sub000Block012Part012
    + surrogateDiagTailX0RatChunk000Sub000Block012Part013
    + surrogateDiagTailX0RatChunk000Sub000Block012Part014
    + surrogateDiagTailX0RatChunk000Sub000Block012Part015
    + surrogateDiagTailX0RatChunk000Sub000Block012Part016
    + surrogateDiagTailX0RatChunk000Sub000Block012Part017
    + surrogateDiagTailX0RatChunk000Sub000Block012Part018
    + surrogateDiagTailX0RatChunk000Sub000Block012Part019
    + surrogateDiagTailX0RatChunk000Sub000Block012Part020
    + surrogateDiagTailX0RatChunk000Sub000Block012Part021
    + surrogateDiagTailX0RatChunk000Sub000Block012Part022
    + surrogateDiagTailX0RatChunk000Sub000Block012Part023
    + surrogateDiagTailX0RatChunk000Sub000Block012Part024

theorem surrogateDiagTailX0RatChunk000Sub000Block012_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk000Sub000Block012Head + surrogateDiagTailX0RatChunk000Sub000Block012Mid + surrogateDiagTailX0RatChunk000Sub000Block012Tail =
      surrogateDiagTailX0RatChunk000Sub000Block012 := by
  unfold surrogateDiagTailX0RatChunk000Sub000Block012Head surrogateDiagTailX0RatChunk000Sub000Block012Mid surrogateDiagTailX0RatChunk000Sub000Block012Tail surrogateDiagTailX0RatChunk000Sub000Block012
  ring

def SurrogateDiagonalTailChunk000Sub000Block012HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block012HeadSum X0 = surrogateDiagTailX0RatChunk000Sub000Block012Head

def SurrogateDiagonalTailChunk000Sub000Block012MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block012MidSum X0 = surrogateDiagTailX0RatChunk000Sub000Block012Mid

def SurrogateDiagonalTailChunk000Sub000Block012TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block012TailSum X0 = surrogateDiagTailX0RatChunk000Sub000Block012Tail

theorem surrogateDiagonalTailChunk000Sub000Block012_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk000Sub000Block012HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk000Sub000Block012MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk000Sub000Block012TailCertificateAt X0) :
    surrogateDiagonalTailChunk000Sub000Block012Sum X0 = surrogateDiagTailX0RatChunk000Sub000Block012 := by
  unfold SurrogateDiagonalTailChunk000Sub000Block012HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk000Sub000Block012MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk000Sub000Block012TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk000Sub000Block012Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk000Sub000Block012_eq_head_add_mid_add_tail

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

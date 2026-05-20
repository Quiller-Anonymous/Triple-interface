import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0TailPilot25

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

open scoped BigOperators

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

/- Generated direct-term certificate blocks for tail chunk 000, subchunk 000, blocks [64,65). -/

/- Block 064 covers tail-support indices [1600,1625) and q from 2683 to 2721. -/

def TailChunk000Sub000Block064Part000SupportExplicit : Finset ℕ :=
  ([2683] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block064Part000 : ℚ :=
  (899631162775 : ℚ) / 129378452714879688

def SurrogateDiagonalTailChunk000Sub000Block064Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2683
    = surrogateDiagTailX0RatChunk000Sub000Block064Part000

theorem surrogateDiagonalTailChunk000Sub000Block064Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block064Part000CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block064Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block064Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block064Part000CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block064Part000SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block064Part000] using hcert

def TailChunk000Sub000Block064Part001SupportExplicit : Finset ℕ :=
  ([2685] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block064Part001 : ℚ :=
  (155979103275 : ℚ) / 3427248234397696

def SurrogateDiagonalTailChunk000Sub000Block064Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2685
    = surrogateDiagTailX0RatChunk000Sub000Block064Part001

theorem surrogateDiagonalTailChunk000Sub000Block064Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block064Part001CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block064Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block064Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block064Part001CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block064Part001SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block064Part001] using hcert

def TailChunk000Sub000Block064Part002SupportExplicit : Finset ℕ :=
  ([2686] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block064Part002 : ℚ :=
  (52102827275 : ℚ) / 758219960549376

def SurrogateDiagonalTailChunk000Sub000Block064Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2686
    = surrogateDiagTailX0RatChunk000Sub000Block064Part002

theorem surrogateDiagonalTailChunk000Sub000Block064Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block064Part002CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block064Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block064Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block064Part002CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block064Part002SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block064Part002] using hcert

def TailChunk000Sub000Block064Part003SupportExplicit : Finset ℕ :=
  ([2687] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block064Part003 : ℚ :=
  (112812015625 : ℚ) / 32538003451440402

def SurrogateDiagonalTailChunk000Sub000Block064Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2687
    = surrogateDiagTailX0RatChunk000Sub000Block064Part003

theorem surrogateDiagonalTailChunk000Sub000Block064Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block064Part003CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block064Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block064Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block064Part003CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block064Part003SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block064Part003] using hcert

def TailChunk000Sub000Block064Part004SupportExplicit : Finset ℕ :=
  ([2689] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block064Part004 : ℚ :=
  (903659356975 : ℚ) / 130540092593799168

def SurrogateDiagonalTailChunk000Sub000Block064Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2689
    = surrogateDiagTailX0RatChunk000Sub000Block064Part004

theorem surrogateDiagonalTailChunk000Sub000Block064Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block064Part004CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block064Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block064Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block064Part004CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block064Part004SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block064Part004] using hcert

def TailChunk000Sub000Block064Part005SupportExplicit : Finset ℕ :=
  ([2690] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block064Part005 : ℚ :=
  (88986840025 : ℚ) / 825554994143232

def SurrogateDiagonalTailChunk000Sub000Block064Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2690
    = surrogateDiagTailX0RatChunk000Sub000Block064Part005

theorem surrogateDiagonalTailChunk000Sub000Block064Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block064Part005CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block064Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block064Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block064Part005CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block064Part005SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block064Part005] using hcert

def TailChunk000Sub000Block064Part006SupportExplicit : Finset ℕ :=
  ([2693] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block064Part006 : ℚ :=
  (906349818775 : ℚ) / 131318853105157248

def SurrogateDiagonalTailChunk000Sub000Block064Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2693
    = surrogateDiagTailX0RatChunk000Sub000Block064Part006

theorem surrogateDiagonalTailChunk000Sub000Block064Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block064Part006CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block064Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block064Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block064Part006CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block064Part006SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block064Part006] using hcert

def TailChunk000Sub000Block064Part007SupportExplicit : Finset ℕ :=
  ([2694] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block064Part007 : ℚ :=
  (251544095725 : ℚ) / 1611606081404928

def SurrogateDiagonalTailChunk000Sub000Block064Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2694
    = surrogateDiagTailX0RatChunk000Sub000Block064Part007

theorem surrogateDiagonalTailChunk000Sub000Block064Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block064Part007CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block064Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block064Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block064Part007CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block064Part007SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block064Part007] using hcert

def TailChunk000Sub000Block064Part008SupportExplicit : Finset ℕ :=
  ([2697] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block064Part008 : ℚ :=
  (6927947071 : ℚ) / 265584498278400

def SurrogateDiagonalTailChunk000Sub000Block064Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2697
    = surrogateDiagTailX0RatChunk000Sub000Block064Part008

theorem surrogateDiagonalTailChunk000Sub000Block064Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block064Part008CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block064Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block064Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block064Part008CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block064Part008SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block064Part008] using hcert

def TailChunk000Sub000Block064Part009SupportExplicit : Finset ℕ :=
  ([2698] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block064Part009 : ℚ :=
  (301951049 : ℚ) / 4501746169200

def SurrogateDiagonalTailChunk000Sub000Block064Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2698
    = surrogateDiagTailX0RatChunk000Sub000Block064Part009

theorem surrogateDiagonalTailChunk000Sub000Block064Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block064Part009CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block064Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block064Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block064Part009CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block064Part009SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block064Part009] using hcert

def TailChunk000Sub000Block064Part010SupportExplicit : Finset ℕ :=
  ([2699] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block064Part010 : ℚ :=
  (910393009975 : ℚ) / 132493520589476808

def SurrogateDiagonalTailChunk000Sub000Block064Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2699
    = surrogateDiagTailX0RatChunk000Sub000Block064Part010

theorem surrogateDiagonalTailChunk000Sub000Block064Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block064Part010CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block064Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block064Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block064Part010CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block064Part010SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block064Part010] using hcert

def TailChunk000Sub000Block064Part011SupportExplicit : Finset ℕ :=
  ([2701] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block064Part011 : ℚ :=
  (452792815075 : ℚ) / 112866965177499648

def SurrogateDiagonalTailChunk000Sub000Block064Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2701
    = surrogateDiagTailX0RatChunk000Sub000Block064Part011

theorem surrogateDiagonalTailChunk000Sub000Block064Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block064Part011CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block064Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block064Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block064Part011CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block064Part011SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block064Part011] using hcert

def TailChunk000Sub000Block064Part012SupportExplicit : Finset ℕ :=
  ([2702] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block064Part012 : ℚ :=
  (9491856875 : ℚ) / 137621661548544

def SurrogateDiagonalTailChunk000Sub000Block064Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2702
    = surrogateDiagTailX0RatChunk000Sub000Block064Part012

theorem surrogateDiagonalTailChunk000Sub000Block064Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block064Part012CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block064Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block064Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block064Part012CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block064Part012SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block064Part012] using hcert

def TailChunk000Sub000Block064Part013SupportExplicit : Finset ℕ :=
  ([2703] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block064Part013 : ℚ :=
  (559323994825 : ℚ) / 19170796039569408

def SurrogateDiagonalTailChunk000Sub000Block064Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2703
    = surrogateDiagTailX0RatChunk000Sub000Block064Part013

theorem surrogateDiagonalTailChunk000Sub000Block064Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block064Part013CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block064Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block064Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block064Part013CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block064Part013SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block064Part013] using hcert

def TailChunk000Sub000Block064Part014SupportExplicit : Finset ℕ :=
  ([2705] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block064Part014 : ℚ :=
  (131881919 : ℚ) / 10079711539200

def SurrogateDiagonalTailChunk000Sub000Block064Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2705
    = surrogateDiagTailX0RatChunk000Sub000Block064Part014

theorem surrogateDiagonalTailChunk000Sub000Block064Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block064Part014CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block064Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block064Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block064Part014CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block064Part014SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block064Part014] using hcert

def TailChunk000Sub000Block064Part015SupportExplicit : Finset ℕ :=
  ([2706] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block064Part015 : ℚ :=
  (1720351299 : ℚ) / 6828032000000

def SurrogateDiagonalTailChunk000Sub000Block064Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2706
    = surrogateDiagTailX0RatChunk000Sub000Block064Part015

theorem surrogateDiagonalTailChunk000Sub000Block064Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block064Part015CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block064Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block064Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block064Part015CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block064Part015SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block064Part015] using hcert

def TailChunk000Sub000Block064Part016SupportExplicit : Finset ℕ :=
  ([2707] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block064Part016 : ℚ :=
  (915797928775 : ℚ) / 134071981469727048

def SurrogateDiagonalTailChunk000Sub000Block064Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2707
    = surrogateDiagTailX0RatChunk000Sub000Block064Part016

theorem surrogateDiagonalTailChunk000Sub000Block064Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block064Part016CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block064Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block064Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block064Part016CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block064Part016SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block064Part016] using hcert

def TailChunk000Sub000Block064Part017SupportExplicit : Finset ℕ :=
  ([2710] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block064Part017 : ℚ :=
  (5766802541 : ℚ) / 68038052889600

def SurrogateDiagonalTailChunk000Sub000Block064Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2710
    = surrogateDiagTailX0RatChunk000Sub000Block064Part017

theorem surrogateDiagonalTailChunk000Sub000Block064Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block064Part017CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block064Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block064Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block064Part017CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block064Part017SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block064Part017] using hcert

def TailChunk000Sub000Block064Part018SupportExplicit : Finset ℕ :=
  ([2711] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block064Part018 : ℚ :=
  (36740255479 : ℚ) / 5394659197096200

def SurrogateDiagonalTailChunk000Sub000Block064Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2711
    = surrogateDiagTailX0RatChunk000Sub000Block064Part018

theorem surrogateDiagonalTailChunk000Sub000Block064Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block064Part018CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block064Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block064Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block064Part018CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block064Part018SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block064Part018] using hcert

def TailChunk000Sub000Block064Part019SupportExplicit : Finset ℕ :=
  ([2713] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block064Part019 : ℚ :=
  (919862115775 : ℚ) / 135265050708461568

def SurrogateDiagonalTailChunk000Sub000Block064Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2713
    = surrogateDiagTailX0RatChunk000Sub000Block064Part019

theorem surrogateDiagonalTailChunk000Sub000Block064Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block064Part019CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block064Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block064Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block064Part019CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block064Part019SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block064Part019] using hcert

def TailChunk000Sub000Block064Part020SupportExplicit : Finset ℕ :=
  ([2714] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block064Part020 : ℚ :=
  (143631787725 : ℚ) / 2209572731994496

def SurrogateDiagonalTailChunk000Sub000Block064Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2714
    = surrogateDiagTailX0RatChunk000Sub000Block064Part020

theorem surrogateDiagonalTailChunk000Sub000Block064Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block064Part020CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block064Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block064Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block064Part020CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block064Part020SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block064Part020] using hcert

def TailChunk000Sub000Block064Part021SupportExplicit : Finset ℕ :=
  ([2715] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block064Part021 : ℚ :=
  (1938122353 : ℚ) / 43006769233920

def SurrogateDiagonalTailChunk000Sub000Block064Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2715
    = surrogateDiagTailX0RatChunk000Sub000Block064Part021

theorem surrogateDiagonalTailChunk000Sub000Block064Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block064Part021CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block064Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block064Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block064Part021CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block064Part021SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block064Part021] using hcert

def TailChunk000Sub000Block064Part022SupportExplicit : Finset ℕ :=
  ([2717] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block064Part022 : ℚ :=
  (289578007 : ℚ) / 36286961541120

def SurrogateDiagonalTailChunk000Sub000Block064Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2717
    = surrogateDiagTailX0RatChunk000Sub000Block064Part022

theorem surrogateDiagonalTailChunk000Sub000Block064Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block064Part022CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block064Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block064Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block064Part022CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block064Part022SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block064Part022] using hcert

def TailChunk000Sub000Block064Part023SupportExplicit : Finset ℕ :=
  ([2719] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block064Part023 : ℚ :=
  (923935300975 : ℚ) / 136466064881865288

def SurrogateDiagonalTailChunk000Sub000Block064Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2719
    = surrogateDiagTailX0RatChunk000Sub000Block064Part023

theorem surrogateDiagonalTailChunk000Sub000Block064Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block064Part023CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block064Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block064Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block064Part023CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block064Part023SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block064Part023] using hcert

def TailChunk000Sub000Block064Part024SupportExplicit : Finset ℕ :=
  ([2721] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block064Part024 : ℚ :=
  (565051894225 : ℚ) / 26956259729751168

def SurrogateDiagonalTailChunk000Sub000Block064Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2721
    = surrogateDiagTailX0RatChunk000Sub000Block064Part024

theorem surrogateDiagonalTailChunk000Sub000Block064Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block064Part024CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block064Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block064Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block064Part024CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block064Part024SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block064Part024] using hcert

def surrogateDiagonalTailChunk000Sub000Block064HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block064Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block064Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block064Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block064Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block064Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block064Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block064Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block064Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block064Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block064Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block064Head : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block064Part000
    + surrogateDiagTailX0RatChunk000Sub000Block064Part001
    + surrogateDiagTailX0RatChunk000Sub000Block064Part002
    + surrogateDiagTailX0RatChunk000Sub000Block064Part003
    + surrogateDiagTailX0RatChunk000Sub000Block064Part004
    + surrogateDiagTailX0RatChunk000Sub000Block064Part005
    + surrogateDiagTailX0RatChunk000Sub000Block064Part006
    + surrogateDiagTailX0RatChunk000Sub000Block064Part007
    + surrogateDiagTailX0RatChunk000Sub000Block064Part008
    + surrogateDiagTailX0RatChunk000Sub000Block064Part009

def surrogateDiagonalTailChunk000Sub000Block064MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block064Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block064Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block064Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block064Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block064Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block064Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block064Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block064Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block064Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block064Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block064Mid : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block064Part010
    + surrogateDiagTailX0RatChunk000Sub000Block064Part011
    + surrogateDiagTailX0RatChunk000Sub000Block064Part012
    + surrogateDiagTailX0RatChunk000Sub000Block064Part013
    + surrogateDiagTailX0RatChunk000Sub000Block064Part014
    + surrogateDiagTailX0RatChunk000Sub000Block064Part015
    + surrogateDiagTailX0RatChunk000Sub000Block064Part016
    + surrogateDiagTailX0RatChunk000Sub000Block064Part017
    + surrogateDiagTailX0RatChunk000Sub000Block064Part018
    + surrogateDiagTailX0RatChunk000Sub000Block064Part019

def surrogateDiagonalTailChunk000Sub000Block064TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block064Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block064Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block064Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block064Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block064Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block064Tail : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block064Part020
    + surrogateDiagTailX0RatChunk000Sub000Block064Part021
    + surrogateDiagTailX0RatChunk000Sub000Block064Part022
    + surrogateDiagTailX0RatChunk000Sub000Block064Part023
    + surrogateDiagTailX0RatChunk000Sub000Block064Part024

def surrogateDiagonalTailChunk000Sub000Block064Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub000Block064HeadSum X0
    + surrogateDiagonalTailChunk000Sub000Block064MidSum X0
    + surrogateDiagonalTailChunk000Sub000Block064TailSum X0

def surrogateDiagTailX0RatChunk000Sub000Block064 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block064Part000
    + surrogateDiagTailX0RatChunk000Sub000Block064Part001
    + surrogateDiagTailX0RatChunk000Sub000Block064Part002
    + surrogateDiagTailX0RatChunk000Sub000Block064Part003
    + surrogateDiagTailX0RatChunk000Sub000Block064Part004
    + surrogateDiagTailX0RatChunk000Sub000Block064Part005
    + surrogateDiagTailX0RatChunk000Sub000Block064Part006
    + surrogateDiagTailX0RatChunk000Sub000Block064Part007
    + surrogateDiagTailX0RatChunk000Sub000Block064Part008
    + surrogateDiagTailX0RatChunk000Sub000Block064Part009
    + surrogateDiagTailX0RatChunk000Sub000Block064Part010
    + surrogateDiagTailX0RatChunk000Sub000Block064Part011
    + surrogateDiagTailX0RatChunk000Sub000Block064Part012
    + surrogateDiagTailX0RatChunk000Sub000Block064Part013
    + surrogateDiagTailX0RatChunk000Sub000Block064Part014
    + surrogateDiagTailX0RatChunk000Sub000Block064Part015
    + surrogateDiagTailX0RatChunk000Sub000Block064Part016
    + surrogateDiagTailX0RatChunk000Sub000Block064Part017
    + surrogateDiagTailX0RatChunk000Sub000Block064Part018
    + surrogateDiagTailX0RatChunk000Sub000Block064Part019
    + surrogateDiagTailX0RatChunk000Sub000Block064Part020
    + surrogateDiagTailX0RatChunk000Sub000Block064Part021
    + surrogateDiagTailX0RatChunk000Sub000Block064Part022
    + surrogateDiagTailX0RatChunk000Sub000Block064Part023
    + surrogateDiagTailX0RatChunk000Sub000Block064Part024

theorem surrogateDiagTailX0RatChunk000Sub000Block064_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk000Sub000Block064Head + surrogateDiagTailX0RatChunk000Sub000Block064Mid + surrogateDiagTailX0RatChunk000Sub000Block064Tail =
      surrogateDiagTailX0RatChunk000Sub000Block064 := by
  unfold surrogateDiagTailX0RatChunk000Sub000Block064Head surrogateDiagTailX0RatChunk000Sub000Block064Mid surrogateDiagTailX0RatChunk000Sub000Block064Tail surrogateDiagTailX0RatChunk000Sub000Block064
  ring

def SurrogateDiagonalTailChunk000Sub000Block064HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block064HeadSum X0 = surrogateDiagTailX0RatChunk000Sub000Block064Head

def SurrogateDiagonalTailChunk000Sub000Block064MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block064MidSum X0 = surrogateDiagTailX0RatChunk000Sub000Block064Mid

def SurrogateDiagonalTailChunk000Sub000Block064TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block064TailSum X0 = surrogateDiagTailX0RatChunk000Sub000Block064Tail

theorem surrogateDiagonalTailChunk000Sub000Block064_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk000Sub000Block064HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk000Sub000Block064MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk000Sub000Block064TailCertificateAt X0) :
    surrogateDiagonalTailChunk000Sub000Block064Sum X0 = surrogateDiagTailX0RatChunk000Sub000Block064 := by
  unfold SurrogateDiagonalTailChunk000Sub000Block064HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk000Sub000Block064MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk000Sub000Block064TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk000Sub000Block064Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk000Sub000Block064_eq_head_add_mid_add_tail

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

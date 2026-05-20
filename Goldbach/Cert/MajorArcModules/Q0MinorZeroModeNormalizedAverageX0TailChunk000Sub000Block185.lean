import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0TailPilot25

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

open scoped BigOperators

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

/- Generated direct-term certificate blocks for tail chunk 000, subchunk 000, blocks [185,186). -/

/-- Block 185 covers tail-support indices [4625,4650) and q from 7657 to 7697. -/

def TailChunk000Sub000Block185Part000SupportExplicit : Finset ℕ :=
  ([7657] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block185Part000 : ℚ :=
  (13733085007 : ℚ) / 176354633089843200

def SurrogateDiagonalTailChunk000Sub000Block185Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7657
    = surrogateDiagTailX0RatChunk000Sub000Block185Part000

theorem surrogateDiagonalTailChunk000Sub000Block185Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block185Part000CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block185Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block185Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block185Part000CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block185Part000SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block185Part000] using hcert

def TailChunk000Sub000Block185Part001SupportExplicit : Finset ℕ :=
  ([7658] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block185Part001 : ℚ :=
  (821840147125 : ℚ) / 288006594038287488

def SurrogateDiagonalTailChunk000Sub000Block185Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7658
    = surrogateDiagTailX0RatChunk000Sub000Block185Part001

theorem surrogateDiagonalTailChunk000Sub000Block185Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block185Part001CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block185Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block185Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block185Part001CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block185Part001SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block185Part001] using hcert

def TailChunk000Sub000Block185Part002SupportExplicit : Finset ℕ :=
  ([7661] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block185Part002 : ℚ :=
  (1351385825 : ℚ) / 160648622651350296

def SurrogateDiagonalTailChunk000Sub000Block185Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7661
    = surrogateDiagTailX0RatChunk000Sub000Block185Part002

theorem surrogateDiagonalTailChunk000Sub000Block185Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block185Part002CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block185Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block185Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block185Part002CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block185Part002SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block185Part002] using hcert

def TailChunk000Sub000Block185Part003SupportExplicit : Finset ℕ :=
  ([7662] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block185Part003 : ℚ :=
  (713073893725 : ℚ) / 106059491135735808

def SurrogateDiagonalTailChunk000Sub000Block185Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7662
    = surrogateDiagTailX0RatChunk000Sub000Block185Part003

theorem surrogateDiagonalTailChunk000Sub000Block185Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block185Part003CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block185Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block185Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block185Part003CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block185Part003SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block185Part003] using hcert

def TailChunk000Sub000Block185Part004SupportExplicit : Finset ℕ :=
  ([7663] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block185Part004 : ℚ :=
  (53908962625 : ℚ) / 7861224550975930368

def SurrogateDiagonalTailChunk000Sub000Block185Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7663
    = surrogateDiagTailX0RatChunk000Sub000Block185Part004

theorem surrogateDiagonalTailChunk000Sub000Block185Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block185Part004CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block185Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block185Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block185Part004CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block185Part004SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block185Part004] using hcert

def TailChunk000Sub000Block185Part005SupportExplicit : Finset ℕ :=
  ([7665] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block185Part005 : ℚ :=
  (377366560025 : ℚ) / 178357673366913024

def SurrogateDiagonalTailChunk000Sub000Block185Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7665
    = surrogateDiagTailX0RatChunk000Sub000Block185Part005

theorem surrogateDiagonalTailChunk000Sub000Block185Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block185Part005CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block185Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block185Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block185Part005CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block185Part005SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block185Part005] using hcert

def TailChunk000Sub000Block185Part006SupportExplicit : Finset ℕ :=
  ([7666] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block185Part006 : ℚ :=
  (229560765625 : ℚ) / 134793474855670272

def SurrogateDiagonalTailChunk000Sub000Block185Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7666
    = surrogateDiagTailX0RatChunk000Sub000Block185Part006

theorem surrogateDiagonalTailChunk000Sub000Block185Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block185Part006CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block185Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block185Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block185Part006CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block185Part006SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block185Part006] using hcert

def TailChunk000Sub000Block185Part007SupportExplicit : Finset ℕ :=
  ([7667] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block185Part007 : ℚ :=
  (2796790901 : ℚ) / 33561142886400000

def SurrogateDiagonalTailChunk000Sub000Block185Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7667
    = surrogateDiagTailX0RatChunk000Sub000Block185Part007

theorem surrogateDiagonalTailChunk000Sub000Block185Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block185Part007CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block185Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block185Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block185Part007CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block185Part007SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block185Part007] using hcert

def TailChunk000Sub000Block185Part008SupportExplicit : Finset ℕ :=
  ([7669] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block185Part008 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub000Block185Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7669
    = surrogateDiagTailX0RatChunk000Sub000Block185Part008

theorem surrogateDiagonalTailChunk000Sub000Block185Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block185Part008CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block185Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block185Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block185Part008CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block185Part008SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block185Part008] using hcert

def TailChunk000Sub000Block185Part009SupportExplicit : Finset ℕ :=
  ([7670] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block185Part009 : ℚ :=
  (249282886475 : ℚ) / 50070569136685056

def SurrogateDiagonalTailChunk000Sub000Block185Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7670
    = surrogateDiagTailX0RatChunk000Sub000Block185Part009

theorem surrogateDiagonalTailChunk000Sub000Block185Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block185Part009CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block185Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block185Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block185Part009CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block185Part009SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block185Part009] using hcert

def TailChunk000Sub000Block185Part010SupportExplicit : Finset ℕ :=
  ([7671] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block185Part010 : ℚ :=
  (408551770475 : ℚ) / 853808047353897984

def SurrogateDiagonalTailChunk000Sub000Block185Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7671
    = surrogateDiagTailX0RatChunk000Sub000Block185Part010

theorem surrogateDiagonalTailChunk000Sub000Block185Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block185Part010CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block185Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block185Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block185Part010CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block185Part010SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block185Part010] using hcert

def TailChunk000Sub000Block185Part011SupportExplicit : Finset ℕ :=
  ([7673] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block185Part011 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub000Block185Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7673
    = surrogateDiagTailX0RatChunk000Sub000Block185Part011

theorem surrogateDiagonalTailChunk000Sub000Block185Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block185Part011CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block185Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block185Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block185Part011CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block185Part011SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block185Part011] using hcert

def TailChunk000Sub000Block185Part012SupportExplicit : Finset ℕ :=
  ([7674] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block185Part012 : ℚ :=
  (10074775025 : ℚ) / 1503183181961088

def SurrogateDiagonalTailChunk000Sub000Block185Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7674
    = surrogateDiagTailX0RatChunk000Sub000Block185Part012

theorem surrogateDiagonalTailChunk000Sub000Block185Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block185Part012CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block185Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block185Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block185Part012CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block185Part012SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block185Part012] using hcert

def TailChunk000Sub000Block185Part013SupportExplicit : Finset ℕ :=
  ([7678] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block185Part013 : ℚ :=
  (17171513771 : ℚ) / 7334556025881600

def SurrogateDiagonalTailChunk000Sub000Block185Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7678
    = surrogateDiagTailX0RatChunk000Sub000Block185Part013

theorem surrogateDiagonalTailChunk000Sub000Block185Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block185Part013CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block185Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block185Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block185Part013CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block185Part013SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block185Part013] using hcert

def TailChunk000Sub000Block185Part014SupportExplicit : Finset ℕ :=
  ([7679] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block185Part014 : ℚ :=
  (376953921775 : ℚ) / 4675995418926809088

def SurrogateDiagonalTailChunk000Sub000Block185Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7679
    = surrogateDiagTailX0RatChunk000Sub000Block185Part014

theorem surrogateDiagonalTailChunk000Sub000Block185Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block185Part014CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block185Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block185Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block185Part014CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block185Part014SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block185Part014] using hcert

def TailChunk000Sub000Block185Part015SupportExplicit : Finset ℕ :=
  ([7681] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block185Part015 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub000Block185Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7681
    = surrogateDiagTailX0RatChunk000Sub000Block185Part015

theorem surrogateDiagonalTailChunk000Sub000Block185Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block185Part015CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block185Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block185Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block185Part015CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block185Part015SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block185Part015] using hcert

def TailChunk000Sub000Block185Part016SupportExplicit : Finset ℕ :=
  ([7682] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block185Part016 : ℚ :=
  (40399485175 : ℚ) / 20217490769936064

def SurrogateDiagonalTailChunk000Sub000Block185Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7682
    = surrogateDiagTailX0RatChunk000Sub000Block185Part016

theorem surrogateDiagonalTailChunk000Sub000Block185Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block185Part016CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block185Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block185Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block185Part016CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block185Part016SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block185Part016] using hcert

def TailChunk000Sub000Block185Part017SupportExplicit : Finset ℕ :=
  ([7683] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block185Part017 : ℚ :=
  (811672890625 : ℚ) / 1224323290303561728

def SurrogateDiagonalTailChunk000Sub000Block185Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7683
    = surrogateDiagTailX0RatChunk000Sub000Block185Part017

theorem surrogateDiagonalTailChunk000Sub000Block185Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block185Part017CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block185Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block185Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block185Part017CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block185Part017SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block185Part017] using hcert

def TailChunk000Sub000Block185Part018SupportExplicit : Finset ℕ :=
  ([7685] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block185Part018 : ℚ :=
  (247748638175 : ℚ) / 1438408790343942144

def SurrogateDiagonalTailChunk000Sub000Block185Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7685
    = surrogateDiagTailX0RatChunk000Sub000Block185Part018

theorem surrogateDiagonalTailChunk000Sub000Block185Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block185Part018CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block185Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block185Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block185Part018CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block185Part018SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block185Part018] using hcert

def TailChunk000Sub000Block185Part019SupportExplicit : Finset ℕ :=
  ([7687] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block185Part019 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub000Block185Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7687
    = surrogateDiagTailX0RatChunk000Sub000Block185Part019

theorem surrogateDiagonalTailChunk000Sub000Block185Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block185Part019CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block185Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block185Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block185Part019CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block185Part019SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block185Part019] using hcert

def TailChunk000Sub000Block185Part020SupportExplicit : Finset ℕ :=
  ([7689] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block185Part020 : ℚ :=
  (32673346159 : ℚ) / 46361638089523200

def SurrogateDiagonalTailChunk000Sub000Block185Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7689
    = surrogateDiagTailX0RatChunk000Sub000Block185Part020

theorem surrogateDiagonalTailChunk000Sub000Block185Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block185Part020CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block185Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block185Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block185Part020CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block185Part020SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block185Part020] using hcert

def TailChunk000Sub000Block185Part021SupportExplicit : Finset ℕ :=
  ([7690] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block185Part021 : ℚ :=
  (775541297125 : ℚ) / 222695634845564928

def SurrogateDiagonalTailChunk000Sub000Block185Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7690
    = surrogateDiagTailX0RatChunk000Sub000Block185Part021

theorem surrogateDiagonalTailChunk000Sub000Block185Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block185Part021CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block185Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block185Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block185Part021CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block185Part021SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block185Part021] using hcert

def TailChunk000Sub000Block185Part022SupportExplicit : Finset ℕ :=
  ([7691] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block185Part022 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub000Block185Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7691
    = surrogateDiagTailX0RatChunk000Sub000Block185Part022

theorem surrogateDiagonalTailChunk000Sub000Block185Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block185Part022CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block185Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block185Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block185Part022CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block185Part022SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block185Part022] using hcert

def TailChunk000Sub000Block185Part023SupportExplicit : Finset ℕ :=
  ([7694] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block185Part023 : ℚ :=
  (1849556139775 : ℚ) / 547096552992752328

def SurrogateDiagonalTailChunk000Sub000Block185Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7694
    = surrogateDiagTailX0RatChunk000Sub000Block185Part023

theorem surrogateDiagonalTailChunk000Sub000Block185Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block185Part023CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block185Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block185Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block185Part023CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block185Part023SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block185Part023] using hcert

def TailChunk000Sub000Block185Part024SupportExplicit : Finset ℕ :=
  ([7697] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block185Part024 : ℚ :=
  (197796896875 : ℚ) / 433941838459569216

def SurrogateDiagonalTailChunk000Sub000Block185Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7697
    = surrogateDiagTailX0RatChunk000Sub000Block185Part024

theorem surrogateDiagonalTailChunk000Sub000Block185Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block185Part024CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block185Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block185Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block185Part024CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block185Part024SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block185Part024] using hcert

def surrogateDiagonalTailChunk000Sub000Block185HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block185Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block185Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block185Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block185Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block185Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block185Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block185Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block185Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block185Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block185Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block185Head : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block185Part000
    + surrogateDiagTailX0RatChunk000Sub000Block185Part001
    + surrogateDiagTailX0RatChunk000Sub000Block185Part002
    + surrogateDiagTailX0RatChunk000Sub000Block185Part003
    + surrogateDiagTailX0RatChunk000Sub000Block185Part004
    + surrogateDiagTailX0RatChunk000Sub000Block185Part005
    + surrogateDiagTailX0RatChunk000Sub000Block185Part006
    + surrogateDiagTailX0RatChunk000Sub000Block185Part007
    + surrogateDiagTailX0RatChunk000Sub000Block185Part008
    + surrogateDiagTailX0RatChunk000Sub000Block185Part009

def surrogateDiagonalTailChunk000Sub000Block185MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block185Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block185Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block185Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block185Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block185Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block185Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block185Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block185Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block185Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block185Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block185Mid : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block185Part010
    + surrogateDiagTailX0RatChunk000Sub000Block185Part011
    + surrogateDiagTailX0RatChunk000Sub000Block185Part012
    + surrogateDiagTailX0RatChunk000Sub000Block185Part013
    + surrogateDiagTailX0RatChunk000Sub000Block185Part014
    + surrogateDiagTailX0RatChunk000Sub000Block185Part015
    + surrogateDiagTailX0RatChunk000Sub000Block185Part016
    + surrogateDiagTailX0RatChunk000Sub000Block185Part017
    + surrogateDiagTailX0RatChunk000Sub000Block185Part018
    + surrogateDiagTailX0RatChunk000Sub000Block185Part019

def surrogateDiagonalTailChunk000Sub000Block185TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block185Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block185Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block185Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block185Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block185Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block185Tail : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block185Part020
    + surrogateDiagTailX0RatChunk000Sub000Block185Part021
    + surrogateDiagTailX0RatChunk000Sub000Block185Part022
    + surrogateDiagTailX0RatChunk000Sub000Block185Part023
    + surrogateDiagTailX0RatChunk000Sub000Block185Part024

def surrogateDiagonalTailChunk000Sub000Block185Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub000Block185HeadSum X0
    + surrogateDiagonalTailChunk000Sub000Block185MidSum X0
    + surrogateDiagonalTailChunk000Sub000Block185TailSum X0

def surrogateDiagTailX0RatChunk000Sub000Block185 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block185Part000
    + surrogateDiagTailX0RatChunk000Sub000Block185Part001
    + surrogateDiagTailX0RatChunk000Sub000Block185Part002
    + surrogateDiagTailX0RatChunk000Sub000Block185Part003
    + surrogateDiagTailX0RatChunk000Sub000Block185Part004
    + surrogateDiagTailX0RatChunk000Sub000Block185Part005
    + surrogateDiagTailX0RatChunk000Sub000Block185Part006
    + surrogateDiagTailX0RatChunk000Sub000Block185Part007
    + surrogateDiagTailX0RatChunk000Sub000Block185Part008
    + surrogateDiagTailX0RatChunk000Sub000Block185Part009
    + surrogateDiagTailX0RatChunk000Sub000Block185Part010
    + surrogateDiagTailX0RatChunk000Sub000Block185Part011
    + surrogateDiagTailX0RatChunk000Sub000Block185Part012
    + surrogateDiagTailX0RatChunk000Sub000Block185Part013
    + surrogateDiagTailX0RatChunk000Sub000Block185Part014
    + surrogateDiagTailX0RatChunk000Sub000Block185Part015
    + surrogateDiagTailX0RatChunk000Sub000Block185Part016
    + surrogateDiagTailX0RatChunk000Sub000Block185Part017
    + surrogateDiagTailX0RatChunk000Sub000Block185Part018
    + surrogateDiagTailX0RatChunk000Sub000Block185Part019
    + surrogateDiagTailX0RatChunk000Sub000Block185Part020
    + surrogateDiagTailX0RatChunk000Sub000Block185Part021
    + surrogateDiagTailX0RatChunk000Sub000Block185Part022
    + surrogateDiagTailX0RatChunk000Sub000Block185Part023
    + surrogateDiagTailX0RatChunk000Sub000Block185Part024

theorem surrogateDiagTailX0RatChunk000Sub000Block185_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk000Sub000Block185Head + surrogateDiagTailX0RatChunk000Sub000Block185Mid + surrogateDiagTailX0RatChunk000Sub000Block185Tail =
      surrogateDiagTailX0RatChunk000Sub000Block185 := by
  unfold surrogateDiagTailX0RatChunk000Sub000Block185Head surrogateDiagTailX0RatChunk000Sub000Block185Mid surrogateDiagTailX0RatChunk000Sub000Block185Tail surrogateDiagTailX0RatChunk000Sub000Block185
  ring

def SurrogateDiagonalTailChunk000Sub000Block185HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block185HeadSum X0 = surrogateDiagTailX0RatChunk000Sub000Block185Head

def SurrogateDiagonalTailChunk000Sub000Block185MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block185MidSum X0 = surrogateDiagTailX0RatChunk000Sub000Block185Mid

def SurrogateDiagonalTailChunk000Sub000Block185TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block185TailSum X0 = surrogateDiagTailX0RatChunk000Sub000Block185Tail

theorem surrogateDiagonalTailChunk000Sub000Block185_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk000Sub000Block185HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk000Sub000Block185MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk000Sub000Block185TailCertificateAt X0) :
    surrogateDiagonalTailChunk000Sub000Block185Sum X0 = surrogateDiagTailX0RatChunk000Sub000Block185 := by
  unfold SurrogateDiagonalTailChunk000Sub000Block185HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk000Sub000Block185MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk000Sub000Block185TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk000Sub000Block185Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk000Sub000Block185_eq_head_add_mid_add_tail

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

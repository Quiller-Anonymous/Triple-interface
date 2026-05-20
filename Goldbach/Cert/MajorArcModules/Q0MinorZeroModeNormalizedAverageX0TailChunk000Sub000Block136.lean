import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0TailPilot25

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

open scoped BigOperators

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

/- Generated direct-term certificate blocks for tail chunk 000, subchunk 000, blocks [136,137). -/

/- Block 136 covers tail-support indices [3400,3425) and q from 5649 to 5689. -/

def TailChunk000Sub000Block136Part000SupportExplicit : Finset ℕ :=
  ([5649] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block136Part000 : ℚ :=
  (1112738036275 : ℚ) / 267479818102407168

def SurrogateDiagonalTailChunk000Sub000Block136Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5649
    = surrogateDiagTailX0RatChunk000Sub000Block136Part000

theorem surrogateDiagonalTailChunk000Sub000Block136Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block136Part000CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block136Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block136Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block136Part000CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block136Part000SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block136Part000] using hcert

def TailChunk000Sub000Block136Part001SupportExplicit : Finset ℕ :=
  ([5651] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block136Part001 : ℚ :=
  (31933801 : ℚ) / 40769992618050

def SurrogateDiagonalTailChunk000Sub000Block136Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5651
    = surrogateDiagTailX0RatChunk000Sub000Block136Part001

theorem surrogateDiagonalTailChunk000Sub000Block136Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block136Part001CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block136Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block136Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block136Part001CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block136Part001SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block136Part001] using hcert

def TailChunk000Sub000Block136Part002SupportExplicit : Finset ℕ :=
  ([5653] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block136Part002 : ℚ :=
  (499318890625 : ℚ) / 637933604690456352

def SurrogateDiagonalTailChunk000Sub000Block136Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5653
    = surrogateDiagTailX0RatChunk000Sub000Block136Part002

theorem surrogateDiagonalTailChunk000Sub000Block136Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block136Part002CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block136Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block136Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block136Part002CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block136Part002SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block136Part002] using hcert

def TailChunk000Sub000Block136Part003SupportExplicit : Finset ℕ :=
  ([5654] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block136Part003 : ℚ :=
  (17842346963 : ℚ) / 2147913144729600

def SurrogateDiagonalTailChunk000Sub000Block136Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5654
    = surrogateDiagTailX0RatChunk000Sub000Block136Part003

theorem surrogateDiagonalTailChunk000Sub000Block136Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block136Part003CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block136Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block136Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block136Part003CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block136Part003SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block136Part003] using hcert

def TailChunk000Sub000Block136Part004SupportExplicit : Finset ℕ :=
  ([5655] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block136Part004 : ℚ :=
  (198901619275 : ℚ) / 32635023148449792

def SurrogateDiagonalTailChunk000Sub000Block136Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5655
    = surrogateDiagTailX0RatChunk000Sub000Block136Part004

theorem surrogateDiagonalTailChunk000Sub000Block136Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block136Part004CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block136Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block136Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block136Part004CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block136Part004SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block136Part004] using hcert

def TailChunk000Sub000Block136Part005SupportExplicit : Finset ℕ :=
  ([5657] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block136Part005 : ℚ :=
  (500025765625 : ℚ) / 639741421070234112

def SurrogateDiagonalTailChunk000Sub000Block136Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5657
    = surrogateDiagTailX0RatChunk000Sub000Block136Part005

theorem surrogateDiagonalTailChunk000Sub000Block136Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block136Part005CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block136Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block136Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block136Part005CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block136Part005SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block136Part005] using hcert

def TailChunk000Sub000Block136Part006SupportExplicit : Finset ℕ :=
  ([5658] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block136Part006 : ℚ :=
  (22757966641 : ℚ) / 959704478515200

def SurrogateDiagonalTailChunk000Sub000Block136Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5658
    = surrogateDiagTailX0RatChunk000Sub000Block136Part006

theorem surrogateDiagonalTailChunk000Sub000Block136Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block136Part006CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block136Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block136Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block136Part006CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block136Part006SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block136Part006] using hcert

def TailChunk000Sub000Block136Part007SupportExplicit : Finset ℕ :=
  ([5659] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block136Part007 : ℚ :=
  (500379390625 : ℚ) / 640646768773818162

def SurrogateDiagonalTailChunk000Sub000Block136Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5659
    = surrogateDiagTailX0RatChunk000Sub000Block136Part007

theorem surrogateDiagonalTailChunk000Sub000Block136Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block136Part007CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block136Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block136Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block136Part007CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block136Part007SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block136Part007] using hcert

def TailChunk000Sub000Block136Part008SupportExplicit : Finset ℕ :=
  ([5662] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block136Part008 : ℚ :=
  (312227391625 : ℚ) / 41980005017819136

def SurrogateDiagonalTailChunk000Sub000Block136Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5662
    = surrogateDiagTailX0RatChunk000Sub000Block136Part008

theorem surrogateDiagonalTailChunk000Sub000Block136Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block136Part008CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block136Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block136Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block136Part008CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block136Part008SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block136Part008] using hcert

def TailChunk000Sub000Block136Part009SupportExplicit : Finset ℕ :=
  ([5663] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block136Part009 : ℚ :=
  (1675162600375 : ℚ) / 1381265942035857408

def SurrogateDiagonalTailChunk000Sub000Block136Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5663
    = surrogateDiagTailX0RatChunk000Sub000Block136Part009

theorem surrogateDiagonalTailChunk000Sub000Block136Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block136Part009CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block136Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block136Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block136Part009CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block136Part009SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block136Part009] using hcert

def TailChunk000Sub000Block136Part010SupportExplicit : Finset ℕ :=
  ([5665] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block136Part010 : ℚ :=
  (852821299 : ℚ) / 433059458572800

def SurrogateDiagonalTailChunk000Sub000Block136Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5665
    = surrogateDiagTailX0RatChunk000Sub000Block136Part010

theorem surrogateDiagonalTailChunk000Sub000Block136Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block136Part010CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block136Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block136Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block136Part010CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block136Part010SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block136Part010] using hcert

def TailChunk000Sub000Block136Part011SupportExplicit : Finset ℕ :=
  ([5666] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block136Part011 : ℚ :=
  (1003035477775 : ℚ) / 160842144521945088

def SurrogateDiagonalTailChunk000Sub000Block136Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5666
    = surrogateDiagTailX0RatChunk000Sub000Block136Part011

theorem surrogateDiagonalTailChunk000Sub000Block136Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block136Part011CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block136Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block136Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block136Part011CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block136Part011SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block136Part011] using hcert

def TailChunk000Sub000Block136Part012SupportExplicit : Finset ℕ :=
  ([5667] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block136Part012 : ℚ :=
  (133732875 : ℚ) / 50823895711744

def SurrogateDiagonalTailChunk000Sub000Block136Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5667
    = surrogateDiagTailX0RatChunk000Sub000Block136Part012

theorem surrogateDiagonalTailChunk000Sub000Block136Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block136Part012CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block136Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block136Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block136Part012CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block136Part012SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block136Part012] using hcert

def TailChunk000Sub000Block136Part013SupportExplicit : Finset ℕ :=
  ([5669] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block136Part013 : ℚ :=
  (502149390625 : ℚ) / 645187929594922272

def SurrogateDiagonalTailChunk000Sub000Block136Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5669
    = surrogateDiagTailX0RatChunk000Sub000Block136Part013

theorem surrogateDiagonalTailChunk000Sub000Block136Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block136Part013CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block136Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block136Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block136Part013CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block136Part013SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block136Part013] using hcert

def TailChunk000Sub000Block136Part014SupportExplicit : Finset ℕ :=
  ([5671] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block136Part014 : ℚ :=
  (973881052325 : ℚ) / 1154074111214429184

def SurrogateDiagonalTailChunk000Sub000Block136Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5671
    = surrogateDiagTailX0RatChunk000Sub000Block136Part014

theorem surrogateDiagonalTailChunk000Sub000Block136Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block136Part014CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block136Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block136Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block136Part014CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block136Part014SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block136Part014] using hcert

def TailChunk000Sub000Block136Part015SupportExplicit : Finset ℕ :=
  ([5673] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block136Part015 : ℚ :=
  (5640022729 : ℚ) / 1866613248000000

def SurrogateDiagonalTailChunk000Sub000Block136Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5673
    = surrogateDiagTailX0RatChunk000Sub000Block136Part015

theorem surrogateDiagonalTailChunk000Sub000Block136Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block136Part015CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block136Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block136Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block136Part015CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block136Part015SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block136Part015] using hcert

def TailChunk000Sub000Block136Part016SupportExplicit : Finset ℕ :=
  ([5674] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block136Part016 : ℚ :=
  (1005869910775 : ℚ) / 161752784255073408

def SurrogateDiagonalTailChunk000Sub000Block136Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5674
    = surrogateDiagTailX0RatChunk000Sub000Block136Part016

theorem surrogateDiagonalTailChunk000Sub000Block136Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block136Part016CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block136Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block136Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block136Part016CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block136Part016SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block136Part016] using hcert

def TailChunk000Sub000Block136Part017SupportExplicit : Finset ℕ :=
  ([5677] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block136Part017 : ℚ :=
  (3821999 : ℚ) / 21527665172100

def SurrogateDiagonalTailChunk000Sub000Block136Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5677
    = surrogateDiagTailX0RatChunk000Sub000Block136Part017

theorem surrogateDiagonalTailChunk000Sub000Block136Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block136Part017CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block136Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block136Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block136Part017CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block136Part017SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block136Part017] using hcert

def TailChunk000Sub000Block136Part018SupportExplicit : Finset ℕ :=
  ([5678] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block136Part018 : ℚ :=
  (164716069125 : ℚ) / 41478007610146816

def SurrogateDiagonalTailChunk000Sub000Block136Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5678
    = surrogateDiagTailX0RatChunk000Sub000Block136Part018

theorem surrogateDiagonalTailChunk000Sub000Block136Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block136Part018CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block136Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block136Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block136Part018CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block136Part018SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block136Part018] using hcert

def TailChunk000Sub000Block136Part019SupportExplicit : Finset ℕ :=
  ([5681] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block136Part019 : ℚ :=
  (83155780325 : ℚ) / 425021923138830336

def SurrogateDiagonalTailChunk000Sub000Block136Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5681
    = surrogateDiagTailX0RatChunk000Sub000Block136Part019

theorem surrogateDiagonalTailChunk000Sub000Block136Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block136Part019CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block136Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block136Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block136Part019CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block136Part019SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block136Part019] using hcert

def TailChunk000Sub000Block136Part020SupportExplicit : Finset ℕ :=
  ([5682] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block136Part020 : ℚ :=
  (134362275 : ℚ) / 6406997176448

def SurrogateDiagonalTailChunk000Sub000Block136Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5682
    = surrogateDiagTailX0RatChunk000Sub000Block136Part020

theorem surrogateDiagonalTailChunk000Sub000Block136Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block136Part020CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block136Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block136Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block136Part020CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block136Part020SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block136Part020] using hcert

def TailChunk000Sub000Block136Part021SupportExplicit : Finset ℕ :=
  ([5683] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block136Part021 : ℚ :=
  (504632640625 : ℚ) / 651586060963571922

def SurrogateDiagonalTailChunk000Sub000Block136Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5683
    = surrogateDiagTailX0RatChunk000Sub000Block136Part021

theorem surrogateDiagonalTailChunk000Sub000Block136Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block136Part021CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block136Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block136Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block136Part021CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block136Part021SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block136Part021] using hcert

def TailChunk000Sub000Block136Part022SupportExplicit : Finset ℕ :=
  ([5685] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block136Part022 : ℚ :=
  (75461893475 : ℚ) / 14935713370324992

def SurrogateDiagonalTailChunk000Sub000Block136Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5685
    = surrogateDiagTailX0RatChunk000Sub000Block136Part022

theorem surrogateDiagonalTailChunk000Sub000Block136Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block136Part022CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block136Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block136Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block136Part022CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block136Part022SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block136Part022] using hcert

def TailChunk000Sub000Block136Part023SupportExplicit : Finset ℕ :=
  ([5686] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block136Part023 : ℚ :=
  (1010129058775 : ℚ) / 163125987316968648

def SurrogateDiagonalTailChunk000Sub000Block136Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5686
    = surrogateDiagTailX0RatChunk000Sub000Block136Part023

theorem surrogateDiagonalTailChunk000Sub000Block136Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block136Part023CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block136Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block136Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block136Part023CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block136Part023SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block136Part023] using hcert

def TailChunk000Sub000Block136Part024SupportExplicit : Finset ℕ :=
  ([5689] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block136Part024 : ℚ :=
  (505698765625 : ℚ) / 654342634847457792

def SurrogateDiagonalTailChunk000Sub000Block136Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5689
    = surrogateDiagTailX0RatChunk000Sub000Block136Part024

theorem surrogateDiagonalTailChunk000Sub000Block136Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block136Part024CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block136Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block136Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block136Part024CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block136Part024SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block136Part024] using hcert

def surrogateDiagonalTailChunk000Sub000Block136HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block136Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block136Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block136Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block136Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block136Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block136Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block136Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block136Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block136Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block136Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block136Head : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block136Part000
    + surrogateDiagTailX0RatChunk000Sub000Block136Part001
    + surrogateDiagTailX0RatChunk000Sub000Block136Part002
    + surrogateDiagTailX0RatChunk000Sub000Block136Part003
    + surrogateDiagTailX0RatChunk000Sub000Block136Part004
    + surrogateDiagTailX0RatChunk000Sub000Block136Part005
    + surrogateDiagTailX0RatChunk000Sub000Block136Part006
    + surrogateDiagTailX0RatChunk000Sub000Block136Part007
    + surrogateDiagTailX0RatChunk000Sub000Block136Part008
    + surrogateDiagTailX0RatChunk000Sub000Block136Part009

def surrogateDiagonalTailChunk000Sub000Block136MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block136Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block136Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block136Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block136Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block136Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block136Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block136Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block136Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block136Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block136Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block136Mid : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block136Part010
    + surrogateDiagTailX0RatChunk000Sub000Block136Part011
    + surrogateDiagTailX0RatChunk000Sub000Block136Part012
    + surrogateDiagTailX0RatChunk000Sub000Block136Part013
    + surrogateDiagTailX0RatChunk000Sub000Block136Part014
    + surrogateDiagTailX0RatChunk000Sub000Block136Part015
    + surrogateDiagTailX0RatChunk000Sub000Block136Part016
    + surrogateDiagTailX0RatChunk000Sub000Block136Part017
    + surrogateDiagTailX0RatChunk000Sub000Block136Part018
    + surrogateDiagTailX0RatChunk000Sub000Block136Part019

def surrogateDiagonalTailChunk000Sub000Block136TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block136Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block136Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block136Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block136Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block136Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block136Tail : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block136Part020
    + surrogateDiagTailX0RatChunk000Sub000Block136Part021
    + surrogateDiagTailX0RatChunk000Sub000Block136Part022
    + surrogateDiagTailX0RatChunk000Sub000Block136Part023
    + surrogateDiagTailX0RatChunk000Sub000Block136Part024

def surrogateDiagonalTailChunk000Sub000Block136Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub000Block136HeadSum X0
    + surrogateDiagonalTailChunk000Sub000Block136MidSum X0
    + surrogateDiagonalTailChunk000Sub000Block136TailSum X0

def surrogateDiagTailX0RatChunk000Sub000Block136 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block136Part000
    + surrogateDiagTailX0RatChunk000Sub000Block136Part001
    + surrogateDiagTailX0RatChunk000Sub000Block136Part002
    + surrogateDiagTailX0RatChunk000Sub000Block136Part003
    + surrogateDiagTailX0RatChunk000Sub000Block136Part004
    + surrogateDiagTailX0RatChunk000Sub000Block136Part005
    + surrogateDiagTailX0RatChunk000Sub000Block136Part006
    + surrogateDiagTailX0RatChunk000Sub000Block136Part007
    + surrogateDiagTailX0RatChunk000Sub000Block136Part008
    + surrogateDiagTailX0RatChunk000Sub000Block136Part009
    + surrogateDiagTailX0RatChunk000Sub000Block136Part010
    + surrogateDiagTailX0RatChunk000Sub000Block136Part011
    + surrogateDiagTailX0RatChunk000Sub000Block136Part012
    + surrogateDiagTailX0RatChunk000Sub000Block136Part013
    + surrogateDiagTailX0RatChunk000Sub000Block136Part014
    + surrogateDiagTailX0RatChunk000Sub000Block136Part015
    + surrogateDiagTailX0RatChunk000Sub000Block136Part016
    + surrogateDiagTailX0RatChunk000Sub000Block136Part017
    + surrogateDiagTailX0RatChunk000Sub000Block136Part018
    + surrogateDiagTailX0RatChunk000Sub000Block136Part019
    + surrogateDiagTailX0RatChunk000Sub000Block136Part020
    + surrogateDiagTailX0RatChunk000Sub000Block136Part021
    + surrogateDiagTailX0RatChunk000Sub000Block136Part022
    + surrogateDiagTailX0RatChunk000Sub000Block136Part023
    + surrogateDiagTailX0RatChunk000Sub000Block136Part024

theorem surrogateDiagTailX0RatChunk000Sub000Block136_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk000Sub000Block136Head + surrogateDiagTailX0RatChunk000Sub000Block136Mid + surrogateDiagTailX0RatChunk000Sub000Block136Tail =
      surrogateDiagTailX0RatChunk000Sub000Block136 := by
  unfold surrogateDiagTailX0RatChunk000Sub000Block136Head surrogateDiagTailX0RatChunk000Sub000Block136Mid surrogateDiagTailX0RatChunk000Sub000Block136Tail surrogateDiagTailX0RatChunk000Sub000Block136
  ring

def SurrogateDiagonalTailChunk000Sub000Block136HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block136HeadSum X0 = surrogateDiagTailX0RatChunk000Sub000Block136Head

def SurrogateDiagonalTailChunk000Sub000Block136MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block136MidSum X0 = surrogateDiagTailX0RatChunk000Sub000Block136Mid

def SurrogateDiagonalTailChunk000Sub000Block136TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block136TailSum X0 = surrogateDiagTailX0RatChunk000Sub000Block136Tail

theorem surrogateDiagonalTailChunk000Sub000Block136_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk000Sub000Block136HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk000Sub000Block136MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk000Sub000Block136TailCertificateAt X0) :
    surrogateDiagonalTailChunk000Sub000Block136Sum X0 = surrogateDiagTailX0RatChunk000Sub000Block136 := by
  unfold SurrogateDiagonalTailChunk000Sub000Block136HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk000Sub000Block136MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk000Sub000Block136TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk000Sub000Block136Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk000Sub000Block136_eq_head_add_mid_add_tail

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

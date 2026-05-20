import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0TailPilot25

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

open scoped BigOperators

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

/- Generated direct-term certificate blocks for tail chunk 000, subchunk 000, blocks [16,17). -/

/- Block 016 covers tail-support indices [400,425) and q from 706 to 749. -/

def TailChunk000Sub000Block016Part000SupportExplicit : Finset ℕ :=
  ([706] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block016Part000 : ℚ :=
  (108749389525 : ℚ) / 38388179140608

def SurrogateDiagonalTailChunk000Sub000Block016Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 706
    = surrogateDiagTailX0RatChunk000Sub000Block016Part000

theorem surrogateDiagonalTailChunk000Sub000Block016Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block016Part000CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block016Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block016Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block016Part000CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block016Part000SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block016Part000] using hcert

def TailChunk000Sub000Block016Part001SupportExplicit : Finset ℕ :=
  ([707] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block016Part001 : ℚ :=
  (3725362523 : ℚ) / 6481296000000

def SurrogateDiagonalTailChunk000Sub000Block016Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 707
    = surrogateDiagTailX0RatChunk000Sub000Block016Part001

theorem surrogateDiagonalTailChunk000Sub000Block016Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block016Part001CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block016Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block016Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block016Part001CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block016Part001SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block016Part001] using hcert

def TailChunk000Sub000Block016Part002SupportExplicit : Finset ℕ :=
  ([709] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block016Part002 : ℚ :=
  (219659029975 : ℚ) / 628289627038848

def SurrogateDiagonalTailChunk000Sub000Block016Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 709
    = surrogateDiagTailX0RatChunk000Sub000Block016Part002

theorem surrogateDiagonalTailChunk000Sub000Block016Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block016Part002CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block016Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block016Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block016Part002CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block016Part002SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block016Part002] using hcert

def TailChunk000Sub000Block016Part003SupportExplicit : Finset ℕ :=
  ([710] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block016Part003 : ℚ :=
  (3551057 : ℚ) / 627325440

def SurrogateDiagonalTailChunk000Sub000Block016Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 710
    = surrogateDiagTailX0RatChunk000Sub000Block016Part003

theorem surrogateDiagonalTailChunk000Sub000Block016Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block016Part003CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block016Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block016Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block016Part003CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block016Part003SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block016Part003] using hcert

def TailChunk000Sub000Block016Part004SupportExplicit : Finset ℕ :=
  ([713] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block016Part004 : ℚ :=
  (1647364397 : ℚ) / 3795706189440

def SurrogateDiagonalTailChunk000Sub000Block016Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 713
    = surrogateDiagTailX0RatChunk000Sub000Block016Part004

theorem surrogateDiagonalTailChunk000Sub000Block016Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block016Part004CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block016Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block016Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block016Part004CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block016Part004SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block016Part004] using hcert

def TailChunk000Sub000Block016Part005SupportExplicit : Finset ℕ :=
  ([714] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block016Part005 : ℚ :=
  (3998425 : ℚ) / 226492416

def SurrogateDiagonalTailChunk000Sub000Block016Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 714
    = surrogateDiagTailX0RatChunk000Sub000Block016Part005

theorem surrogateDiagonalTailChunk000Sub000Block016Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block016Part005CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block016Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block016Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block016Part005CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block016Part005SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block016Part005] using hcert

def TailChunk000Sub000Block016Part006SupportExplicit : Finset ℕ :=
  ([715] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block016Part006 : ℚ :=
  (600719119 : ℚ) / 530947768320

def SurrogateDiagonalTailChunk000Sub000Block016Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 715
    = surrogateDiagTailX0RatChunk000Sub000Block016Part006

theorem surrogateDiagonalTailChunk000Sub000Block016Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block016Part006CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block016Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block016Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block016Part006CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block016Part006SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block016Part006] using hcert

def TailChunk000Sub000Block016Part007SupportExplicit : Finset ℕ :=
  ([717] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block016Part007 : ℚ :=
  (72900626525 : ℚ) / 64183688890944

def SurrogateDiagonalTailChunk000Sub000Block016Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 717
    = surrogateDiagTailX0RatChunk000Sub000Block016Part007

theorem surrogateDiagonalTailChunk000Sub000Block016Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block016Part007CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block016Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block016Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block016Part007CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block016Part007SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block016Part007] using hcert

def TailChunk000Sub000Block016Part008SupportExplicit : Finset ℕ :=
  ([718] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block016Part008 : ℚ :=
  (112477670725 : ℚ) / 41073240245448

def SurrogateDiagonalTailChunk000Sub000Block016Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 718
    = surrogateDiagTailX0RatChunk000Sub000Block016Part008

theorem surrogateDiagonalTailChunk000Sub000Block016Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block016Part008CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block016Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block016Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block016Part008CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block016Part008SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block016Part008] using hcert

def TailChunk000Sub000Block016Part009SupportExplicit : Finset ℕ :=
  ([719] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block016Part009 : ℚ :=
  (225899032975 : ℚ) / 664545368937288

def SurrogateDiagonalTailChunk000Sub000Block016Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 719
    = surrogateDiagTailX0RatChunk000Sub000Block016Part009

theorem surrogateDiagonalTailChunk000Sub000Block016Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block016Part009CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block016Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block016Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block016Part009CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block016Part009SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block016Part009] using hcert

def TailChunk000Sub000Block016Part010SupportExplicit : Finset ℕ :=
  ([721] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block016Part010 : ℚ :=
  (192417710425 : ℚ) / 350778161443968

def SurrogateDiagonalTailChunk000Sub000Block016Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 721
    = surrogateDiagTailX0RatChunk000Sub000Block016Part010

theorem surrogateDiagonalTailChunk000Sub000Block016Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block016Part010CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block016Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block016Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block016Part010CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block016Part010SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block016Part010] using hcert

def TailChunk000Sub000Block016Part011SupportExplicit : Finset ℕ :=
  ([723] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block016Part011 : ℚ :=
  (20243 : ℚ) / 17694720

def SurrogateDiagonalTailChunk000Sub000Block016Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 723
    = surrogateDiagTailX0RatChunk000Sub000Block016Part011

theorem surrogateDiagonalTailChunk000Sub000Block016Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block016Part011CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block016Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block016Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block016Part011CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block016Part011SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block016Part011] using hcert

def TailChunk000Sub000Block016Part012SupportExplicit : Finset ℕ :=
  ([727] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block016Part012 : ℚ :=
  (20995814525 : ℚ) / 63151061726808

def SurrogateDiagonalTailChunk000Sub000Block016Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 727
    = surrogateDiagTailX0RatChunk000Sub000Block016Part012

theorem surrogateDiagonalTailChunk000Sub000Block016Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block016Part012CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block016Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block016Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block016Part012CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block016Part012SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block016Part012] using hcert

def TailChunk000Sub000Block016Part013SupportExplicit : Finset ℕ :=
  ([730] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block016Part013 : ℚ :=
  (91323634075 : ℚ) / 17202707693568

def SurrogateDiagonalTailChunk000Sub000Block016Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 730
    = surrogateDiagTailX0RatChunk000Sub000Block016Part013

theorem surrogateDiagonalTailChunk000Sub000Block016Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block016Part013CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block016Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block016Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block016Part013CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block016Part013SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block016Part013] using hcert

def TailChunk000Sub000Block016Part014SupportExplicit : Finset ℕ :=
  ([731] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block016Part014 : ℚ :=
  (107308814225 : ℚ) / 254961118347264

def SurrogateDiagonalTailChunk000Sub000Block016Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 731
    = surrogateDiagTailX0RatChunk000Sub000Block016Part014

theorem surrogateDiagonalTailChunk000Sub000Block016Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block016Part014CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block016Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block016Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block016Part014CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block016Part014SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block016Part014] using hcert

def TailChunk000Sub000Block016Part015SupportExplicit : Finset ℕ :=
  ([733] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block016Part015 : ℚ :=
  (2484961625 : ℚ) / 8863110507648

def SurrogateDiagonalTailChunk000Sub000Block016Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 733
    = surrogateDiagTailX0RatChunk000Sub000Block016Part015

theorem surrogateDiagonalTailChunk000Sub000Block016Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block016Part015CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block016Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block016Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block016Part015CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block016Part015SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block016Part015] using hcert

def TailChunk000Sub000Block016Part016SupportExplicit : Finset ℕ :=
  ([734] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block016Part016 : ℚ :=
  (117546457525 : ℚ) / 44869496944968

def SurrogateDiagonalTailChunk000Sub000Block016Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 734
    = surrogateDiagTailX0RatChunk000Sub000Block016Part016

theorem surrogateDiagonalTailChunk000Sub000Block016Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block016Part016CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block016Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block016Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block016Part016CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block016Part016SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block016Part016] using hcert

def TailChunk000Sub000Block016Part017SupportExplicit : Finset ℕ :=
  ([737] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block016Part017 : ℚ :=
  (8488403893 : ℚ) / 18978530947200

def SurrogateDiagonalTailChunk000Sub000Block016Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 737
    = surrogateDiagTailX0RatChunk000Sub000Block016Part017

theorem surrogateDiagonalTailChunk000Sub000Block016Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block016Part017CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block016Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block016Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block016Part017CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block016Part017SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block016Part017] using hcert

def TailChunk000Sub000Block016Part018SupportExplicit : Finset ℕ :=
  ([739] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block016Part018 : ℚ :=
  (238641223975 : ℚ) / 741741035383368

def SurrogateDiagonalTailChunk000Sub000Block016Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 739
    = surrogateDiagTailX0RatChunk000Sub000Block016Part018

theorem surrogateDiagonalTailChunk000Sub000Block016Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block016Part018CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block016Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block016Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block016Part018CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block016Part018SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block016Part018] using hcert

def TailChunk000Sub000Block016Part019SupportExplicit : Finset ℕ :=
  ([741] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block016Part019 : ℚ :=
  (136522760725 : ℚ) / 87088707698688

def SurrogateDiagonalTailChunk000Sub000Block016Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 741
    = surrogateDiagTailX0RatChunk000Sub000Block016Part019

theorem surrogateDiagonalTailChunk000Sub000Block016Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block016Part019CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block016Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block016Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block016Part019CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block016Part019SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block016Part019] using hcert

def TailChunk000Sub000Block016Part020SupportExplicit : Finset ℕ :=
  ([742] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block016Part020 : ℚ :=
  (11191409725 : ℚ) / 2632708196352

def SurrogateDiagonalTailChunk000Sub000Block016Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 742
    = surrogateDiagTailX0RatChunk000Sub000Block016Part020

theorem surrogateDiagonalTailChunk000Sub000Block016Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block016Part020CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block016Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block016Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block016Part020CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block016Part020SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block016Part020] using hcert

def TailChunk000Sub000Block016Part021SupportExplicit : Finset ℕ :=
  ([743] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block016Part021 : ℚ :=
  (34461658825 : ℚ) / 108279050799864

def SurrogateDiagonalTailChunk000Sub000Block016Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 743
    = surrogateDiagTailX0RatChunk000Sub000Block016Part021

theorem surrogateDiagonalTailChunk000Sub000Block016Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block016Part021CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block016Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block016Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block016Part021CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block016Part021SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block016Part021] using hcert

def TailChunk000Sub000Block016Part022SupportExplicit : Finset ℕ :=
  ([745] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block016Part022 : ℚ :=
  (770400675 : ℚ) / 1383441219584

def SurrogateDiagonalTailChunk000Sub000Block016Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 745
    = surrogateDiagTailX0RatChunk000Sub000Block016Part022

theorem surrogateDiagonalTailChunk000Sub000Block016Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block016Part022CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block016Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block016Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block016Part022CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block016Part022SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block016Part022] using hcert

def TailChunk000Sub000Block016Part023SupportExplicit : Finset ℕ :=
  ([746] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block016Part023 : ℚ :=
  (56385505475 : ℚ) / 23942451852864

def SurrogateDiagonalTailChunk000Sub000Block016Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 746
    = surrogateDiagTailX0RatChunk000Sub000Block016Part023

theorem surrogateDiagonalTailChunk000Sub000Block016Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block016Part023CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block016Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block016Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block016Part023CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block016Part023SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block016Part023] using hcert

def TailChunk000Sub000Block016Part024SupportExplicit : Finset ℕ :=
  ([749] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block016Part024 : ℚ :=
  (206953981525 : ℚ) / 409124343547008

def SurrogateDiagonalTailChunk000Sub000Block016Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 749
    = surrogateDiagTailX0RatChunk000Sub000Block016Part024

theorem surrogateDiagonalTailChunk000Sub000Block016Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block016Part024CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block016Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block016Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block016Part024CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block016Part024SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block016Part024] using hcert

def surrogateDiagonalTailChunk000Sub000Block016HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block016Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block016Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block016Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block016Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block016Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block016Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block016Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block016Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block016Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block016Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block016Head : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block016Part000
    + surrogateDiagTailX0RatChunk000Sub000Block016Part001
    + surrogateDiagTailX0RatChunk000Sub000Block016Part002
    + surrogateDiagTailX0RatChunk000Sub000Block016Part003
    + surrogateDiagTailX0RatChunk000Sub000Block016Part004
    + surrogateDiagTailX0RatChunk000Sub000Block016Part005
    + surrogateDiagTailX0RatChunk000Sub000Block016Part006
    + surrogateDiagTailX0RatChunk000Sub000Block016Part007
    + surrogateDiagTailX0RatChunk000Sub000Block016Part008
    + surrogateDiagTailX0RatChunk000Sub000Block016Part009

def surrogateDiagonalTailChunk000Sub000Block016MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block016Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block016Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block016Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block016Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block016Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block016Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block016Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block016Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block016Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block016Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block016Mid : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block016Part010
    + surrogateDiagTailX0RatChunk000Sub000Block016Part011
    + surrogateDiagTailX0RatChunk000Sub000Block016Part012
    + surrogateDiagTailX0RatChunk000Sub000Block016Part013
    + surrogateDiagTailX0RatChunk000Sub000Block016Part014
    + surrogateDiagTailX0RatChunk000Sub000Block016Part015
    + surrogateDiagTailX0RatChunk000Sub000Block016Part016
    + surrogateDiagTailX0RatChunk000Sub000Block016Part017
    + surrogateDiagTailX0RatChunk000Sub000Block016Part018
    + surrogateDiagTailX0RatChunk000Sub000Block016Part019

def surrogateDiagonalTailChunk000Sub000Block016TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block016Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block016Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block016Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block016Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block016Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block016Tail : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block016Part020
    + surrogateDiagTailX0RatChunk000Sub000Block016Part021
    + surrogateDiagTailX0RatChunk000Sub000Block016Part022
    + surrogateDiagTailX0RatChunk000Sub000Block016Part023
    + surrogateDiagTailX0RatChunk000Sub000Block016Part024

def surrogateDiagonalTailChunk000Sub000Block016Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub000Block016HeadSum X0
    + surrogateDiagonalTailChunk000Sub000Block016MidSum X0
    + surrogateDiagonalTailChunk000Sub000Block016TailSum X0

def surrogateDiagTailX0RatChunk000Sub000Block016 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block016Part000
    + surrogateDiagTailX0RatChunk000Sub000Block016Part001
    + surrogateDiagTailX0RatChunk000Sub000Block016Part002
    + surrogateDiagTailX0RatChunk000Sub000Block016Part003
    + surrogateDiagTailX0RatChunk000Sub000Block016Part004
    + surrogateDiagTailX0RatChunk000Sub000Block016Part005
    + surrogateDiagTailX0RatChunk000Sub000Block016Part006
    + surrogateDiagTailX0RatChunk000Sub000Block016Part007
    + surrogateDiagTailX0RatChunk000Sub000Block016Part008
    + surrogateDiagTailX0RatChunk000Sub000Block016Part009
    + surrogateDiagTailX0RatChunk000Sub000Block016Part010
    + surrogateDiagTailX0RatChunk000Sub000Block016Part011
    + surrogateDiagTailX0RatChunk000Sub000Block016Part012
    + surrogateDiagTailX0RatChunk000Sub000Block016Part013
    + surrogateDiagTailX0RatChunk000Sub000Block016Part014
    + surrogateDiagTailX0RatChunk000Sub000Block016Part015
    + surrogateDiagTailX0RatChunk000Sub000Block016Part016
    + surrogateDiagTailX0RatChunk000Sub000Block016Part017
    + surrogateDiagTailX0RatChunk000Sub000Block016Part018
    + surrogateDiagTailX0RatChunk000Sub000Block016Part019
    + surrogateDiagTailX0RatChunk000Sub000Block016Part020
    + surrogateDiagTailX0RatChunk000Sub000Block016Part021
    + surrogateDiagTailX0RatChunk000Sub000Block016Part022
    + surrogateDiagTailX0RatChunk000Sub000Block016Part023
    + surrogateDiagTailX0RatChunk000Sub000Block016Part024

theorem surrogateDiagTailX0RatChunk000Sub000Block016_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk000Sub000Block016Head + surrogateDiagTailX0RatChunk000Sub000Block016Mid + surrogateDiagTailX0RatChunk000Sub000Block016Tail =
      surrogateDiagTailX0RatChunk000Sub000Block016 := by
  unfold surrogateDiagTailX0RatChunk000Sub000Block016Head surrogateDiagTailX0RatChunk000Sub000Block016Mid surrogateDiagTailX0RatChunk000Sub000Block016Tail surrogateDiagTailX0RatChunk000Sub000Block016
  ring

def SurrogateDiagonalTailChunk000Sub000Block016HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block016HeadSum X0 = surrogateDiagTailX0RatChunk000Sub000Block016Head

def SurrogateDiagonalTailChunk000Sub000Block016MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block016MidSum X0 = surrogateDiagTailX0RatChunk000Sub000Block016Mid

def SurrogateDiagonalTailChunk000Sub000Block016TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block016TailSum X0 = surrogateDiagTailX0RatChunk000Sub000Block016Tail

theorem surrogateDiagonalTailChunk000Sub000Block016_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk000Sub000Block016HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk000Sub000Block016MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk000Sub000Block016TailCertificateAt X0) :
    surrogateDiagonalTailChunk000Sub000Block016Sum X0 = surrogateDiagTailX0RatChunk000Sub000Block016 := by
  unfold SurrogateDiagonalTailChunk000Sub000Block016HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk000Sub000Block016MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk000Sub000Block016TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk000Sub000Block016Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk000Sub000Block016_eq_head_add_mid_add_tail

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

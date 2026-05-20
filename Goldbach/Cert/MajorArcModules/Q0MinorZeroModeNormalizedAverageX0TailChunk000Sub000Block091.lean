import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0TailPilot25

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

open scoped BigOperators

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

/- Generated direct-term certificate blocks for tail chunk 000, subchunk 000, blocks [91,92). -/

/- Block 091 covers tail-support indices [2275,2300) and q from 3795 to 3833. -/

def TailChunk000Sub000Block091Part000SupportExplicit : Finset ℕ :=
  ([3795] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block091Part000 : ℚ :=
  (6478134079 : ℚ) / 239926119628800

def SurrogateDiagonalTailChunk000Sub000Block091Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3795
    = surrogateDiagTailX0RatChunk000Sub000Block091Part000

theorem surrogateDiagonalTailChunk000Sub000Block091Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block091Part000CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block091Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block091Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block091Part000CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block091Part000SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block091Part000] using hcert

def TailChunk000Sub000Block091Part001SupportExplicit : Finset ℕ :=
  ([3797] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block091Part001 : ℚ :=
  (225268890625 : ℚ) / 129799100421318432

def SurrogateDiagonalTailChunk000Sub000Block091Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3797
    = surrogateDiagTailX0RatChunk000Sub000Block091Part001

theorem surrogateDiagonalTailChunk000Sub000Block091Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block091Part001CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block091Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block091Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block091Part001CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block091Part001SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block091Part001] using hcert

def TailChunk000Sub000Block091Part002SupportExplicit : Finset ℕ :=
  ([3799] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block091Part002 : ℚ :=
  (350407171 : ℚ) / 175587010540032

def SurrogateDiagonalTailChunk000Sub000Block091Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3799
    = surrogateDiagTailX0RatChunk000Sub000Block091Part002

theorem surrogateDiagonalTailChunk000Sub000Block091Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block091Part002CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block091Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block091Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block091Part002CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block091Part002SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block091Part002] using hcert

def TailChunk000Sub000Block091Part003SupportExplicit : Finset ℕ :=
  ([3801] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block091Part003 : ℚ :=
  (914659597 : ℚ) / 80637692313600

def SurrogateDiagonalTailChunk000Sub000Block091Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3801
    = surrogateDiagTailX0RatChunk000Sub000Block091Part003

theorem surrogateDiagonalTailChunk000Sub000Block091Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block091Part003CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block091Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block091Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block091Part003CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block091Part003SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block091Part003] using hcert

def TailChunk000Sub000Block091Part004SupportExplicit : Finset ℕ :=
  ([3802] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block091Part004 : ℚ :=
  (18065391199 : ℚ) / 1303470642000000

def SurrogateDiagonalTailChunk000Sub000Block091Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3802
    = surrogateDiagTailX0RatChunk000Sub000Block091Part004

theorem surrogateDiagonalTailChunk000Sub000Block091Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block091Part004CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block091Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block091Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block091Part004CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block091Part004SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block091Part004] using hcert

def TailChunk000Sub000Block091Part005SupportExplicit : Finset ℕ :=
  ([3803] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block091Part005 : ℚ :=
  (225981390625 : ℚ) / 130621695791345202

def SurrogateDiagonalTailChunk000Sub000Block091Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3803
    = surrogateDiagTailX0RatChunk000Sub000Block091Part005

theorem surrogateDiagonalTailChunk000Sub000Block091Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block091Part005CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block091Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block091Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block091Part005CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block091Part005SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block091Part005] using hcert

def TailChunk000Sub000Block091Part006SupportExplicit : Finset ℕ :=
  ([3805] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block091Part006 : ℚ :=
  (2025317979 : ℚ) / 569495013294080

def SurrogateDiagonalTailChunk000Sub000Block091Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3805
    = surrogateDiagTailX0RatChunk000Sub000Block091Part006

theorem surrogateDiagonalTailChunk000Sub000Block091Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block091Part006CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block091Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block091Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block091Part006CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block091Part006SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block091Part006] using hcert

def TailChunk000Sub000Block091Part007SupportExplicit : Finset ℕ :=
  ([3806] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block091Part007 : ℚ :=
  (1211993519 : ℚ) / 43769404930560

def SurrogateDiagonalTailChunk000Sub000Block091Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3806
    = surrogateDiagTailX0RatChunk000Sub000Block091Part007

theorem surrogateDiagonalTailChunk000Sub000Block091Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block091Part007CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block091Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block091Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block091Part007CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block091Part007SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block091Part007] using hcert

def TailChunk000Sub000Block091Part008SupportExplicit : Finset ℕ :=
  ([3809] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block091Part008 : ℚ :=
  (71378124125 : ℚ) / 31412463923257344

def SurrogateDiagonalTailChunk000Sub000Block091Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3809
    = surrogateDiagTailX0RatChunk000Sub000Block091Part008

theorem surrogateDiagonalTailChunk000Sub000Block091Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block091Part008CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block091Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block091Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block091Part008CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block091Part008SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block091Part008] using hcert

def TailChunk000Sub000Block091Part009SupportExplicit : Finset ℕ :=
  ([3810] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block091Part009 : ℚ :=
  (3082962425 : ℚ) / 23902604845056

def SurrogateDiagonalTailChunk000Sub000Block091Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3810
    = surrogateDiagTailX0RatChunk000Sub000Block091Part009

theorem surrogateDiagonalTailChunk000Sub000Block091Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block091Part009CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block091Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block091Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block091Part009CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block091Part009SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block091Part009] using hcert

def TailChunk000Sub000Block091Part010SupportExplicit : Finset ℕ :=
  ([3811] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block091Part010 : ℚ :=
  (884601949075 : ℚ) / 454608497231382528

def SurrogateDiagonalTailChunk000Sub000Block091Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3811
    = surrogateDiagTailX0RatChunk000Sub000Block091Part010

theorem surrogateDiagonalTailChunk000Sub000Block091Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block091Part010CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block091Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block091Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block091Part010CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block091Part010SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block091Part010] using hcert

def TailChunk000Sub000Block091Part011SupportExplicit : Finset ℕ :=
  ([3813] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block091Part011 : ℚ :=
  (13439620361 : ℚ) / 1659211776000000

def SurrogateDiagonalTailChunk000Sub000Block091Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3813
    = surrogateDiagTailX0RatChunk000Sub000Block091Part011

theorem surrogateDiagonalTailChunk000Sub000Block091Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block091Part011CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block091Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block091Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block091Part011CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block091Part011SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block091Part011] using hcert

def TailChunk000Sub000Block091Part012SupportExplicit : Finset ℕ :=
  ([3814] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block091Part012 : ℚ :=
  (454490208775 : ℚ) / 33000342255941448

def SurrogateDiagonalTailChunk000Sub000Block091Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3814
    = surrogateDiagTailX0RatChunk000Sub000Block091Part012

theorem surrogateDiagonalTailChunk000Sub000Block091Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block091Part012CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block091Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block091Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block091Part012CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block091Part012SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block091Part012] using hcert

def TailChunk000Sub000Block091Part013SupportExplicit : Finset ℕ :=
  ([3815] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block091Part013 : ℚ :=
  (112556909875 : ℚ) / 18811160862916608

def SurrogateDiagonalTailChunk000Sub000Block091Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3815
    = surrogateDiagTailX0RatChunk000Sub000Block091Part013

theorem surrogateDiagonalTailChunk000Sub000Block091Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block091Part013CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block091Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block091Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block091Part013CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block091Part013SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block091Part013] using hcert

def TailChunk000Sub000Block091Part014SupportExplicit : Finset ℕ :=
  ([3817] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block091Part014 : ℚ :=
  (31941593429 : ℚ) / 7167393520065600

def SurrogateDiagonalTailChunk000Sub000Block091Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3817
    = surrogateDiagTailX0RatChunk000Sub000Block091Part014

theorem surrogateDiagonalTailChunk000Sub000Block091Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block091Part014CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block091Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block091Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block091Part014CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block091Part014SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block091Part014] using hcert

def TailChunk000Sub000Block091Part015SupportExplicit : Finset ℕ :=
  ([3818] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block091Part015 : ℚ :=
  (641047209625 : ℚ) / 26483354364390528

def SurrogateDiagonalTailChunk000Sub000Block091Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3818
    = surrogateDiagTailX0RatChunk000Sub000Block091Part015

theorem surrogateDiagonalTailChunk000Sub000Block091Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block091Part015CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block091Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block091Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block091Part015CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block091Part015SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block091Part015] using hcert

def TailChunk000Sub000Block091Part016SupportExplicit : Finset ℕ :=
  ([3819] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block091Part016 : ℚ :=
  (931364117425 : ℚ) / 79691610588530688

def SurrogateDiagonalTailChunk000Sub000Block091Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3819
    = surrogateDiagTailX0RatChunk000Sub000Block091Part016

theorem surrogateDiagonalTailChunk000Sub000Block091Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block091Part016CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block091Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block091Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block091Part016CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block091Part016SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block091Part016] using hcert

def TailChunk000Sub000Block091Part017SupportExplicit : Finset ℕ :=
  ([3821] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block091Part017 : ℚ :=
  (72985604959 : ℚ) / 21298072538755200

def SurrogateDiagonalTailChunk000Sub000Block091Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3821
    = surrogateDiagTailX0RatChunk000Sub000Block091Part017

theorem surrogateDiagonalTailChunk000Sub000Block091Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block091Part017CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block091Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block091Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block091Part017CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block091Part017SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block091Part017] using hcert

def TailChunk000Sub000Block091Part018SupportExplicit : Finset ℕ :=
  ([3823] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block091Part018 : ℚ :=
  (1826550741775 : ℚ) / 533567771825561928

def SurrogateDiagonalTailChunk000Sub000Block091Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3823
    = surrogateDiagTailX0RatChunk000Sub000Block091Part018

theorem surrogateDiagonalTailChunk000Sub000Block091Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block091Part018CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block091Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block091Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block091Part018CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block091Part018SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block091Part018] using hcert

def TailChunk000Sub000Block091Part019SupportExplicit : Finset ℕ :=
  ([3826] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block091Part019 : ℚ :=
  (457354635775 : ℚ) / 33417842715936768

def SurrogateDiagonalTailChunk000Sub000Block091Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3826
    = surrogateDiagTailX0RatChunk000Sub000Block091Part019

theorem surrogateDiagonalTailChunk000Sub000Block091Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block091Part019CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block091Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block091Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block091Part019CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block091Part019SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block091Part019] using hcert

def TailChunk000Sub000Block091Part020SupportExplicit : Finset ℕ :=
  ([3827] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block091Part020 : ℚ :=
  (447064595975 : ℚ) / 233305358357643264

def SurrogateDiagonalTailChunk000Sub000Block091Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3827
    = surrogateDiagTailX0RatChunk000Sub000Block091Part020

theorem surrogateDiagonalTailChunk000Sub000Block091Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block091Part020CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block091Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block091Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block091Part020CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block091Part020SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block091Part020] using hcert

def TailChunk000Sub000Block091Part021SupportExplicit : Finset ℕ :=
  ([3829] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block091Part021 : ℚ :=
  (821840147125 : ℚ) / 288006594038287488

def SurrogateDiagonalTailChunk000Sub000Block091Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3829
    = surrogateDiagTailX0RatChunk000Sub000Block091Part021

theorem surrogateDiagonalTailChunk000Sub000Block091Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block091Part021CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block091Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block091Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block091Part021CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block091Part021SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block091Part021] using hcert

def TailChunk000Sub000Block091Part022SupportExplicit : Finset ℕ :=
  ([3830] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block091Part022 : ℚ :=
  (98370282175 : ℚ) / 3407691606200832

def SurrogateDiagonalTailChunk000Sub000Block091Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3830
    = surrogateDiagTailX0RatChunk000Sub000Block091Part022

theorem surrogateDiagonalTailChunk000Sub000Block091Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block091Part022CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block091Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block091Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block091Part022CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block091Part022SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block091Part022] using hcert

def TailChunk000Sub000Block091Part023SupportExplicit : Finset ℕ :=
  ([3831] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block091Part023 : ℚ :=
  (713073893725 : ℚ) / 106059491135735808

def SurrogateDiagonalTailChunk000Sub000Block091Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3831
    = surrogateDiagTailX0RatChunk000Sub000Block091Part023

theorem surrogateDiagonalTailChunk000Sub000Block091Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block091Part023CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block091Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block091Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block091Part023CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block091Part023SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block091Part023] using hcert

def TailChunk000Sub000Block091Part024SupportExplicit : Finset ℕ :=
  ([3833] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block091Part024 : ℚ :=
  (229560765625 : ℚ) / 134793474855670272

def SurrogateDiagonalTailChunk000Sub000Block091Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3833
    = surrogateDiagTailX0RatChunk000Sub000Block091Part024

theorem surrogateDiagonalTailChunk000Sub000Block091Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block091Part024CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block091Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block091Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block091Part024CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block091Part024SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block091Part024] using hcert

def surrogateDiagonalTailChunk000Sub000Block091HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block091Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block091Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block091Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block091Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block091Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block091Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block091Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block091Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block091Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block091Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block091Head : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block091Part000
    + surrogateDiagTailX0RatChunk000Sub000Block091Part001
    + surrogateDiagTailX0RatChunk000Sub000Block091Part002
    + surrogateDiagTailX0RatChunk000Sub000Block091Part003
    + surrogateDiagTailX0RatChunk000Sub000Block091Part004
    + surrogateDiagTailX0RatChunk000Sub000Block091Part005
    + surrogateDiagTailX0RatChunk000Sub000Block091Part006
    + surrogateDiagTailX0RatChunk000Sub000Block091Part007
    + surrogateDiagTailX0RatChunk000Sub000Block091Part008
    + surrogateDiagTailX0RatChunk000Sub000Block091Part009

def surrogateDiagonalTailChunk000Sub000Block091MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block091Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block091Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block091Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block091Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block091Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block091Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block091Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block091Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block091Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block091Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block091Mid : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block091Part010
    + surrogateDiagTailX0RatChunk000Sub000Block091Part011
    + surrogateDiagTailX0RatChunk000Sub000Block091Part012
    + surrogateDiagTailX0RatChunk000Sub000Block091Part013
    + surrogateDiagTailX0RatChunk000Sub000Block091Part014
    + surrogateDiagTailX0RatChunk000Sub000Block091Part015
    + surrogateDiagTailX0RatChunk000Sub000Block091Part016
    + surrogateDiagTailX0RatChunk000Sub000Block091Part017
    + surrogateDiagTailX0RatChunk000Sub000Block091Part018
    + surrogateDiagTailX0RatChunk000Sub000Block091Part019

def surrogateDiagonalTailChunk000Sub000Block091TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block091Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block091Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block091Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block091Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block091Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block091Tail : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block091Part020
    + surrogateDiagTailX0RatChunk000Sub000Block091Part021
    + surrogateDiagTailX0RatChunk000Sub000Block091Part022
    + surrogateDiagTailX0RatChunk000Sub000Block091Part023
    + surrogateDiagTailX0RatChunk000Sub000Block091Part024

def surrogateDiagonalTailChunk000Sub000Block091Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub000Block091HeadSum X0
    + surrogateDiagonalTailChunk000Sub000Block091MidSum X0
    + surrogateDiagonalTailChunk000Sub000Block091TailSum X0

def surrogateDiagTailX0RatChunk000Sub000Block091 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block091Part000
    + surrogateDiagTailX0RatChunk000Sub000Block091Part001
    + surrogateDiagTailX0RatChunk000Sub000Block091Part002
    + surrogateDiagTailX0RatChunk000Sub000Block091Part003
    + surrogateDiagTailX0RatChunk000Sub000Block091Part004
    + surrogateDiagTailX0RatChunk000Sub000Block091Part005
    + surrogateDiagTailX0RatChunk000Sub000Block091Part006
    + surrogateDiagTailX0RatChunk000Sub000Block091Part007
    + surrogateDiagTailX0RatChunk000Sub000Block091Part008
    + surrogateDiagTailX0RatChunk000Sub000Block091Part009
    + surrogateDiagTailX0RatChunk000Sub000Block091Part010
    + surrogateDiagTailX0RatChunk000Sub000Block091Part011
    + surrogateDiagTailX0RatChunk000Sub000Block091Part012
    + surrogateDiagTailX0RatChunk000Sub000Block091Part013
    + surrogateDiagTailX0RatChunk000Sub000Block091Part014
    + surrogateDiagTailX0RatChunk000Sub000Block091Part015
    + surrogateDiagTailX0RatChunk000Sub000Block091Part016
    + surrogateDiagTailX0RatChunk000Sub000Block091Part017
    + surrogateDiagTailX0RatChunk000Sub000Block091Part018
    + surrogateDiagTailX0RatChunk000Sub000Block091Part019
    + surrogateDiagTailX0RatChunk000Sub000Block091Part020
    + surrogateDiagTailX0RatChunk000Sub000Block091Part021
    + surrogateDiagTailX0RatChunk000Sub000Block091Part022
    + surrogateDiagTailX0RatChunk000Sub000Block091Part023
    + surrogateDiagTailX0RatChunk000Sub000Block091Part024

theorem surrogateDiagTailX0RatChunk000Sub000Block091_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk000Sub000Block091Head + surrogateDiagTailX0RatChunk000Sub000Block091Mid + surrogateDiagTailX0RatChunk000Sub000Block091Tail =
      surrogateDiagTailX0RatChunk000Sub000Block091 := by
  unfold surrogateDiagTailX0RatChunk000Sub000Block091Head surrogateDiagTailX0RatChunk000Sub000Block091Mid surrogateDiagTailX0RatChunk000Sub000Block091Tail surrogateDiagTailX0RatChunk000Sub000Block091
  ring

def SurrogateDiagonalTailChunk000Sub000Block091HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block091HeadSum X0 = surrogateDiagTailX0RatChunk000Sub000Block091Head

def SurrogateDiagonalTailChunk000Sub000Block091MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block091MidSum X0 = surrogateDiagTailX0RatChunk000Sub000Block091Mid

def SurrogateDiagonalTailChunk000Sub000Block091TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block091TailSum X0 = surrogateDiagTailX0RatChunk000Sub000Block091Tail

theorem surrogateDiagonalTailChunk000Sub000Block091_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk000Sub000Block091HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk000Sub000Block091MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk000Sub000Block091TailCertificateAt X0) :
    surrogateDiagonalTailChunk000Sub000Block091Sum X0 = surrogateDiagTailX0RatChunk000Sub000Block091 := by
  unfold SurrogateDiagonalTailChunk000Sub000Block091HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk000Sub000Block091MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk000Sub000Block091TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk000Sub000Block091Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk000Sub000Block091_eq_head_add_mid_add_tail

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

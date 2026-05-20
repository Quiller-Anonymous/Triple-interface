import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0TailPilot25

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

open scoped BigOperators

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

/- Generated direct-term certificate blocks for tail chunk 000, subchunk 000, blocks [184,185). -/

/-- Block 184 covers tail-support indices [4600,4625) and q from 7618 to 7655. -/

def TailChunk000Sub000Block184Part000SupportExplicit : Finset ℕ :=
  ([7618] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block184Part000 : ℚ :=
  (71378124125 : ℚ) / 31412463923257344

def SurrogateDiagonalTailChunk000Sub000Block184Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7618
    = surrogateDiagTailX0RatChunk000Sub000Block184Part000

theorem surrogateDiagonalTailChunk000Sub000Block184Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block184Part000CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block184Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block184Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block184Part000CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block184Part000SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block184Part000] using hcert

def TailChunk000Sub000Block184Part001SupportExplicit : Finset ℕ :=
  ([7619] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block184Part001 : ℚ :=
  (134648055757 : ℚ) / 268792307712000000

def SurrogateDiagonalTailChunk000Sub000Block184Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7619
    = surrogateDiagTailX0RatChunk000Sub000Block184Part001

theorem surrogateDiagonalTailChunk000Sub000Block184Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block184Part001CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block184Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block184Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block184Part001CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block184Part001SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block184Part001] using hcert

def TailChunk000Sub000Block184Part002SupportExplicit : Finset ℕ :=
  ([7621] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block184Part002 : ℚ :=
  (1451991025 : ℚ) / 3372148842269472

def SurrogateDiagonalTailChunk000Sub000Block184Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7621
    = surrogateDiagTailX0RatChunk000Sub000Block184Part002

theorem surrogateDiagonalTailChunk000Sub000Block184Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block184Part002CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block184Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block184Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block184Part002CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block184Part002SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block184Part002] using hcert

def TailChunk000Sub000Block184Part003SupportExplicit : Finset ℕ :=
  ([7622] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block184Part003 : ℚ :=
  (884601949075 : ℚ) / 454608497231382528

def SurrogateDiagonalTailChunk000Sub000Block184Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7622
    = surrogateDiagTailX0RatChunk000Sub000Block184Part003

theorem surrogateDiagonalTailChunk000Sub000Block184Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block184Part003CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block184Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block184Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block184Part003CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block184Part003SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block184Part003] using hcert

def TailChunk000Sub000Block184Part004SupportExplicit : Finset ℕ :=
  ([7626] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block184Part004 : ℚ :=
  (13439620361 : ℚ) / 1659211776000000

def SurrogateDiagonalTailChunk000Sub000Block184Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7626
    = surrogateDiagTailX0RatChunk000Sub000Block184Part004

theorem surrogateDiagonalTailChunk000Sub000Block184Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block184Part004CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block184Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block184Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block184Part004CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block184Part004SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block184Part004] using hcert

def TailChunk000Sub000Block184Part005SupportExplicit : Finset ℕ :=
  ([7627] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block184Part005 : ℚ :=
  (164288702925 : ℚ) / 344861612706408448

def SurrogateDiagonalTailChunk000Sub000Block184Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7627
    = surrogateDiagTailX0RatChunk000Sub000Block184Part005

theorem surrogateDiagonalTailChunk000Sub000Block184Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block184Part005CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block184Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block184Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block184Part005CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block184Part005SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block184Part005] using hcert

def TailChunk000Sub000Block184Part006SupportExplicit : Finset ℕ :=
  ([7629] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block184Part006 : ℚ :=
  (505062303025 : ℚ) / 417627448704943392

def SurrogateDiagonalTailChunk000Sub000Block184Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7629
    = surrogateDiagTailX0RatChunk000Sub000Block184Part006

theorem surrogateDiagonalTailChunk000Sub000Block184Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block184Part006CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block184Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block184Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block184Part006CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block184Part006SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block184Part006] using hcert

def TailChunk000Sub000Block184Part007SupportExplicit : Finset ℕ :=
  ([7630] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block184Part007 : ℚ :=
  (112556909875 : ℚ) / 18811160862916608

def SurrogateDiagonalTailChunk000Sub000Block184Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7630
    = surrogateDiagTailX0RatChunk000Sub000Block184Part007

theorem surrogateDiagonalTailChunk000Sub000Block184Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block184Part007CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block184Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block184Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block184Part007CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block184Part007SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block184Part007] using hcert

def TailChunk000Sub000Block184Part008SupportExplicit : Finset ℕ :=
  ([7631] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block184Part008 : ℚ :=
  (204161907625 : ℚ) / 382139846210544768

def SurrogateDiagonalTailChunk000Sub000Block184Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7631
    = surrogateDiagTailX0RatChunk000Sub000Block184Part008

theorem surrogateDiagonalTailChunk000Sub000Block184Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block184Part008CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block184Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block184Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block184Part008CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block184Part008SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block184Part008] using hcert

def TailChunk000Sub000Block184Part009SupportExplicit : Finset ℕ :=
  ([7633] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block184Part009 : ℚ :=
  (139260957375 : ℚ) / 275047437893107712

def SurrogateDiagonalTailChunk000Sub000Block184Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7633
    = surrogateDiagTailX0RatChunk000Sub000Block184Part009

theorem surrogateDiagonalTailChunk000Sub000Block184Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block184Part009CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block184Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block184Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block184Part009CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block184Part009SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block184Part009] using hcert

def TailChunk000Sub000Block184Part010SupportExplicit : Finset ℕ :=
  ([7634] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block184Part010 : ℚ :=
  (31941593429 : ℚ) / 7167393520065600

def SurrogateDiagonalTailChunk000Sub000Block184Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7634
    = surrogateDiagTailX0RatChunk000Sub000Block184Part010

theorem surrogateDiagonalTailChunk000Sub000Block184Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block184Part010CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block184Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block184Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block184Part010CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block184Part010SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block184Part010] using hcert

def TailChunk000Sub000Block184Part011SupportExplicit : Finset ℕ :=
  ([7635] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block184Part011 : ℚ :=
  (759403311425 : ℚ) / 341044979208290304

def SurrogateDiagonalTailChunk000Sub000Block184Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7635
    = surrogateDiagTailX0RatChunk000Sub000Block184Part011

theorem surrogateDiagonalTailChunk000Sub000Block184Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block184Part011CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block184Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block184Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block184Part011CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block184Part011SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block184Part011] using hcert

def TailChunk000Sub000Block184Part012SupportExplicit : Finset ℕ :=
  ([7637] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block184Part012 : ℚ :=
  (6440691491 : ℚ) / 10165420269518400

def SurrogateDiagonalTailChunk000Sub000Block184Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7637
    = surrogateDiagTailX0RatChunk000Sub000Block184Part012

theorem surrogateDiagonalTailChunk000Sub000Block184Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block184Part012CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block184Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block184Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block184Part012CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block184Part012SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block184Part012] using hcert

def TailChunk000Sub000Block184Part013SupportExplicit : Finset ℕ :=
  ([7638] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block184Part013 : ℚ :=
  (931364117425 : ℚ) / 79691610588530688

def SurrogateDiagonalTailChunk000Sub000Block184Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7638
    = surrogateDiagTailX0RatChunk000Sub000Block184Part013

theorem surrogateDiagonalTailChunk000Sub000Block184Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block184Part013CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block184Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block184Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block184Part013CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block184Part013SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block184Part013] using hcert

def TailChunk000Sub000Block184Part014SupportExplicit : Finset ℕ :=
  ([7639] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block184Part014 : ℚ :=
  (911786265625 : ℚ) / 2127577964778064242

def SurrogateDiagonalTailChunk000Sub000Block184Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7639
    = surrogateDiagTailX0RatChunk000Sub000Block184Part014

theorem surrogateDiagonalTailChunk000Sub000Block184Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block184Part014CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block184Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block184Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block184Part014CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block184Part014SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block184Part014] using hcert

def TailChunk000Sub000Block184Part015SupportExplicit : Finset ℕ :=
  ([7642] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block184Part015 : ℚ :=
  (72985604959 : ℚ) / 21298072538755200

def SurrogateDiagonalTailChunk000Sub000Block184Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7642
    = surrogateDiagTailX0RatChunk000Sub000Block184Part015

theorem surrogateDiagonalTailChunk000Sub000Block184Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block184Part015CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block184Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block184Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block184Part015CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block184Part015SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block184Part015] using hcert

def TailChunk000Sub000Block184Part016SupportExplicit : Finset ℕ :=
  ([7643] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block184Part016 : ℚ :=
  (912741390625 : ℚ) / 2132038294411213362

def SurrogateDiagonalTailChunk000Sub000Block184Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7643
    = surrogateDiagTailX0RatChunk000Sub000Block184Part016

theorem surrogateDiagonalTailChunk000Sub000Block184Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block184Part016CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block184Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block184Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block184Part016CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block184Part016SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block184Part016] using hcert

def TailChunk000Sub000Block184Part017SupportExplicit : Finset ℕ :=
  ([7645] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block184Part017 : ℚ :=
  (5114611069 : ℚ) / 5159060917862400

def SurrogateDiagonalTailChunk000Sub000Block184Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7645
    = surrogateDiagTailX0RatChunk000Sub000Block184Part017

theorem surrogateDiagonalTailChunk000Sub000Block184Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block184Part017CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block184Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block184Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block184Part017CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block184Part017SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block184Part017] using hcert

def TailChunk000Sub000Block184Part018SupportExplicit : Finset ℕ :=
  ([7646] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block184Part018 : ℚ :=
  (1826550741775 : ℚ) / 533567771825561928

def SurrogateDiagonalTailChunk000Sub000Block184Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7646
    = surrogateDiagTailX0RatChunk000Sub000Block184Part018

theorem surrogateDiagonalTailChunk000Sub000Block184Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block184Part018CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block184Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block184Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block184Part018CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block184Part018SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block184Part018] using hcert

def TailChunk000Sub000Block184Part019SupportExplicit : Finset ℕ :=
  ([7647] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block184Part019 : ℚ :=
  (1014897244475 : ℚ) / 843168824613233664

def SurrogateDiagonalTailChunk000Sub000Block184Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7647
    = surrogateDiagTailX0RatChunk000Sub000Block184Part019

theorem surrogateDiagonalTailChunk000Sub000Block184Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block184Part019CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block184Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block184Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block184Part019CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block184Part019SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block184Part019] using hcert

def TailChunk000Sub000Block184Part020SupportExplicit : Finset ℕ :=
  ([7649] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block184Part020 : ℚ :=
  (914175015625 : ℚ) / 2138741933819953152

def SurrogateDiagonalTailChunk000Sub000Block184Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7649
    = surrogateDiagTailX0RatChunk000Sub000Block184Part020

theorem surrogateDiagonalTailChunk000Sub000Block184Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block184Part020CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block184Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block184Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block184Part020CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block184Part020SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block184Part020] using hcert

def TailChunk000Sub000Block184Part021SupportExplicit : Finset ℕ :=
  ([7651] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block184Part021 : ℚ :=
  (2983568647375 : ℚ) / 4608105504612599808

def SurrogateDiagonalTailChunk000Sub000Block184Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7651
    = surrogateDiagTailX0RatChunk000Sub000Block184Part021

theorem surrogateDiagonalTailChunk000Sub000Block184Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block184Part021CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block184Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block184Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block184Part021CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block184Part021SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block184Part021] using hcert

def TailChunk000Sub000Block184Part022SupportExplicit : Finset ℕ :=
  ([7653] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block184Part022 : ℚ :=
  (325625099 : ℚ) / 1353310808040000

def SurrogateDiagonalTailChunk000Sub000Block184Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7653
    = surrogateDiagTailX0RatChunk000Sub000Block184Part022

theorem surrogateDiagonalTailChunk000Sub000Block184Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block184Part022CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block184Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block184Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block184Part022CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block184Part022SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block184Part022] using hcert

def TailChunk000Sub000Block184Part023SupportExplicit : Finset ℕ :=
  ([7654] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block184Part023 : ℚ :=
  (447064595975 : ℚ) / 233305358357643264

def SurrogateDiagonalTailChunk000Sub000Block184Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7654
    = surrogateDiagTailX0RatChunk000Sub000Block184Part023

theorem surrogateDiagonalTailChunk000Sub000Block184Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block184Part023CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block184Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block184Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block184Part023CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block184Part023SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block184Part023] using hcert

def TailChunk000Sub000Block184Part024SupportExplicit : Finset ℕ :=
  ([7655] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block184Part024 : ℚ :=
  (4399934413 : ℚ) / 35077816144396800

def SurrogateDiagonalTailChunk000Sub000Block184Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7655
    = surrogateDiagTailX0RatChunk000Sub000Block184Part024

theorem surrogateDiagonalTailChunk000Sub000Block184Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block184Part024CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block184Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block184Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block184Part024CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block184Part024SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block184Part024] using hcert

def surrogateDiagonalTailChunk000Sub000Block184HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block184Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block184Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block184Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block184Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block184Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block184Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block184Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block184Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block184Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block184Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block184Head : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block184Part000
    + surrogateDiagTailX0RatChunk000Sub000Block184Part001
    + surrogateDiagTailX0RatChunk000Sub000Block184Part002
    + surrogateDiagTailX0RatChunk000Sub000Block184Part003
    + surrogateDiagTailX0RatChunk000Sub000Block184Part004
    + surrogateDiagTailX0RatChunk000Sub000Block184Part005
    + surrogateDiagTailX0RatChunk000Sub000Block184Part006
    + surrogateDiagTailX0RatChunk000Sub000Block184Part007
    + surrogateDiagTailX0RatChunk000Sub000Block184Part008
    + surrogateDiagTailX0RatChunk000Sub000Block184Part009

def surrogateDiagonalTailChunk000Sub000Block184MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block184Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block184Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block184Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block184Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block184Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block184Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block184Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block184Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block184Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block184Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block184Mid : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block184Part010
    + surrogateDiagTailX0RatChunk000Sub000Block184Part011
    + surrogateDiagTailX0RatChunk000Sub000Block184Part012
    + surrogateDiagTailX0RatChunk000Sub000Block184Part013
    + surrogateDiagTailX0RatChunk000Sub000Block184Part014
    + surrogateDiagTailX0RatChunk000Sub000Block184Part015
    + surrogateDiagTailX0RatChunk000Sub000Block184Part016
    + surrogateDiagTailX0RatChunk000Sub000Block184Part017
    + surrogateDiagTailX0RatChunk000Sub000Block184Part018
    + surrogateDiagTailX0RatChunk000Sub000Block184Part019

def surrogateDiagonalTailChunk000Sub000Block184TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block184Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block184Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block184Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block184Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block184Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block184Tail : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block184Part020
    + surrogateDiagTailX0RatChunk000Sub000Block184Part021
    + surrogateDiagTailX0RatChunk000Sub000Block184Part022
    + surrogateDiagTailX0RatChunk000Sub000Block184Part023
    + surrogateDiagTailX0RatChunk000Sub000Block184Part024

def surrogateDiagonalTailChunk000Sub000Block184Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub000Block184HeadSum X0
    + surrogateDiagonalTailChunk000Sub000Block184MidSum X0
    + surrogateDiagonalTailChunk000Sub000Block184TailSum X0

def surrogateDiagTailX0RatChunk000Sub000Block184 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block184Part000
    + surrogateDiagTailX0RatChunk000Sub000Block184Part001
    + surrogateDiagTailX0RatChunk000Sub000Block184Part002
    + surrogateDiagTailX0RatChunk000Sub000Block184Part003
    + surrogateDiagTailX0RatChunk000Sub000Block184Part004
    + surrogateDiagTailX0RatChunk000Sub000Block184Part005
    + surrogateDiagTailX0RatChunk000Sub000Block184Part006
    + surrogateDiagTailX0RatChunk000Sub000Block184Part007
    + surrogateDiagTailX0RatChunk000Sub000Block184Part008
    + surrogateDiagTailX0RatChunk000Sub000Block184Part009
    + surrogateDiagTailX0RatChunk000Sub000Block184Part010
    + surrogateDiagTailX0RatChunk000Sub000Block184Part011
    + surrogateDiagTailX0RatChunk000Sub000Block184Part012
    + surrogateDiagTailX0RatChunk000Sub000Block184Part013
    + surrogateDiagTailX0RatChunk000Sub000Block184Part014
    + surrogateDiagTailX0RatChunk000Sub000Block184Part015
    + surrogateDiagTailX0RatChunk000Sub000Block184Part016
    + surrogateDiagTailX0RatChunk000Sub000Block184Part017
    + surrogateDiagTailX0RatChunk000Sub000Block184Part018
    + surrogateDiagTailX0RatChunk000Sub000Block184Part019
    + surrogateDiagTailX0RatChunk000Sub000Block184Part020
    + surrogateDiagTailX0RatChunk000Sub000Block184Part021
    + surrogateDiagTailX0RatChunk000Sub000Block184Part022
    + surrogateDiagTailX0RatChunk000Sub000Block184Part023
    + surrogateDiagTailX0RatChunk000Sub000Block184Part024

theorem surrogateDiagTailX0RatChunk000Sub000Block184_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk000Sub000Block184Head + surrogateDiagTailX0RatChunk000Sub000Block184Mid + surrogateDiagTailX0RatChunk000Sub000Block184Tail =
      surrogateDiagTailX0RatChunk000Sub000Block184 := by
  unfold surrogateDiagTailX0RatChunk000Sub000Block184Head surrogateDiagTailX0RatChunk000Sub000Block184Mid surrogateDiagTailX0RatChunk000Sub000Block184Tail surrogateDiagTailX0RatChunk000Sub000Block184
  ring

def SurrogateDiagonalTailChunk000Sub000Block184HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block184HeadSum X0 = surrogateDiagTailX0RatChunk000Sub000Block184Head

def SurrogateDiagonalTailChunk000Sub000Block184MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block184MidSum X0 = surrogateDiagTailX0RatChunk000Sub000Block184Mid

def SurrogateDiagonalTailChunk000Sub000Block184TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block184TailSum X0 = surrogateDiagTailX0RatChunk000Sub000Block184Tail

theorem surrogateDiagonalTailChunk000Sub000Block184_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk000Sub000Block184HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk000Sub000Block184MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk000Sub000Block184TailCertificateAt X0) :
    surrogateDiagonalTailChunk000Sub000Block184Sum X0 = surrogateDiagTailX0RatChunk000Sub000Block184 := by
  unfold SurrogateDiagonalTailChunk000Sub000Block184HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk000Sub000Block184MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk000Sub000Block184TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk000Sub000Block184Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk000Sub000Block184_eq_head_add_mid_add_tail

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

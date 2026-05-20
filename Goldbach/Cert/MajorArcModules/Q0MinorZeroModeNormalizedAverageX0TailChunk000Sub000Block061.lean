import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0TailPilot25

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

open scoped BigOperators

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

/- Generated direct-term certificate blocks for tail chunk 000, subchunk 000, blocks [61,62). -/

/- Block 061 covers tail-support indices [1525,1550) and q from 2559 to 2598. -/

def TailChunk000Sub000Block061Part000SupportExplicit : Finset ℕ :=
  ([2559] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block061Part000 : ℚ :=
  (4037425 : ℚ) / 156129368064

def SurrogateDiagonalTailChunk000Sub000Block061Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2559
    = surrogateDiagTailX0RatChunk000Sub000Block061Part000

theorem surrogateDiagonalTailChunk000Sub000Block061Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block061Part000CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block061Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block061Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block061Part000CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block061Part000SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block061Part000] using hcert

def TailChunk000Sub000Block061Part001SupportExplicit : Finset ℕ :=
  ([2561] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block061Part001 : ℚ :=
  (187648671475 : ℚ) / 19130051410993152

def SurrogateDiagonalTailChunk000Sub000Block061Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2561
    = surrogateDiagTailX0RatChunk000Sub000Block061Part001

theorem surrogateDiagonalTailChunk000Sub000Block061Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block061Part001CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block061Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block061Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block061Part001CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block061Part001SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block061Part001] using hcert

def TailChunk000Sub000Block061Part002SupportExplicit : Finset ℕ :=
  ([2562] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block061Part002 : ℚ :=
  (9176280529 : ℚ) / 26879230771200

def SurrogateDiagonalTailChunk000Sub000Block061Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2562
    = surrogateDiagTailX0RatChunk000Sub000Block061Part002

theorem surrogateDiagonalTailChunk000Sub000Block061Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block061Part002CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block061Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block061Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block061Part002CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block061Part002SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block061Part002] using hcert

def TailChunk000Sub000Block061Part003SupportExplicit : Finset ℕ :=
  ([2563] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block061Part003 : ℚ :=
  (5946742109 : ℚ) / 579520476119040

def SurrogateDiagonalTailChunk000Sub000Block061Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2563
    = surrogateDiagTailX0RatChunk000Sub000Block061Part003

theorem surrogateDiagonalTailChunk000Sub000Block061Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block061Part003CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block061Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block061Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block061Part003CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block061Part003SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block061Part003] using hcert

def TailChunk000Sub000Block061Part004SupportExplicit : Finset ℕ :=
  ([2566] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block061Part004 : ℚ :=
  (205637668325 : ℚ) / 3377139216004644

def SurrogateDiagonalTailChunk000Sub000Block061Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2566
    = surrogateDiagTailX0RatChunk000Sub000Block061Part004

theorem surrogateDiagonalTailChunk000Sub000Block061Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block061Part004CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block061Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block061Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block061Part004CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block061Part004SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block061Part004] using hcert

def TailChunk000Sub000Block061Part005SupportExplicit : Finset ℕ :=
  ([2567] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block061Part005 : ℚ :=
  (15374228303 : ℚ) / 1659211776000000

def SurrogateDiagonalTailChunk000Sub000Block061Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2567
    = surrogateDiagTailX0RatChunk000Sub000Block061Part005

theorem surrogateDiagonalTailChunk000Sub000Block061Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block061Part005CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block061Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block061Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block061Part005CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block061Part005SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block061Part005] using hcert

def TailChunk000Sub000Block061Part006SupportExplicit : Finset ℕ :=
  ([2569] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block061Part006 : ℚ :=
  (78364357225 : ℚ) / 6461207560075392

def SurrogateDiagonalTailChunk000Sub000Block061Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2569
    = surrogateDiagTailX0RatChunk000Sub000Block061Part006

theorem surrogateDiagonalTailChunk000Sub000Block061Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block061Part006CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block061Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block061Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block061Part006CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block061Part006SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block061Part006] using hcert

def TailChunk000Sub000Block061Part007SupportExplicit : Finset ℕ :=
  ([2570] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block061Part007 : ℚ :=
  (10976265225 : ℚ) / 114555367718912

def SurrogateDiagonalTailChunk000Sub000Block061Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2570
    = surrogateDiagTailX0RatChunk000Sub000Block061Part007

theorem surrogateDiagonalTailChunk000Sub000Block061Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block061Part007CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block061Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block061Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block061Part007CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block061Part007SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block061Part007] using hcert

def TailChunk000Sub000Block061Part008SupportExplicit : Finset ℕ :=
  ([2571] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block061Part008 : ℚ :=
  (110035275 : ℚ) / 4295216365568

def SurrogateDiagonalTailChunk000Sub000Block061Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2571
    = surrogateDiagTailX0RatChunk000Sub000Block061Part008

theorem surrogateDiagonalTailChunk000Sub000Block061Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block061Part008CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block061Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block061Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block061Part008CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block061Part008SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block061Part008] using hcert

def TailChunk000Sub000Block061Part009SupportExplicit : Finset ℕ :=
  ([2573] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block061Part009 : ℚ :=
  (31608990049 : ℚ) / 3662918693251200

def SurrogateDiagonalTailChunk000Sub000Block061Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2573
    = surrogateDiagTailX0RatChunk000Sub000Block061Part009

theorem surrogateDiagonalTailChunk000Sub000Block061Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block061Part009CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block061Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block061Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block061Part009CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block061Part009SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block061Part009] using hcert

def TailChunk000Sub000Block061Part010SupportExplicit : Finset ℕ :=
  ([2577] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block061Part010 : ℚ :=
  (368743472275 : ℚ) / 21681832895319168

def SurrogateDiagonalTailChunk000Sub000Block061Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2577
    = surrogateDiagTailX0RatChunk000Sub000Block061Part010

theorem surrogateDiagonalTailChunk000Sub000Block061Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block061Part010CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block061Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block061Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block061Part010CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block061Part010SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block061Part010] using hcert

def TailChunk000Sub000Block061Part011SupportExplicit : Finset ℕ :=
  ([2578] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block061Part011 : ℚ :=
  (207565510925 : ℚ) / 3440807017718784

def SurrogateDiagonalTailChunk000Sub000Block061Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2578
    = surrogateDiagTailX0RatChunk000Sub000Block061Part011

theorem surrogateDiagonalTailChunk000Sub000Block061Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block061Part011CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block061Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block061Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block061Part011CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block061Part011SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block061Part011] using hcert

def TailChunk000Sub000Block061Part012SupportExplicit : Finset ℕ :=
  ([2579] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block061Part012 : ℚ :=
  (831238843975 : ℚ) / 110448166553907528

def SurrogateDiagonalTailChunk000Sub000Block061Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2579
    = surrogateDiagTailX0RatChunk000Sub000Block061Part012

theorem surrogateDiagonalTailChunk000Sub000Block061Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block061Part012CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block061Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block061Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block061Part012CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block061Part012SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block061Part012] using hcert

def TailChunk000Sub000Block061Part013SupportExplicit : Finset ℕ :=
  ([2581] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block061Part013 : ℚ :=
  (264773025675 : ℚ) / 30723339372199936

def SurrogateDiagonalTailChunk000Sub000Block061Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2581
    = surrogateDiagTailX0RatChunk000Sub000Block061Part013

theorem surrogateDiagonalTailChunk000Sub000Block061Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block061Part013CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block061Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block061Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block061Part013CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block061Part013SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block061Part013] using hcert

def TailChunk000Sub000Block061Part014SupportExplicit : Finset ℕ :=
  ([2582] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block061Part014 : ℚ :=
  (8328404957 : ℚ) / 138489132788100

def SurrogateDiagonalTailChunk000Sub000Block061Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2582
    = surrogateDiagTailX0RatChunk000Sub000Block061Part014

theorem surrogateDiagonalTailChunk000Sub000Block061Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block061Part014CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block061Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block061Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block061Part014CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block061Part014SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block061Part014] using hcert

def TailChunk000Sub000Block061Part015SupportExplicit : Finset ℕ :=
  ([2585] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block061Part015 : ℚ :=
  (23146032001 : ℚ) / 1146457981747200

def SurrogateDiagonalTailChunk000Sub000Block061Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2585
    = surrogateDiagTailX0RatChunk000Sub000Block061Part015

theorem surrogateDiagonalTailChunk000Sub000Block061Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block061Part015CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block061Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block061Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block061Part015CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block061Part015SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block061Part015] using hcert

def TailChunk000Sub000Block061Part016SupportExplicit : Finset ℕ :=
  ([2586] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block061Part016 : ℚ :=
  (10658735959 : ℚ) / 54711756163200

def SurrogateDiagonalTailChunk000Sub000Block061Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2586
    = surrogateDiagTailX0RatChunk000Sub000Block061Part016

theorem surrogateDiagonalTailChunk000Sub000Block061Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block061Part016CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block061Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block061Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block061Part016CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block061Part016SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block061Part016] using hcert

def TailChunk000Sub000Block061Part017SupportExplicit : Finset ℕ :=
  ([2587] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block061Part017 : ℚ :=
  (42550804975 : ℚ) / 4427311699362816

def SurrogateDiagonalTailChunk000Sub000Block061Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2587
    = surrogateDiagTailX0RatChunk000Sub000Block061Part017

theorem surrogateDiagonalTailChunk000Sub000Block061Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block061Part017CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block061Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block061Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block061Part017CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block061Part017SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block061Part017] using hcert

def TailChunk000Sub000Block061Part018SupportExplicit : Finset ℕ :=
  ([2589] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block061Part018 : ℚ :=
  (111581475 : ℚ) / 4416915087488

def SurrogateDiagonalTailChunk000Sub000Block061Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2589
    = surrogateDiagTailX0RatChunk000Sub000Block061Part018

theorem surrogateDiagonalTailChunk000Sub000Block061Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block061Part018CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block061Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block061Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block061Part018CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block061Part018SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block061Part018] using hcert

def TailChunk000Sub000Block061Part019SupportExplicit : Finset ℕ :=
  ([2590] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block061Part019 : ℚ :=
  (116272160375 : ℚ) / 696709661589504

def SurrogateDiagonalTailChunk000Sub000Block061Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2590
    = surrogateDiagTailX0RatChunk000Sub000Block061Part019

theorem surrogateDiagonalTailChunk000Sub000Block061Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block061Part019CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block061Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block061Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block061Part019CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block061Part019SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block061Part019] using hcert

def TailChunk000Sub000Block061Part020SupportExplicit : Finset ℕ :=
  ([2591] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block061Part020 : ℚ :=
  (33559691719 : ℚ) / 4500760533112200

def SurrogateDiagonalTailChunk000Sub000Block061Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2591
    = surrogateDiagTailX0RatChunk000Sub000Block061Part020

theorem surrogateDiagonalTailChunk000Sub000Block061Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block061Part020CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block061Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block061Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block061Part020CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block061Part020SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block061Part020] using hcert

def TailChunk000Sub000Block061Part021SupportExplicit : Finset ℕ :=
  ([2593] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block061Part021 : ℚ :=
  (840288033775 : ℚ) / 112866965177499648

def SurrogateDiagonalTailChunk000Sub000Block061Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2593
    = surrogateDiagTailX0RatChunk000Sub000Block061Part021

theorem surrogateDiagonalTailChunk000Sub000Block061Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block061Part021CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block061Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block061Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block061Part021CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block061Part021SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block061Part021] using hcert

def TailChunk000Sub000Block061Part022SupportExplicit : Finset ℕ :=
  ([2594] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block061Part022 : ℚ :=
  (210149959325 : ℚ) / 3527092661796864

def SurrogateDiagonalTailChunk000Sub000Block061Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2594
    = surrogateDiagTailX0RatChunk000Sub000Block061Part022

theorem surrogateDiagonalTailChunk000Sub000Block061Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block061Part022CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block061Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block061Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block061Part022CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block061Part022SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block061Part022] using hcert

def TailChunk000Sub000Block061Part023SupportExplicit : Finset ℕ :=
  ([2595] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block061Part023 : ℚ :=
  (138913099125 : ℚ) / 2987991376592896

def SurrogateDiagonalTailChunk000Sub000Block061Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2595
    = surrogateDiagTailX0RatChunk000Sub000Block061Part023

theorem surrogateDiagonalTailChunk000Sub000Block061Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block061Part023CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block061Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block061Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block061Part023CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block061Part023SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block061Part023] using hcert

def TailChunk000Sub000Block061Part024SupportExplicit : Finset ℕ :=
  ([2598] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block061Part024 : ℚ :=
  (18703975 : ℚ) / 92876046336

def SurrogateDiagonalTailChunk000Sub000Block061Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2598
    = surrogateDiagTailX0RatChunk000Sub000Block061Part024

theorem surrogateDiagonalTailChunk000Sub000Block061Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block061Part024CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block061Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block061Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block061Part024CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block061Part024SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block061Part024] using hcert

def surrogateDiagonalTailChunk000Sub000Block061HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block061Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block061Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block061Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block061Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block061Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block061Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block061Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block061Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block061Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block061Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block061Head : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block061Part000
    + surrogateDiagTailX0RatChunk000Sub000Block061Part001
    + surrogateDiagTailX0RatChunk000Sub000Block061Part002
    + surrogateDiagTailX0RatChunk000Sub000Block061Part003
    + surrogateDiagTailX0RatChunk000Sub000Block061Part004
    + surrogateDiagTailX0RatChunk000Sub000Block061Part005
    + surrogateDiagTailX0RatChunk000Sub000Block061Part006
    + surrogateDiagTailX0RatChunk000Sub000Block061Part007
    + surrogateDiagTailX0RatChunk000Sub000Block061Part008
    + surrogateDiagTailX0RatChunk000Sub000Block061Part009

def surrogateDiagonalTailChunk000Sub000Block061MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block061Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block061Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block061Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block061Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block061Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block061Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block061Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block061Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block061Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block061Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block061Mid : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block061Part010
    + surrogateDiagTailX0RatChunk000Sub000Block061Part011
    + surrogateDiagTailX0RatChunk000Sub000Block061Part012
    + surrogateDiagTailX0RatChunk000Sub000Block061Part013
    + surrogateDiagTailX0RatChunk000Sub000Block061Part014
    + surrogateDiagTailX0RatChunk000Sub000Block061Part015
    + surrogateDiagTailX0RatChunk000Sub000Block061Part016
    + surrogateDiagTailX0RatChunk000Sub000Block061Part017
    + surrogateDiagTailX0RatChunk000Sub000Block061Part018
    + surrogateDiagTailX0RatChunk000Sub000Block061Part019

def surrogateDiagonalTailChunk000Sub000Block061TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block061Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block061Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block061Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block061Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block061Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block061Tail : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block061Part020
    + surrogateDiagTailX0RatChunk000Sub000Block061Part021
    + surrogateDiagTailX0RatChunk000Sub000Block061Part022
    + surrogateDiagTailX0RatChunk000Sub000Block061Part023
    + surrogateDiagTailX0RatChunk000Sub000Block061Part024

def surrogateDiagonalTailChunk000Sub000Block061Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub000Block061HeadSum X0
    + surrogateDiagonalTailChunk000Sub000Block061MidSum X0
    + surrogateDiagonalTailChunk000Sub000Block061TailSum X0

def surrogateDiagTailX0RatChunk000Sub000Block061 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block061Part000
    + surrogateDiagTailX0RatChunk000Sub000Block061Part001
    + surrogateDiagTailX0RatChunk000Sub000Block061Part002
    + surrogateDiagTailX0RatChunk000Sub000Block061Part003
    + surrogateDiagTailX0RatChunk000Sub000Block061Part004
    + surrogateDiagTailX0RatChunk000Sub000Block061Part005
    + surrogateDiagTailX0RatChunk000Sub000Block061Part006
    + surrogateDiagTailX0RatChunk000Sub000Block061Part007
    + surrogateDiagTailX0RatChunk000Sub000Block061Part008
    + surrogateDiagTailX0RatChunk000Sub000Block061Part009
    + surrogateDiagTailX0RatChunk000Sub000Block061Part010
    + surrogateDiagTailX0RatChunk000Sub000Block061Part011
    + surrogateDiagTailX0RatChunk000Sub000Block061Part012
    + surrogateDiagTailX0RatChunk000Sub000Block061Part013
    + surrogateDiagTailX0RatChunk000Sub000Block061Part014
    + surrogateDiagTailX0RatChunk000Sub000Block061Part015
    + surrogateDiagTailX0RatChunk000Sub000Block061Part016
    + surrogateDiagTailX0RatChunk000Sub000Block061Part017
    + surrogateDiagTailX0RatChunk000Sub000Block061Part018
    + surrogateDiagTailX0RatChunk000Sub000Block061Part019
    + surrogateDiagTailX0RatChunk000Sub000Block061Part020
    + surrogateDiagTailX0RatChunk000Sub000Block061Part021
    + surrogateDiagTailX0RatChunk000Sub000Block061Part022
    + surrogateDiagTailX0RatChunk000Sub000Block061Part023
    + surrogateDiagTailX0RatChunk000Sub000Block061Part024

theorem surrogateDiagTailX0RatChunk000Sub000Block061_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk000Sub000Block061Head + surrogateDiagTailX0RatChunk000Sub000Block061Mid + surrogateDiagTailX0RatChunk000Sub000Block061Tail =
      surrogateDiagTailX0RatChunk000Sub000Block061 := by
  unfold surrogateDiagTailX0RatChunk000Sub000Block061Head surrogateDiagTailX0RatChunk000Sub000Block061Mid surrogateDiagTailX0RatChunk000Sub000Block061Tail surrogateDiagTailX0RatChunk000Sub000Block061
  ring

def SurrogateDiagonalTailChunk000Sub000Block061HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block061HeadSum X0 = surrogateDiagTailX0RatChunk000Sub000Block061Head

def SurrogateDiagonalTailChunk000Sub000Block061MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block061MidSum X0 = surrogateDiagTailX0RatChunk000Sub000Block061Mid

def SurrogateDiagonalTailChunk000Sub000Block061TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block061TailSum X0 = surrogateDiagTailX0RatChunk000Sub000Block061Tail

theorem surrogateDiagonalTailChunk000Sub000Block061_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk000Sub000Block061HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk000Sub000Block061MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk000Sub000Block061TailCertificateAt X0) :
    surrogateDiagonalTailChunk000Sub000Block061Sum X0 = surrogateDiagTailX0RatChunk000Sub000Block061 := by
  unfold SurrogateDiagonalTailChunk000Sub000Block061HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk000Sub000Block061MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk000Sub000Block061TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk000Sub000Block061Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk000Sub000Block061_eq_head_add_mid_add_tail

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0TailPilot25

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

open scoped BigOperators

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

/- Generated direct-term certificate blocks for tail chunk 000, subchunk 000, blocks [134,135). -/

/- Block 134 covers tail-support indices [3350,3375) and q from 5565 to 5606. -/

def TailChunk000Sub000Block134Part000SupportExplicit : Finset ℕ :=
  ([5565] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block134Part000 : ℚ :=
  (834723181375 : ℚ) / 97052154950320128

def SurrogateDiagonalTailChunk000Sub000Block134Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5565
    = surrogateDiagTailX0RatChunk000Sub000Block134Part000

theorem surrogateDiagonalTailChunk000Sub000Block134Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block134Part000CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block134Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block134Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block134Part000CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block134Part000SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block134Part000] using hcert

def TailChunk000Sub000Block134Part001SupportExplicit : Finset ℕ :=
  ([5567] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block134Part001 : ℚ :=
  (1817819765875 : ℚ) / 1908307183337883648

def SurrogateDiagonalTailChunk000Sub000Block134Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5567
    = surrogateDiagTailX0RatChunk000Sub000Block134Part001

theorem surrogateDiagonalTailChunk000Sub000Block134Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block134Part001CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block134Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block134Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block134Part001CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block134Part001SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block134Part001] using hcert

def TailChunk000Sub000Block134Part002SupportExplicit : Finset ℕ :=
  ([5569] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block134Part002 : ℚ :=
  (484590015625 : ℚ) / 600846829640220672

def SurrogateDiagonalTailChunk000Sub000Block134Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5569
    = surrogateDiagTailX0RatChunk000Sub000Block134Part002

theorem surrogateDiagonalTailChunk000Sub000Block134Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block134Part002CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block134Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block134Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block134Part002CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block134Part002SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block134Part002] using hcert

def TailChunk000Sub000Block134Part003SupportExplicit : Finset ℕ :=
  ([5570] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block134Part003 : ℚ :=
  (94364336675 : ℚ) / 7646734360743936

def SurrogateDiagonalTailChunk000Sub000Block134Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5570
    = surrogateDiagTailX0RatChunk000Sub000Block134Part003

theorem surrogateDiagonalTailChunk000Sub000Block134Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block134Part003CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block134Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block134Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block134Part003CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block134Part003SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block134Part003] using hcert

def TailChunk000Sub000Block134Part004SupportExplicit : Finset ℕ :=
  ([5573] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block134Part004 : ℚ :=
  (485286390625 : ℚ) / 602575262410451232

def SurrogateDiagonalTailChunk000Sub000Block134Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5573
    = surrogateDiagTailX0RatChunk000Sub000Block134Part004

theorem surrogateDiagonalTailChunk000Sub000Block134Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block134Part004CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block134Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block134Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block134Part004CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block134Part004SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block134Part004] using hcert

def TailChunk000Sub000Block134Part005SupportExplicit : Finset ℕ :=
  ([5574] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block134Part005 : ℚ :=
  (592796187175 : ℚ) / 29671448377294848

def SurrogateDiagonalTailChunk000Sub000Block134Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5574
    = surrogateDiagTailX0RatChunk000Sub000Block134Part005

theorem surrogateDiagonalTailChunk000Sub000Block134Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block134Part005CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block134Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block134Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block134Part005CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block134Part005SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block134Part005] using hcert

def TailChunk000Sub000Block134Part006SupportExplicit : Finset ℕ :=
  ([5578] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block134Part006 : ℚ :=
  (972120661975 : ℚ) / 151076855397053568

def SurrogateDiagonalTailChunk000Sub000Block134Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5578
    = surrogateDiagTailX0RatChunk000Sub000Block134Part006

theorem surrogateDiagonalTailChunk000Sub000Block134Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block134Part006CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block134Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block134Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block134Part006CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block134Part006SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block134Part006] using hcert

def TailChunk000Sub000Block134Part007SupportExplicit : Finset ℕ :=
  ([5579] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block134Part007 : ℚ :=
  (1625829977575 : ℚ) / 1301020474942015488

def SurrogateDiagonalTailChunk000Sub000Block134Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5579
    = surrogateDiagTailX0RatChunk000Sub000Block134Part007

theorem surrogateDiagonalTailChunk000Sub000Block134Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block134Part007CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block134Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block134Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block134Part007CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block134Part007SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block134Part007] using hcert

def TailChunk000Sub000Block134Part008SupportExplicit : Finset ℕ :=
  ([5581] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block134Part008 : ℚ :=
  (778689025 : ℚ) / 969669300040992

def SurrogateDiagonalTailChunk000Sub000Block134Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5581
    = surrogateDiagTailX0RatChunk000Sub000Block134Part008

theorem surrogateDiagonalTailChunk000Sub000Block134Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block134Part008CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block134Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block134Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block134Part008CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block134Part008SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block134Part008] using hcert

def TailChunk000Sub000Block134Part009SupportExplicit : Finset ℕ :=
  ([5582] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block134Part009 : ℚ :=
  (194742025 : ℚ) / 60604331252562

def SurrogateDiagonalTailChunk000Sub000Block134Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5582
    = surrogateDiagTailX0RatChunk000Sub000Block134Part009

theorem surrogateDiagonalTailChunk000Sub000Block134Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block134Part009CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block134Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block134Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block134Part009CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block134Part009SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block134Part009] using hcert

def TailChunk000Sub000Block134Part010SupportExplicit : Finset ℕ :=
  ([5583] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block134Part010 : ℚ :=
  (1730633 : ℚ) / 638337715200

def SurrogateDiagonalTailChunk000Sub000Block134Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5583
    = surrogateDiagTailX0RatChunk000Sub000Block134Part010

theorem surrogateDiagonalTailChunk000Sub000Block134Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block134Part010CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block134Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block134Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block134Part010CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block134Part010SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block134Part010] using hcert

def TailChunk000Sub000Block134Part011SupportExplicit : Finset ℕ :=
  ([5585] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block134Part011 : ℚ :=
  (779190681875 : ℚ) / 496470681620987904

def SurrogateDiagonalTailChunk000Sub000Block134Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5585
    = surrogateDiagTailX0RatChunk000Sub000Block134Part011

theorem surrogateDiagonalTailChunk000Sub000Block134Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block134Part011CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block134Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block134Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block134Part011CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block134Part011SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block134Part011] using hcert

def TailChunk000Sub000Block134Part012SupportExplicit : Finset ℕ :=
  ([5587] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block134Part012 : ℚ :=
  (75161088199 : ℚ) / 85047566112000000

def SurrogateDiagonalTailChunk000Sub000Block134Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5587
    = surrogateDiagTailX0RatChunk000Sub000Block134Part012

theorem surrogateDiagonalTailChunk000Sub000Block134Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block134Part012CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block134Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block134Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block134Part012CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block134Part012SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block134Part012] using hcert

def TailChunk000Sub000Block134Part013SupportExplicit : Finset ℕ :=
  ([5590] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block134Part013 : ℚ :=
  (170141971225 : ℚ) / 10325925293064192

def SurrogateDiagonalTailChunk000Sub000Block134Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5590
    = surrogateDiagTailX0RatChunk000Sub000Block134Part013

theorem surrogateDiagonalTailChunk000Sub000Block134Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block134Part013CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block134Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block134Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block134Part013CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block134Part013SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block134Part013] using hcert

def TailChunk000Sub000Block134Part014SupportExplicit : Finset ℕ :=
  ([5591] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block134Part014 : ℚ :=
  (781482025 : ℚ) / 976639042360722

def SurrogateDiagonalTailChunk000Sub000Block134Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5591
    = surrogateDiagTailX0RatChunk000Sub000Block134Part014

theorem surrogateDiagonalTailChunk000Sub000Block134Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block134Part014CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block134Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block134Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block134Part014CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block134Part014SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block134Part014] using hcert

def TailChunk000Sub000Block134Part015SupportExplicit : Finset ℕ :=
  ([5593] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block134Part015 : ℚ :=
  (1529432426125 : ℚ) / 950918108380397568

def SurrogateDiagonalTailChunk000Sub000Block134Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5593
    = surrogateDiagTailX0RatChunk000Sub000Block134Part015

theorem surrogateDiagonalTailChunk000Sub000Block134Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block134Part015CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block134Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block134Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block134Part015CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block134Part015SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block134Part015] using hcert

def TailChunk000Sub000Block134Part016SupportExplicit : Finset ℕ :=
  ([5594] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block134Part016 : ℚ :=
  (977705544775 : ℚ) / 152818357368601728

def SurrogateDiagonalTailChunk000Sub000Block134Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5594
    = surrogateDiagTailX0RatChunk000Sub000Block134Part016

theorem surrogateDiagonalTailChunk000Sub000Block134Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block134Part016CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block134Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block134Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block134Part016CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block134Part016SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block134Part016] using hcert

def TailChunk000Sub000Block134Part017SupportExplicit : Finset ℕ :=
  ([5595] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block134Part017 : ℚ :=
  (893503422625 : ℚ) / 196136565578661888

def SurrogateDiagonalTailChunk000Sub000Block134Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5595
    = surrogateDiagTailX0RatChunk000Sub000Block134Part017

theorem surrogateDiagonalTailChunk000Sub000Block134Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block134Part017CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block134Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block134Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block134Part017CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block134Part017SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block134Part017] using hcert

def TailChunk000Sub000Block134Part018SupportExplicit : Finset ℕ :=
  ([5597] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block134Part018 : ℚ :=
  (133784670875 : ℚ) / 149188677250056192

def SurrogateDiagonalTailChunk000Sub000Block134Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5597
    = surrogateDiagTailX0RatChunk000Sub000Block134Part018

theorem surrogateDiagonalTailChunk000Sub000Block134Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block134Part018CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block134Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block134Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block134Part018CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block134Part018SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block134Part018] using hcert

def TailChunk000Sub000Block134Part019SupportExplicit : Finset ℕ :=
  ([5599] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block134Part019 : ℚ :=
  (17615311111 : ℚ) / 16652586875404800

def SurrogateDiagonalTailChunk000Sub000Block134Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5599
    = surrogateDiagTailX0RatChunk000Sub000Block134Part019

theorem surrogateDiagonalTailChunk000Sub000Block134Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block134Part019CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block134Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block134Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block134Part019CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block134Part019SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block134Part019] using hcert

def TailChunk000Sub000Block134Part020SupportExplicit : Finset ℕ :=
  ([5601] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block134Part020 : ℚ :=
  (43545275 : ℚ) / 16165356781248

def SurrogateDiagonalTailChunk000Sub000Block134Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5601
    = surrogateDiagTailX0RatChunk000Sub000Block134Part020

theorem surrogateDiagonalTailChunk000Sub000Block134Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block134Part020CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block134Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block134Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block134Part020CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block134Part020SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block134Part020] using hcert

def TailChunk000Sub000Block134Part021SupportExplicit : Finset ℕ :=
  ([5602] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block134Part021 : ℚ :=
  (39220159399 : ℚ) / 6147789312000000

def SurrogateDiagonalTailChunk000Sub000Block134Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5602
    = surrogateDiagTailX0RatChunk000Sub000Block134Part021

theorem surrogateDiagonalTailChunk000Sub000Block134Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block134Part021CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block134Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block134Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block134Part021CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block134Part021SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block134Part021] using hcert

def TailChunk000Sub000Block134Part022SupportExplicit : Finset ℕ :=
  ([5603] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block134Part022 : ℚ :=
  (23783384723 : ℚ) / 23635478662502400

def SurrogateDiagonalTailChunk000Sub000Block134Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5603
    = surrogateDiagTailX0RatChunk000Sub000Block134Part022

theorem surrogateDiagonalTailChunk000Sub000Block134Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block134Part022CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block134Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block134Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block134Part022CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block134Part022SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block134Part022] using hcert

def TailChunk000Sub000Block134Part023SupportExplicit : Finset ℕ :=
  ([5605] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block134Part023 : ℚ :=
  (230658379025 : ℚ) / 126741128127234048

def SurrogateDiagonalTailChunk000Sub000Block134Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5605
    = surrogateDiagTailX0RatChunk000Sub000Block134Part023

theorem surrogateDiagonalTailChunk000Sub000Block134Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block134Part023CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block134Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block134Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block134Part023CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block134Part023SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block134Part023] using hcert

def TailChunk000Sub000Block134Part024SupportExplicit : Finset ℕ :=
  ([5606] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block134Part024 : ℚ :=
  (981904704775 : ℚ) / 154134331326164808

def SurrogateDiagonalTailChunk000Sub000Block134Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5606
    = surrogateDiagTailX0RatChunk000Sub000Block134Part024

theorem surrogateDiagonalTailChunk000Sub000Block134Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block134Part024CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block134Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block134Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block134Part024CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block134Part024SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block134Part024] using hcert

def surrogateDiagonalTailChunk000Sub000Block134HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block134Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block134Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block134Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block134Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block134Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block134Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block134Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block134Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block134Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block134Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block134Head : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block134Part000
    + surrogateDiagTailX0RatChunk000Sub000Block134Part001
    + surrogateDiagTailX0RatChunk000Sub000Block134Part002
    + surrogateDiagTailX0RatChunk000Sub000Block134Part003
    + surrogateDiagTailX0RatChunk000Sub000Block134Part004
    + surrogateDiagTailX0RatChunk000Sub000Block134Part005
    + surrogateDiagTailX0RatChunk000Sub000Block134Part006
    + surrogateDiagTailX0RatChunk000Sub000Block134Part007
    + surrogateDiagTailX0RatChunk000Sub000Block134Part008
    + surrogateDiagTailX0RatChunk000Sub000Block134Part009

def surrogateDiagonalTailChunk000Sub000Block134MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block134Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block134Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block134Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block134Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block134Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block134Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block134Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block134Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block134Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block134Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block134Mid : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block134Part010
    + surrogateDiagTailX0RatChunk000Sub000Block134Part011
    + surrogateDiagTailX0RatChunk000Sub000Block134Part012
    + surrogateDiagTailX0RatChunk000Sub000Block134Part013
    + surrogateDiagTailX0RatChunk000Sub000Block134Part014
    + surrogateDiagTailX0RatChunk000Sub000Block134Part015
    + surrogateDiagTailX0RatChunk000Sub000Block134Part016
    + surrogateDiagTailX0RatChunk000Sub000Block134Part017
    + surrogateDiagTailX0RatChunk000Sub000Block134Part018
    + surrogateDiagTailX0RatChunk000Sub000Block134Part019

def surrogateDiagonalTailChunk000Sub000Block134TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block134Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block134Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block134Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block134Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block134Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block134Tail : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block134Part020
    + surrogateDiagTailX0RatChunk000Sub000Block134Part021
    + surrogateDiagTailX0RatChunk000Sub000Block134Part022
    + surrogateDiagTailX0RatChunk000Sub000Block134Part023
    + surrogateDiagTailX0RatChunk000Sub000Block134Part024

def surrogateDiagonalTailChunk000Sub000Block134Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub000Block134HeadSum X0
    + surrogateDiagonalTailChunk000Sub000Block134MidSum X0
    + surrogateDiagonalTailChunk000Sub000Block134TailSum X0

def surrogateDiagTailX0RatChunk000Sub000Block134 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block134Part000
    + surrogateDiagTailX0RatChunk000Sub000Block134Part001
    + surrogateDiagTailX0RatChunk000Sub000Block134Part002
    + surrogateDiagTailX0RatChunk000Sub000Block134Part003
    + surrogateDiagTailX0RatChunk000Sub000Block134Part004
    + surrogateDiagTailX0RatChunk000Sub000Block134Part005
    + surrogateDiagTailX0RatChunk000Sub000Block134Part006
    + surrogateDiagTailX0RatChunk000Sub000Block134Part007
    + surrogateDiagTailX0RatChunk000Sub000Block134Part008
    + surrogateDiagTailX0RatChunk000Sub000Block134Part009
    + surrogateDiagTailX0RatChunk000Sub000Block134Part010
    + surrogateDiagTailX0RatChunk000Sub000Block134Part011
    + surrogateDiagTailX0RatChunk000Sub000Block134Part012
    + surrogateDiagTailX0RatChunk000Sub000Block134Part013
    + surrogateDiagTailX0RatChunk000Sub000Block134Part014
    + surrogateDiagTailX0RatChunk000Sub000Block134Part015
    + surrogateDiagTailX0RatChunk000Sub000Block134Part016
    + surrogateDiagTailX0RatChunk000Sub000Block134Part017
    + surrogateDiagTailX0RatChunk000Sub000Block134Part018
    + surrogateDiagTailX0RatChunk000Sub000Block134Part019
    + surrogateDiagTailX0RatChunk000Sub000Block134Part020
    + surrogateDiagTailX0RatChunk000Sub000Block134Part021
    + surrogateDiagTailX0RatChunk000Sub000Block134Part022
    + surrogateDiagTailX0RatChunk000Sub000Block134Part023
    + surrogateDiagTailX0RatChunk000Sub000Block134Part024

theorem surrogateDiagTailX0RatChunk000Sub000Block134_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk000Sub000Block134Head + surrogateDiagTailX0RatChunk000Sub000Block134Mid + surrogateDiagTailX0RatChunk000Sub000Block134Tail =
      surrogateDiagTailX0RatChunk000Sub000Block134 := by
  unfold surrogateDiagTailX0RatChunk000Sub000Block134Head surrogateDiagTailX0RatChunk000Sub000Block134Mid surrogateDiagTailX0RatChunk000Sub000Block134Tail surrogateDiagTailX0RatChunk000Sub000Block134
  ring

def SurrogateDiagonalTailChunk000Sub000Block134HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block134HeadSum X0 = surrogateDiagTailX0RatChunk000Sub000Block134Head

def SurrogateDiagonalTailChunk000Sub000Block134MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block134MidSum X0 = surrogateDiagTailX0RatChunk000Sub000Block134Mid

def SurrogateDiagonalTailChunk000Sub000Block134TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block134TailSum X0 = surrogateDiagTailX0RatChunk000Sub000Block134Tail

theorem surrogateDiagonalTailChunk000Sub000Block134_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk000Sub000Block134HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk000Sub000Block134MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk000Sub000Block134TailCertificateAt X0) :
    surrogateDiagonalTailChunk000Sub000Block134Sum X0 = surrogateDiagTailX0RatChunk000Sub000Block134 := by
  unfold SurrogateDiagonalTailChunk000Sub000Block134HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk000Sub000Block134MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk000Sub000Block134TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk000Sub000Block134Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk000Sub000Block134_eq_head_add_mid_add_tail

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

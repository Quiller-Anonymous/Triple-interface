import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0TailPilot25

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

open scoped BigOperators

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

/- Generated direct-term certificate blocks for tail chunk 000, subchunk 001, blocks [7,8). -/

/-- Block 007 covers tail-support indices [5175,5200) and q from 8561 to 8599. -/

def TailChunk000Sub001Block007Part000SupportExplicit : Finset ℕ :=
  ([8561] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block007Part000 : ℚ :=
  (374971447525 : ℚ) / 7226311592409257088

def SurrogateDiagonalTailChunk000Sub001Block007Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8561
    = surrogateDiagTailX0RatChunk000Sub001Block007Part000

theorem surrogateDiagonalTailChunk000Sub001Block007Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block007Part000CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block007Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block007Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block007Part000CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block007Part000SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block007Part000] using hcert

def TailChunk000Sub001Block007Part001SupportExplicit : Finset ℕ :=
  ([8562] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block007Part001 : ℚ :=
  (76317825 : ℚ) / 16540098570304

def SurrogateDiagonalTailChunk000Sub001Block007Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8562
    = surrogateDiagTailX0RatChunk000Sub001Block007Part001

theorem surrogateDiagonalTailChunk000Sub001Block007Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block007Part001CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block007Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block007Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block007Part001CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block007Part001SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block007Part001] using hcert

def TailChunk000Sub001Block007Part002SupportExplicit : Finset ℕ :=
  ([8563] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block007Part002 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block007Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8563
    = surrogateDiagTailX0RatChunk000Sub001Block007Part002

theorem surrogateDiagonalTailChunk000Sub001Block007Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block007Part002CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block007Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block007Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block007Part002CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block007Part002SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block007Part002] using hcert

def TailChunk000Sub001Block007Part003SupportExplicit : Finset ℕ :=
  ([8565] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block007Part003 : ℚ :=
  (13452753161 : ℚ) / 21623013786009600

def SurrogateDiagonalTailChunk000Sub001Block007Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8565
    = surrogateDiagTailX0RatChunk000Sub001Block007Part003

theorem surrogateDiagonalTailChunk000Sub001Block007Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block007Part003CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block007Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block007Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block007Part003CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block007Part003SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block007Part003] using hcert

def TailChunk000Sub001Block007Part004SupportExplicit : Finset ℕ :=
  ([8566] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block007Part004 : ℚ :=
  (286626390625 : ℚ) / 210161674151654322

def SurrogateDiagonalTailChunk000Sub001Block007Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8566
    = surrogateDiagTailX0RatChunk000Sub001Block007Part004

theorem surrogateDiagonalTailChunk000Sub001Block007Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block007Part004CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block007Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block007Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block007Part004CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block007Part004SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block007Part004] using hcert

def TailChunk000Sub001Block007Part005SupportExplicit : Finset ℕ :=
  ([8567] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block007Part005 : ℚ :=
  (13745693425 : ℚ) / 607484826629831808

def SurrogateDiagonalTailChunk000Sub001Block007Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8567
    = surrogateDiagTailX0RatChunk000Sub001Block007Part005

theorem surrogateDiagonalTailChunk000Sub001Block007Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block007Part005CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block007Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block007Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block007Part005CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block007Part005SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block007Part005] using hcert

def TailChunk000Sub001Block007Part006SupportExplicit : Finset ℕ :=
  ([8569] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block007Part006 : ℚ :=
  (5374642807 : ℚ) / 89597435904000000

def SurrogateDiagonalTailChunk000Sub001Block007Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8569
    = surrogateDiagTailX0RatChunk000Sub001Block007Part006

theorem surrogateDiagonalTailChunk000Sub001Block007Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block007Part006CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block007Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block007Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block007Part006CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block007Part006SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block007Part006] using hcert

def TailChunk000Sub001Block007Part007SupportExplicit : Finset ℕ :=
  ([8570] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block007Part007 : ℚ :=
  (321049671375 : ℚ) / 114562010902429696

def SurrogateDiagonalTailChunk000Sub001Block007Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8570
    = surrogateDiagTailX0RatChunk000Sub001Block007Part007

theorem surrogateDiagonalTailChunk000Sub001Block007Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block007Part007CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block007Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block007Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block007Part007CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block007Part007SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block007Part007] using hcert

def TailChunk000Sub001Block007Part008SupportExplicit : Finset ℕ :=
  ([8571] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block007Part008 : ℚ :=
  (18229325575 : ℚ) / 95065212345901056

def SurrogateDiagonalTailChunk000Sub001Block007Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8571
    = surrogateDiagTailX0RatChunk000Sub001Block007Part008

theorem surrogateDiagonalTailChunk000Sub001Block007Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block007Part008CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block007Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block007Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block007Part008CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block007Part008SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block007Part008] using hcert

def TailChunk000Sub001Block007Part009SupportExplicit : Finset ℕ :=
  ([8573] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block007Part009 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block007Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8573
    = surrogateDiagTailX0RatChunk000Sub001Block007Part009

theorem surrogateDiagonalTailChunk000Sub001Block007Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block007Part009CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block007Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block007Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block007Part009CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block007Part009SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block007Part009] using hcert

def TailChunk000Sub001Block007Part010SupportExplicit : Finset ℕ :=
  ([8574] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block007Part010 : ℚ :=
  (892920715525 : ℚ) / 166364121605326848

def SurrogateDiagonalTailChunk000Sub001Block007Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8574
    = surrogateDiagTailX0RatChunk000Sub001Block007Part010

theorem surrogateDiagonalTailChunk000Sub001Block007Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block007Part010CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block007Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block007Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block007Part010CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block007Part010SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block007Part010] using hcert

def TailChunk000Sub001Block007Part011SupportExplicit : Finset ℕ :=
  ([8578] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block007Part011 : ℚ :=
  (287430015625 : ℚ) / 211342078500667392

def SurrogateDiagonalTailChunk000Sub001Block007Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8578
    = surrogateDiagTailX0RatChunk000Sub001Block007Part011

theorem surrogateDiagonalTailChunk000Sub001Block007Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block007Part011CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block007Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block007Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block007Part011CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block007Part011SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block007Part011] using hcert

def TailChunk000Sub001Block007Part012SupportExplicit : Finset ℕ :=
  ([8579] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block007Part012 : ℚ :=
  (39676866125 : ℚ) / 3739108667496339456

def SurrogateDiagonalTailChunk000Sub001Block007Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8579
    = surrogateDiagTailX0RatChunk000Sub001Block007Part012

theorem surrogateDiagonalTailChunk000Sub001Block007Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block007Part012CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block007Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block007Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block007Part012CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block007Part012SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block007Part012] using hcert

def TailChunk000Sub001Block007Part013SupportExplicit : Finset ℕ :=
  ([8581] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block007Part013 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block007Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8581
    = surrogateDiagTailX0RatChunk000Sub001Block007Part013

theorem surrogateDiagonalTailChunk000Sub001Block007Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block007Part013CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block007Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block007Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block007Part013CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block007Part013SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block007Part013] using hcert

def TailChunk000Sub001Block007Part014SupportExplicit : Finset ℕ :=
  ([8582] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block007Part014 : ℚ :=
  (252163947625 : ℚ) / 113652124307845632

def SurrogateDiagonalTailChunk000Sub001Block007Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8582
    = surrogateDiagTailX0RatChunk000Sub001Block007Part014

theorem surrogateDiagonalTailChunk000Sub001Block007Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block007Part014CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block007Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block007Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block007Part014CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block007Part014SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block007Part014] using hcert

def TailChunk000Sub001Block007Part015SupportExplicit : Finset ℕ :=
  ([8583] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block007Part015 : ℚ :=
  (20457406979 : ℚ) / 53535389864985600

def SurrogateDiagonalTailChunk000Sub001Block007Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8583
    = surrogateDiagTailX0RatChunk000Sub001Block007Part015

theorem surrogateDiagonalTailChunk000Sub001Block007Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block007Part015CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block007Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block007Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block007Part015CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block007Part015SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block007Part015] using hcert

def TailChunk000Sub001Block007Part016SupportExplicit : Finset ℕ :=
  ([8585] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block007Part016 : ℚ :=
  (124579457 : ℚ) / 839028572160000

def SurrogateDiagonalTailChunk000Sub001Block007Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8585
    = surrogateDiagTailX0RatChunk000Sub001Block007Part016

theorem surrogateDiagonalTailChunk000Sub001Block007Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block007Part016CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block007Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block007Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block007Part016CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block007Part016SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block007Part016] using hcert

def TailChunk000Sub001Block007Part017SupportExplicit : Finset ℕ :=
  ([8587] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block007Part017 : ℚ :=
  (3790605157 : ℚ) / 470119426140211200

def SurrogateDiagonalTailChunk000Sub001Block007Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8587
    = surrogateDiagTailX0RatChunk000Sub001Block007Part017

theorem surrogateDiagonalTailChunk000Sub001Block007Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block007Part017CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block007Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block007Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block007Part017CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block007Part017SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block007Part017] using hcert

def TailChunk000Sub001Block007Part018SupportExplicit : Finset ℕ :=
  ([8589] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block007Part018 : ℚ :=
  (490752752675 : ℚ) / 718393674637246464

def SurrogateDiagonalTailChunk000Sub001Block007Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8589
    = surrogateDiagTailX0RatChunk000Sub001Block007Part018

theorem surrogateDiagonalTailChunk000Sub001Block007Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block007Part018CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block007Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block007Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block007Part018CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block007Part018SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block007Part018] using hcert

def TailChunk000Sub001Block007Part019SupportExplicit : Finset ℕ :=
  ([8590] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block007Part019 : ℚ :=
  (460819520375 : ℚ) / 173454663162553344

def SurrogateDiagonalTailChunk000Sub001Block007Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8590
    = surrogateDiagTailX0RatChunk000Sub001Block007Part019

theorem surrogateDiagonalTailChunk000Sub001Block007Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block007Part019CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block007Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block007Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block007Part019CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block007Part019SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block007Part019] using hcert

def TailChunk000Sub001Block007Part020SupportExplicit : Finset ℕ :=
  ([8593] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block007Part020 : ℚ :=
  (176453501 : ℚ) / 8944064039116800

def SurrogateDiagonalTailChunk000Sub001Block007Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8593
    = surrogateDiagTailX0RatChunk000Sub001Block007Part020

theorem surrogateDiagonalTailChunk000Sub001Block007Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block007Part020CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block007Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block007Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block007Part020CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block007Part020SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block007Part020] using hcert

def TailChunk000Sub001Block007Part021SupportExplicit : Finset ℕ :=
  ([8594] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block007Part021 : ℚ :=
  (288503265625 : ℚ) / 212923677432402432

def SurrogateDiagonalTailChunk000Sub001Block007Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8594
    = surrogateDiagTailX0RatChunk000Sub001Block007Part021

theorem surrogateDiagonalTailChunk000Sub001Block007Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block007Part021CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block007Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block007Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block007Part021CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block007Part021SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block007Part021] using hcert

def TailChunk000Sub001Block007Part022SupportExplicit : Finset ℕ :=
  ([8597] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block007Part022 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block007Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8597
    = surrogateDiagTailX0RatChunk000Sub001Block007Part022

theorem surrogateDiagonalTailChunk000Sub001Block007Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block007Part022CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block007Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block007Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block007Part022CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block007Part022SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block007Part022] using hcert

def TailChunk000Sub001Block007Part023SupportExplicit : Finset ℕ :=
  ([8598] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block007Part023 : ℚ :=
  (897926573425 : ℚ) / 168235992045355008

def SurrogateDiagonalTailChunk000Sub001Block007Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8598
    = surrogateDiagTailX0RatChunk000Sub001Block007Part023

theorem surrogateDiagonalTailChunk000Sub001Block007Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block007Part023CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block007Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block007Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block007Part023CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block007Part023SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block007Part023] using hcert

def TailChunk000Sub001Block007Part024SupportExplicit : Finset ℕ :=
  ([8599] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block007Part024 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block007Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8599
    = surrogateDiagTailX0RatChunk000Sub001Block007Part024

theorem surrogateDiagonalTailChunk000Sub001Block007Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block007Part024CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block007Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block007Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block007Part024CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block007Part024SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block007Part024] using hcert

def surrogateDiagonalTailChunk000Sub001Block007HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block007Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block007Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block007Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block007Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block007Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block007Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block007Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block007Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block007Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block007Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block007Head : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block007Part000
    + surrogateDiagTailX0RatChunk000Sub001Block007Part001
    + surrogateDiagTailX0RatChunk000Sub001Block007Part002
    + surrogateDiagTailX0RatChunk000Sub001Block007Part003
    + surrogateDiagTailX0RatChunk000Sub001Block007Part004
    + surrogateDiagTailX0RatChunk000Sub001Block007Part005
    + surrogateDiagTailX0RatChunk000Sub001Block007Part006
    + surrogateDiagTailX0RatChunk000Sub001Block007Part007
    + surrogateDiagTailX0RatChunk000Sub001Block007Part008
    + surrogateDiagTailX0RatChunk000Sub001Block007Part009

def surrogateDiagonalTailChunk000Sub001Block007MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block007Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block007Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block007Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block007Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block007Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block007Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block007Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block007Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block007Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block007Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block007Mid : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block007Part010
    + surrogateDiagTailX0RatChunk000Sub001Block007Part011
    + surrogateDiagTailX0RatChunk000Sub001Block007Part012
    + surrogateDiagTailX0RatChunk000Sub001Block007Part013
    + surrogateDiagTailX0RatChunk000Sub001Block007Part014
    + surrogateDiagTailX0RatChunk000Sub001Block007Part015
    + surrogateDiagTailX0RatChunk000Sub001Block007Part016
    + surrogateDiagTailX0RatChunk000Sub001Block007Part017
    + surrogateDiagTailX0RatChunk000Sub001Block007Part018
    + surrogateDiagTailX0RatChunk000Sub001Block007Part019

def surrogateDiagonalTailChunk000Sub001Block007TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block007Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block007Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block007Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block007Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block007Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block007Tail : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block007Part020
    + surrogateDiagTailX0RatChunk000Sub001Block007Part021
    + surrogateDiagTailX0RatChunk000Sub001Block007Part022
    + surrogateDiagTailX0RatChunk000Sub001Block007Part023
    + surrogateDiagTailX0RatChunk000Sub001Block007Part024

def surrogateDiagonalTailChunk000Sub001Block007Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub001Block007HeadSum X0
    + surrogateDiagonalTailChunk000Sub001Block007MidSum X0
    + surrogateDiagonalTailChunk000Sub001Block007TailSum X0

def surrogateDiagTailX0RatChunk000Sub001Block007 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block007Part000
    + surrogateDiagTailX0RatChunk000Sub001Block007Part001
    + surrogateDiagTailX0RatChunk000Sub001Block007Part002
    + surrogateDiagTailX0RatChunk000Sub001Block007Part003
    + surrogateDiagTailX0RatChunk000Sub001Block007Part004
    + surrogateDiagTailX0RatChunk000Sub001Block007Part005
    + surrogateDiagTailX0RatChunk000Sub001Block007Part006
    + surrogateDiagTailX0RatChunk000Sub001Block007Part007
    + surrogateDiagTailX0RatChunk000Sub001Block007Part008
    + surrogateDiagTailX0RatChunk000Sub001Block007Part009
    + surrogateDiagTailX0RatChunk000Sub001Block007Part010
    + surrogateDiagTailX0RatChunk000Sub001Block007Part011
    + surrogateDiagTailX0RatChunk000Sub001Block007Part012
    + surrogateDiagTailX0RatChunk000Sub001Block007Part013
    + surrogateDiagTailX0RatChunk000Sub001Block007Part014
    + surrogateDiagTailX0RatChunk000Sub001Block007Part015
    + surrogateDiagTailX0RatChunk000Sub001Block007Part016
    + surrogateDiagTailX0RatChunk000Sub001Block007Part017
    + surrogateDiagTailX0RatChunk000Sub001Block007Part018
    + surrogateDiagTailX0RatChunk000Sub001Block007Part019
    + surrogateDiagTailX0RatChunk000Sub001Block007Part020
    + surrogateDiagTailX0RatChunk000Sub001Block007Part021
    + surrogateDiagTailX0RatChunk000Sub001Block007Part022
    + surrogateDiagTailX0RatChunk000Sub001Block007Part023
    + surrogateDiagTailX0RatChunk000Sub001Block007Part024

theorem surrogateDiagTailX0RatChunk000Sub001Block007_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk000Sub001Block007Head + surrogateDiagTailX0RatChunk000Sub001Block007Mid + surrogateDiagTailX0RatChunk000Sub001Block007Tail =
      surrogateDiagTailX0RatChunk000Sub001Block007 := by
  unfold surrogateDiagTailX0RatChunk000Sub001Block007Head surrogateDiagTailX0RatChunk000Sub001Block007Mid surrogateDiagTailX0RatChunk000Sub001Block007Tail surrogateDiagTailX0RatChunk000Sub001Block007
  ring

def SurrogateDiagonalTailChunk000Sub001Block007HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block007HeadSum X0 = surrogateDiagTailX0RatChunk000Sub001Block007Head

def SurrogateDiagonalTailChunk000Sub001Block007MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block007MidSum X0 = surrogateDiagTailX0RatChunk000Sub001Block007Mid

def SurrogateDiagonalTailChunk000Sub001Block007TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block007TailSum X0 = surrogateDiagTailX0RatChunk000Sub001Block007Tail

theorem surrogateDiagonalTailChunk000Sub001Block007_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk000Sub001Block007HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk000Sub001Block007MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk000Sub001Block007TailCertificateAt X0) :
    surrogateDiagonalTailChunk000Sub001Block007Sum X0 = surrogateDiagTailX0RatChunk000Sub001Block007 := by
  unfold SurrogateDiagonalTailChunk000Sub001Block007HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk000Sub001Block007MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk000Sub001Block007TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk000Sub001Block007Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk000Sub001Block007_eq_head_add_mid_add_tail

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

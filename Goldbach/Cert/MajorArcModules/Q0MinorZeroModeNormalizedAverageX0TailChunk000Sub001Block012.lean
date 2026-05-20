import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0TailPilot25

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

open scoped BigOperators

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

/- Generated direct-term certificate blocks for tail chunk 000, subchunk 001, blocks [12,13). -/

/-- Block 012 covers tail-support indices [5300,5325) and q from 8763 to 8801. -/

def TailChunk000Sub001Block012Part000SupportExplicit : Finset ℕ :=
  ([8763] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block012Part000 : ℚ :=
  (31684587925 : ℚ) / 131234264076174336

def SurrogateDiagonalTailChunk000Sub001Block012Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8763
    = surrogateDiagTailX0RatChunk000Sub001Block012Part000

theorem surrogateDiagonalTailChunk000Sub001Block012Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block012Part000CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block012Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block012Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block012Part000CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block012Part000SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block012Part000] using hcert

def TailChunk000Sub001Block012Part001SupportExplicit : Finset ℕ :=
  ([8765] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block012Part001 : ℚ :=
  (288275964725 : ℚ) / 3015596536632705024

def SurrogateDiagonalTailChunk000Sub001Block012Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8765
    = surrogateDiagTailX0RatChunk000Sub001Block012Part001

theorem surrogateDiagonalTailChunk000Sub001Block012Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block012Part001CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block012Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block012Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block012Part001CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block012Part001SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block012Part001] using hcert

def TailChunk000Sub001Block012Part002SupportExplicit : Finset ℕ :=
  ([8767] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block012Part002 : ℚ :=
  (961981297 : ℚ) / 40154952930309120

def SurrogateDiagonalTailChunk000Sub001Block012Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8767
    = surrogateDiagTailX0RatChunk000Sub001Block012Part002

theorem surrogateDiagonalTailChunk000Sub001Block012Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block012Part002CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block012Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block012Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block012Part002CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block012Part002SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block012Part002] using hcert

def TailChunk000Sub001Block012Part003SupportExplicit : Finset ℕ :=
  ([8769] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block012Part003 : ℚ :=
  (562730433325 : ℚ) / 2487340580582227968

def SurrogateDiagonalTailChunk000Sub001Block012Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8769
    = surrogateDiagTailX0RatChunk000Sub001Block012Part003

theorem surrogateDiagonalTailChunk000Sub001Block012Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block012Part003CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block012Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block012Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block012Part003CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block012Part003SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block012Part003] using hcert

def TailChunk000Sub001Block012Part004SupportExplicit : Finset ℕ :=
  ([8770] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block012Part004 : ℚ :=
  (480330921875 : ℚ) / 188474783539544064

def SurrogateDiagonalTailChunk000Sub001Block012Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8770
    = surrogateDiagTailX0RatChunk000Sub001Block012Part004

theorem surrogateDiagonalTailChunk000Sub001Block012Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block012Part004CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block012Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block012Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block012Part004CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block012Part004SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block012Part004] using hcert

def TailChunk000Sub001Block012Part005SupportExplicit : Finset ℕ :=
  ([8773] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block012Part005 : ℚ :=
  (36542111861 : ℚ) / 102470368506906240

def SurrogateDiagonalTailChunk000Sub001Block012Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8773
    = surrogateDiagTailX0RatChunk000Sub001Block012Part005

theorem surrogateDiagonalTailChunk000Sub001Block012Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block012Part005CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block012Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block012Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block012Part005CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block012Part005SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block012Part005] using hcert

def TailChunk000Sub001Block012Part006SupportExplicit : Finset ℕ :=
  ([8774] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block012Part006 : ℚ :=
  (30551818353 : ℚ) / 10775291352678400

def SurrogateDiagonalTailChunk000Sub001Block012Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8774
    = surrogateDiagTailX0RatChunk000Sub001Block012Part006

theorem surrogateDiagonalTailChunk000Sub001Block012Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block012Part006CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block012Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block012Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block012Part006CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block012Part006SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block012Part006] using hcert

def TailChunk000Sub001Block012Part007SupportExplicit : Finset ℕ :=
  ([8777] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block012Part007 : ℚ :=
  (651931789 : ℚ) / 1895265113227200

def SurrogateDiagonalTailChunk000Sub001Block012Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8777
    = surrogateDiagTailX0RatChunk000Sub001Block012Part007

theorem surrogateDiagonalTailChunk000Sub001Block012Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block012Part007CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block012Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block012Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block012Part007CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block012Part007SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block012Part007] using hcert

def TailChunk000Sub001Block012Part008SupportExplicit : Finset ℕ :=
  ([8778] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block012Part008 : ℚ :=
  (11939557379 : ℚ) / 725739230822400

def SurrogateDiagonalTailChunk000Sub001Block012Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8778
    = surrogateDiagTailX0RatChunk000Sub001Block012Part008

theorem surrogateDiagonalTailChunk000Sub001Block012Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block012Part008CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block012Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block012Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block012Part008CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block012Part008SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block012Part008] using hcert

def TailChunk000Sub001Block012Part009SupportExplicit : Finset ℕ :=
  ([8779] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block012Part009 : ℚ :=
  (1204231890625 : ℚ) / 3711497510562308082

def SurrogateDiagonalTailChunk000Sub001Block012Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8779
    = surrogateDiagTailX0RatChunk000Sub001Block012Part009

theorem surrogateDiagonalTailChunk000Sub001Block012Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block012Part009CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block012Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block012Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block012Part009CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block012Part009SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block012Part009] using hcert

def TailChunk000Sub001Block012Part010SupportExplicit : Finset ℕ :=
  ([8781] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block012Part010 : ℚ :=
  (669128547025 : ℚ) / 733135310728357152

def SurrogateDiagonalTailChunk000Sub001Block012Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8781
    = surrogateDiagTailX0RatChunk000Sub001Block012Part010

theorem surrogateDiagonalTailChunk000Sub001Block012Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block012Part010CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block012Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block012Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block012Part010CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block012Part010SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block012Part010] using hcert

def TailChunk000Sub001Block012Part011SupportExplicit : Finset ℕ :=
  ([8782] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block012Part011 : ℚ :=
  (96385124119 : ℚ) / 37148812117768200

def SurrogateDiagonalTailChunk000Sub001Block012Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8782
    = surrogateDiagTailX0RatChunk000Sub001Block012Part011

theorem surrogateDiagonalTailChunk000Sub001Block012Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block012Part011CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block012Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block012Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block012Part011CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block012Part011SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block012Part011] using hcert

def TailChunk000Sub001Block012Part012SupportExplicit : Finset ℕ :=
  ([8783] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block012Part012 : ℚ :=
  (1205329515625 : ℚ) / 3718267226105882322

def SurrogateDiagonalTailChunk000Sub001Block012Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8783
    = surrogateDiagTailX0RatChunk000Sub001Block012Part012

theorem surrogateDiagonalTailChunk000Sub001Block012Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block012Part012CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block012Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block012Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block012Part012CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block012Part012SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block012Part012] using hcert

def TailChunk000Sub001Block012Part013SupportExplicit : Finset ℕ :=
  ([8785] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block012Part013 : ℚ :=
  (13887072767 : ℚ) / 16203240000000000

def SurrogateDiagonalTailChunk000Sub001Block012Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8785
    = surrogateDiagTailX0RatChunk000Sub001Block012Part013

theorem surrogateDiagonalTailChunk000Sub001Block012Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block012Part013CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block012Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block012Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block012Part013CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block012Part013SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block012Part013] using hcert

def TailChunk000Sub001Block012Part014SupportExplicit : Finset ℕ :=
  ([8786] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block012Part014 : ℚ :=
  (46219591117 : ℚ) / 30534581871235200

def SurrogateDiagonalTailChunk000Sub001Block012Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8786
    = surrogateDiagTailX0RatChunk000Sub001Block012Part014

theorem surrogateDiagonalTailChunk000Sub001Block012Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block012Part014CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block012Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block012Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block012Part014CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block012Part014SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block012Part014] using hcert

def TailChunk000Sub001Block012Part015SupportExplicit : Finset ℕ :=
  ([8787] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block012Part015 : ℚ :=
  (101026604479 : ℚ) / 98364628992000000

def SurrogateDiagonalTailChunk000Sub001Block012Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8787
    = surrogateDiagTailX0RatChunk000Sub001Block012Part015

theorem surrogateDiagonalTailChunk000Sub001Block012Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block012Part015CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block012Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block012Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block012Part015CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block012Part015SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block012Part015] using hcert

def TailChunk000Sub001Block012Part016SupportExplicit : Finset ℕ :=
  ([8789] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block012Part016 : ℚ :=
  (75116666813 : ℚ) / 146746621663641600

def SurrogateDiagonalTailChunk000Sub001Block012Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8789
    = surrogateDiagTailX0RatChunk000Sub001Block012Part016

theorem surrogateDiagonalTailChunk000Sub001Block012Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block012Part016CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block012Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block012Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block012Part016CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block012Part016SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block012Part016] using hcert

def TailChunk000Sub001Block012Part017SupportExplicit : Finset ℕ :=
  ([8790] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block012Part017 : ℚ :=
  (334375017425 : ℚ) / 37229586872008704

def SurrogateDiagonalTailChunk000Sub001Block012Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8790
    = surrogateDiagTailX0RatChunk000Sub001Block012Part017

theorem surrogateDiagonalTailChunk000Sub001Block012Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block012Part017CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block012Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block012Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block012Part017CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block012Part017SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block012Part017] using hcert

def TailChunk000Sub001Block012Part018SupportExplicit : Finset ℕ :=
  ([8791] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block012Part018 : ℚ :=
  (1556406911775 : ℚ) / 4525477812682233856

def SurrogateDiagonalTailChunk000Sub001Block012Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8791
    = surrogateDiagTailX0RatChunk000Sub001Block012Part018

theorem surrogateDiagonalTailChunk000Sub001Block012Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block012Part018CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block012Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block012Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block012Part018CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block012Part018SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block012Part018] using hcert

def TailChunk000Sub001Block012Part019SupportExplicit : Finset ℕ :=
  ([8794] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block012Part019 : ℚ :=
  (302087640625 : ℚ) / 233452001960339232

def SurrogateDiagonalTailChunk000Sub001Block012Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8794
    = surrogateDiagTailX0RatChunk000Sub001Block012Part019

theorem surrogateDiagonalTailChunk000Sub001Block012Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block012Part019CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block012Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block012Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block012Part019CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block012Part019SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block012Part019] using hcert

def TailChunk000Sub001Block012Part020SupportExplicit : Finset ℕ :=
  ([8795] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block012Part020 : ℚ :=
  (3478675649425 : ℚ) / 6114237539368716288

def SurrogateDiagonalTailChunk000Sub001Block012Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8795
    = surrogateDiagTailX0RatChunk000Sub001Block012Part020

theorem surrogateDiagonalTailChunk000Sub001Block012Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block012Part020CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block012Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block012Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block012Part020CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block012Part020SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block012Part020] using hcert

def TailChunk000Sub001Block012Part021SupportExplicit : Finset ℕ :=
  ([8797] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block012Part021 : ℚ :=
  (123943468975 : ℚ) / 332186730942816288

def SurrogateDiagonalTailChunk000Sub001Block012Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8797
    = surrogateDiagTailX0RatChunk000Sub001Block012Part021

theorem surrogateDiagonalTailChunk000Sub001Block012Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block012Part021CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block012Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block012Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block012Part021CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block012Part021SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block012Part021] using hcert

def TailChunk000Sub001Block012Part022SupportExplicit : Finset ℕ :=
  ([8798] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block012Part022 : ℚ :=
  (392523475875 : ℚ) / 275533486875252736

def SurrogateDiagonalTailChunk000Sub001Block012Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8798
    = surrogateDiagTailX0RatChunk000Sub001Block012Part022

theorem surrogateDiagonalTailChunk000Sub001Block012Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block012Part022CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block012Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block012Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block012Part022CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block012Part022SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block012Part022] using hcert

def TailChunk000Sub001Block012Part023SupportExplicit : Finset ℕ :=
  ([8799] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block012Part023 : ℚ :=
  (2177194029625 : ℚ) / 1582912724204832768

def SurrogateDiagonalTailChunk000Sub001Block012Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8799
    = surrogateDiagTailX0RatChunk000Sub001Block012Part023

theorem surrogateDiagonalTailChunk000Sub001Block012Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block012Part023CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block012Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block012Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block012Part023CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block012Part023SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block012Part023] using hcert

def TailChunk000Sub001Block012Part024SupportExplicit : Finset ℕ :=
  ([8801] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block012Part024 : ℚ :=
  (4288545861775 : ℚ) / 10827760146625363968

def SurrogateDiagonalTailChunk000Sub001Block012Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8801
    = surrogateDiagTailX0RatChunk000Sub001Block012Part024

theorem surrogateDiagonalTailChunk000Sub001Block012Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block012Part024CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block012Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block012Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block012Part024CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block012Part024SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block012Part024] using hcert

def surrogateDiagonalTailChunk000Sub001Block012HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block012Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block012Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block012Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block012Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block012Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block012Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block012Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block012Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block012Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block012Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block012Head : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block012Part000
    + surrogateDiagTailX0RatChunk000Sub001Block012Part001
    + surrogateDiagTailX0RatChunk000Sub001Block012Part002
    + surrogateDiagTailX0RatChunk000Sub001Block012Part003
    + surrogateDiagTailX0RatChunk000Sub001Block012Part004
    + surrogateDiagTailX0RatChunk000Sub001Block012Part005
    + surrogateDiagTailX0RatChunk000Sub001Block012Part006
    + surrogateDiagTailX0RatChunk000Sub001Block012Part007
    + surrogateDiagTailX0RatChunk000Sub001Block012Part008
    + surrogateDiagTailX0RatChunk000Sub001Block012Part009

def surrogateDiagonalTailChunk000Sub001Block012MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block012Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block012Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block012Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block012Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block012Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block012Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block012Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block012Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block012Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block012Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block012Mid : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block012Part010
    + surrogateDiagTailX0RatChunk000Sub001Block012Part011
    + surrogateDiagTailX0RatChunk000Sub001Block012Part012
    + surrogateDiagTailX0RatChunk000Sub001Block012Part013
    + surrogateDiagTailX0RatChunk000Sub001Block012Part014
    + surrogateDiagTailX0RatChunk000Sub001Block012Part015
    + surrogateDiagTailX0RatChunk000Sub001Block012Part016
    + surrogateDiagTailX0RatChunk000Sub001Block012Part017
    + surrogateDiagTailX0RatChunk000Sub001Block012Part018
    + surrogateDiagTailX0RatChunk000Sub001Block012Part019

def surrogateDiagonalTailChunk000Sub001Block012TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block012Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block012Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block012Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block012Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block012Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block012Tail : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block012Part020
    + surrogateDiagTailX0RatChunk000Sub001Block012Part021
    + surrogateDiagTailX0RatChunk000Sub001Block012Part022
    + surrogateDiagTailX0RatChunk000Sub001Block012Part023
    + surrogateDiagTailX0RatChunk000Sub001Block012Part024

def surrogateDiagonalTailChunk000Sub001Block012Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub001Block012HeadSum X0
    + surrogateDiagonalTailChunk000Sub001Block012MidSum X0
    + surrogateDiagonalTailChunk000Sub001Block012TailSum X0

def surrogateDiagTailX0RatChunk000Sub001Block012 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block012Part000
    + surrogateDiagTailX0RatChunk000Sub001Block012Part001
    + surrogateDiagTailX0RatChunk000Sub001Block012Part002
    + surrogateDiagTailX0RatChunk000Sub001Block012Part003
    + surrogateDiagTailX0RatChunk000Sub001Block012Part004
    + surrogateDiagTailX0RatChunk000Sub001Block012Part005
    + surrogateDiagTailX0RatChunk000Sub001Block012Part006
    + surrogateDiagTailX0RatChunk000Sub001Block012Part007
    + surrogateDiagTailX0RatChunk000Sub001Block012Part008
    + surrogateDiagTailX0RatChunk000Sub001Block012Part009
    + surrogateDiagTailX0RatChunk000Sub001Block012Part010
    + surrogateDiagTailX0RatChunk000Sub001Block012Part011
    + surrogateDiagTailX0RatChunk000Sub001Block012Part012
    + surrogateDiagTailX0RatChunk000Sub001Block012Part013
    + surrogateDiagTailX0RatChunk000Sub001Block012Part014
    + surrogateDiagTailX0RatChunk000Sub001Block012Part015
    + surrogateDiagTailX0RatChunk000Sub001Block012Part016
    + surrogateDiagTailX0RatChunk000Sub001Block012Part017
    + surrogateDiagTailX0RatChunk000Sub001Block012Part018
    + surrogateDiagTailX0RatChunk000Sub001Block012Part019
    + surrogateDiagTailX0RatChunk000Sub001Block012Part020
    + surrogateDiagTailX0RatChunk000Sub001Block012Part021
    + surrogateDiagTailX0RatChunk000Sub001Block012Part022
    + surrogateDiagTailX0RatChunk000Sub001Block012Part023
    + surrogateDiagTailX0RatChunk000Sub001Block012Part024

theorem surrogateDiagTailX0RatChunk000Sub001Block012_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk000Sub001Block012Head + surrogateDiagTailX0RatChunk000Sub001Block012Mid + surrogateDiagTailX0RatChunk000Sub001Block012Tail =
      surrogateDiagTailX0RatChunk000Sub001Block012 := by
  unfold surrogateDiagTailX0RatChunk000Sub001Block012Head surrogateDiagTailX0RatChunk000Sub001Block012Mid surrogateDiagTailX0RatChunk000Sub001Block012Tail surrogateDiagTailX0RatChunk000Sub001Block012
  ring

def SurrogateDiagonalTailChunk000Sub001Block012HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block012HeadSum X0 = surrogateDiagTailX0RatChunk000Sub001Block012Head

def SurrogateDiagonalTailChunk000Sub001Block012MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block012MidSum X0 = surrogateDiagTailX0RatChunk000Sub001Block012Mid

def SurrogateDiagonalTailChunk000Sub001Block012TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block012TailSum X0 = surrogateDiagTailX0RatChunk000Sub001Block012Tail

theorem surrogateDiagonalTailChunk000Sub001Block012_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk000Sub001Block012HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk000Sub001Block012MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk000Sub001Block012TailCertificateAt X0) :
    surrogateDiagonalTailChunk000Sub001Block012Sum X0 = surrogateDiagTailX0RatChunk000Sub001Block012 := by
  unfold SurrogateDiagonalTailChunk000Sub001Block012HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk000Sub001Block012MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk000Sub001Block012TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk000Sub001Block012Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk000Sub001Block012_eq_head_add_mid_add_tail

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

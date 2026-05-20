import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0TailPilot25

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

open scoped BigOperators

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

/- Generated direct-term certificate blocks for tail chunk 000, subchunk 001, blocks [15,16). -/

/-- Block 015 covers tail-support indices [5375,5400) and q from 8886 to 8923. -/

def TailChunk000Sub001Block015Part000SupportExplicit : Finset ℕ :=
  ([8886] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block015Part000 : ℚ :=
  (3288099 : ℚ) / 767656345600

def SurrogateDiagonalTailChunk000Sub001Block015Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8886
    = surrogateDiagTailX0RatChunk000Sub001Block015Part000

theorem surrogateDiagonalTailChunk000Sub001Block015Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block015Part000CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block015Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block015Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block015Part000CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block015Part000SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block015Part000] using hcert

def TailChunk000Sub001Block015Part001SupportExplicit : Finset ℕ :=
  ([8887] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block015Part001 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block015Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8887
    = surrogateDiagTailX0RatChunk000Sub001Block015Part001

theorem surrogateDiagonalTailChunk000Sub001Block015Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block015Part001CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block015Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block015Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block015Part001CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block015Part001SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block015Part001] using hcert

def TailChunk000Sub001Block015Part002SupportExplicit : Finset ℕ :=
  ([8889] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block015Part002 : ℚ :=
  (548542996325 : ℚ) / 1539774285701204544

def SurrogateDiagonalTailChunk000Sub001Block015Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8889
    = surrogateDiagTailX0RatChunk000Sub001Block015Part002

theorem surrogateDiagonalTailChunk000Sub001Block015Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block015Part002CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block015Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block015Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block015Part002CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block015Part002SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block015Part002] using hcert

def TailChunk000Sub001Block015Part003SupportExplicit : Finset ℕ :=
  ([8890] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block015Part003 : ℚ :=
  (894686612125 : ℚ) / 209099987184549888

def SurrogateDiagonalTailChunk000Sub001Block015Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8890
    = surrogateDiagTailX0RatChunk000Sub001Block015Part003

theorem surrogateDiagonalTailChunk000Sub001Block015Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block015Part003CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block015Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block015Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block015Part003CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block015Part003SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block015Part003] using hcert

def TailChunk000Sub001Block015Part004SupportExplicit : Finset ℕ :=
  ([8891] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block015Part004 : ℚ :=
  (5852775325 : ℚ) / 450635122230165504

def SurrogateDiagonalTailChunk000Sub001Block015Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8891
    = surrogateDiagTailX0RatChunk000Sub001Block015Part004

theorem surrogateDiagonalTailChunk000Sub001Block015Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block015Part004CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block015Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block015Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block015Part004CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block015Part004SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block015Part004] using hcert

def TailChunk000Sub001Block015Part005SupportExplicit : Finset ℕ :=
  ([8893] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block015Part005 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block015Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8893
    = surrogateDiagTailX0RatChunk000Sub001Block015Part005

theorem surrogateDiagonalTailChunk000Sub001Block015Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block015Part005CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block015Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block015Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block015Part005CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block015Part005SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block015Part005] using hcert

def TailChunk000Sub001Block015Part006SupportExplicit : Finset ℕ :=
  ([8894] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block015Part006 : ℚ :=
  (308997015625 : ℚ) / 244255696465428882

def SurrogateDiagonalTailChunk000Sub001Block015Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8894
    = surrogateDiagTailX0RatChunk000Sub001Block015Part006

theorem surrogateDiagonalTailChunk000Sub001Block015Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block015Part006CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block015Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block015Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block015Part006CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block015Part006SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block015Part006] using hcert

def TailChunk000Sub001Block015Part007SupportExplicit : Finset ℕ :=
  ([8895] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block015Part007 : ℚ :=
  (322062165075 : ℚ) / 419326567420788736

def SurrogateDiagonalTailChunk000Sub001Block015Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8895
    = surrogateDiagTailX0RatChunk000Sub001Block015Part007

theorem surrogateDiagonalTailChunk000Sub001Block015Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block015Part007CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block015Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block015Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block015Part007CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block015Part007SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block015Part007] using hcert

def TailChunk000Sub001Block015Part008SupportExplicit : Finset ℕ :=
  ([8897] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block015Part008 : ℚ :=
  (2434857101 : ℚ) / 33599038464000000

def SurrogateDiagonalTailChunk000Sub001Block015Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8897
    = surrogateDiagTailX0RatChunk000Sub001Block015Part008

theorem surrogateDiagonalTailChunk000Sub001Block015Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block015Part008CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block015Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block015Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block015Part008CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block015Part008SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block015Part008] using hcert

def TailChunk000Sub001Block015Part009SupportExplicit : Finset ℕ :=
  ([8898] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block015Part009 : ℚ :=
  (27474875 : ℚ) / 6431785483968

def SurrogateDiagonalTailChunk000Sub001Block015Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8898
    = surrogateDiagTailX0RatChunk000Sub001Block015Part009

theorem surrogateDiagonalTailChunk000Sub001Block015Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block015Part009CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block015Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block015Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block015Part009CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block015Part009SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block015Part009] using hcert

def TailChunk000Sub001Block015Part010SupportExplicit : Finset ℕ :=
  ([8899] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block015Part010 : ℚ :=
  (990824353 : ℚ) / 42631664877649920

def SurrogateDiagonalTailChunk000Sub001Block015Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8899
    = surrogateDiagTailX0RatChunk000Sub001Block015Part010

theorem surrogateDiagonalTailChunk000Sub001Block015Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block015Part010CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block015Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block015Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block015Part010CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block015Part010SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block015Part010] using hcert

def TailChunk000Sub001Block015Part011SupportExplicit : Finset ℕ :=
  ([8902] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block015Part011 : ℚ :=
  (19811401 : ℚ) / 15688697362050

def SurrogateDiagonalTailChunk000Sub001Block015Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8902
    = surrogateDiagTailX0RatChunk000Sub001Block015Part011

theorem surrogateDiagonalTailChunk000Sub001Block015Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block015Part011CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block015Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block015Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block015Part011CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block015Part011SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block015Part011] using hcert

def TailChunk000Sub001Block015Part012SupportExplicit : Finset ℕ :=
  ([8903] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block015Part012 : ℚ :=
  (2430601975 : ℚ) / 320845091667416064

def SurrogateDiagonalTailChunk000Sub001Block015Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8903
    = surrogateDiagTailX0RatChunk000Sub001Block015Part012

theorem surrogateDiagonalTailChunk000Sub001Block015Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block015Part012CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block015Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block015Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block015Part012CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block015Part012SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block015Part012] using hcert

def TailChunk000Sub001Block015Part013SupportExplicit : Finset ℕ :=
  ([8905] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block015Part013 : ℚ :=
  (692119322575 : ℚ) / 4540957548324323328

def SurrogateDiagonalTailChunk000Sub001Block015Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8905
    = surrogateDiagTailX0RatChunk000Sub001Block015Part013

theorem surrogateDiagonalTailChunk000Sub001Block015Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block015Part013CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block015Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block015Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block015Part013CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block015Part013SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block015Part013] using hcert

def TailChunk000Sub001Block015Part014SupportExplicit : Finset ℕ :=
  ([8906] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block015Part014 : ℚ :=
  (24137486009 : ℚ) / 17417741539737600

def SurrogateDiagonalTailChunk000Sub001Block015Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8906
    = surrogateDiagTailX0RatChunk000Sub001Block015Part014

theorem surrogateDiagonalTailChunk000Sub001Block015Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block015Part014CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block015Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block015Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block015Part014CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block015Part014SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block015Part014] using hcert

def TailChunk000Sub001Block015Part015SupportExplicit : Finset ℕ :=
  ([8907] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block015Part015 : ℚ :=
  (550766301275 : ℚ) / 1552288472266850304

def SurrogateDiagonalTailChunk000Sub001Block015Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8907
    = surrogateDiagTailX0RatChunk000Sub001Block015Part015

theorem surrogateDiagonalTailChunk000Sub001Block015Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block015Part015CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block015Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block015Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block015Part015CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block015Part015SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block015Part015] using hcert

def TailChunk000Sub001Block015Part016SupportExplicit : Finset ℕ :=
  ([8909] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block015Part016 : ℚ :=
  (2571339157 : ℚ) / 573012189522000000

def SurrogateDiagonalTailChunk000Sub001Block015Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8909
    = surrogateDiagTailX0RatChunk000Sub001Block015Part016

theorem surrogateDiagonalTailChunk000Sub001Block015Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block015Part016CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block015Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block015Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block015Part016CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block015Part016SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block015Part016] using hcert

def TailChunk000Sub001Block015Part017SupportExplicit : Finset ℕ :=
  ([8911] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block015Part017 : ℚ :=
  (1034087575 : ℚ) / 13336819127419392

def SurrogateDiagonalTailChunk000Sub001Block015Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8911
    = surrogateDiagTailX0RatChunk000Sub001Block015Part017

theorem surrogateDiagonalTailChunk000Sub001Block015Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block015Part017CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block015Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block015Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block015Part017CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block015Part017SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block015Part017] using hcert

def TailChunk000Sub001Block015Part018SupportExplicit : Finset ℕ :=
  ([8913] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block015Part018 : ℚ :=
  (2207725453 : ℚ) / 12451814154457920

def SurrogateDiagonalTailChunk000Sub001Block015Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8913
    = surrogateDiagTailX0RatChunk000Sub001Block015Part018

theorem surrogateDiagonalTailChunk000Sub001Block015Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block015Part018CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block015Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block015Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block015Part018CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block015Part018SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block015Part018] using hcert

def TailChunk000Sub001Block015Part019SupportExplicit : Finset ℕ :=
  ([8914] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block015Part019 : ℚ :=
  (310388265625 : ℚ) / 246460653796864512

def SurrogateDiagonalTailChunk000Sub001Block015Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8914
    = surrogateDiagTailX0RatChunk000Sub001Block015Part019

theorem surrogateDiagonalTailChunk000Sub001Block015Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block015Part019CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block015Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block015Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block015Part019CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block015Part019SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block015Part019] using hcert

def TailChunk000Sub001Block015Part020SupportExplicit : Finset ℕ :=
  ([8915] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block015Part020 : ℚ :=
  (74552839025 : ℚ) / 806877557208873216

def SurrogateDiagonalTailChunk000Sub001Block015Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8915
    = surrogateDiagTailX0RatChunk000Sub001Block015Part020

theorem surrogateDiagonalTailChunk000Sub001Block015Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block015Part020CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block015Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block015Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block015Part020CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block015Part020SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block015Part020] using hcert

def TailChunk000Sub001Block015Part021SupportExplicit : Finset ℕ :=
  ([8917] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block015Part021 : ℚ :=
  (38460341 : ℚ) / 6192974769684480

def SurrogateDiagonalTailChunk000Sub001Block015Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8917
    = surrogateDiagTailX0RatChunk000Sub001Block015Part021

theorem surrogateDiagonalTailChunk000Sub001Block015Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block015Part021CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block015Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block015Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block015Part021CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block015Part021SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block015Part021] using hcert

def TailChunk000Sub001Block015Part022SupportExplicit : Finset ℕ :=
  ([8921] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block015Part022 : ℚ :=
  (995673487 : ℚ) / 43055330344200000

def SurrogateDiagonalTailChunk000Sub001Block015Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8921
    = surrogateDiagTailX0RatChunk000Sub001Block015Part022

theorem surrogateDiagonalTailChunk000Sub001Block015Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block015Part022CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block015Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block015Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block015Part022CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block015Part022SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block015Part022] using hcert

def TailChunk000Sub001Block015Part023SupportExplicit : Finset ℕ :=
  ([8922] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block015Part023 : ℚ :=
  (82869825 : ℚ) / 19504518297664

def SurrogateDiagonalTailChunk000Sub001Block015Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8922
    = surrogateDiagTailX0RatChunk000Sub001Block015Part023

theorem surrogateDiagonalTailChunk000Sub001Block015Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block015Part023CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block015Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block015Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block015Part023CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block015Part023SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block015Part023] using hcert

def TailChunk000Sub001Block015Part024SupportExplicit : Finset ℕ :=
  ([8923] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block015Part024 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block015Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8923
    = surrogateDiagTailX0RatChunk000Sub001Block015Part024

theorem surrogateDiagonalTailChunk000Sub001Block015Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block015Part024CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block015Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block015Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block015Part024CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block015Part024SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block015Part024] using hcert

def surrogateDiagonalTailChunk000Sub001Block015HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block015Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block015Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block015Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block015Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block015Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block015Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block015Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block015Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block015Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block015Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block015Head : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block015Part000
    + surrogateDiagTailX0RatChunk000Sub001Block015Part001
    + surrogateDiagTailX0RatChunk000Sub001Block015Part002
    + surrogateDiagTailX0RatChunk000Sub001Block015Part003
    + surrogateDiagTailX0RatChunk000Sub001Block015Part004
    + surrogateDiagTailX0RatChunk000Sub001Block015Part005
    + surrogateDiagTailX0RatChunk000Sub001Block015Part006
    + surrogateDiagTailX0RatChunk000Sub001Block015Part007
    + surrogateDiagTailX0RatChunk000Sub001Block015Part008
    + surrogateDiagTailX0RatChunk000Sub001Block015Part009

def surrogateDiagonalTailChunk000Sub001Block015MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block015Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block015Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block015Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block015Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block015Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block015Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block015Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block015Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block015Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block015Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block015Mid : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block015Part010
    + surrogateDiagTailX0RatChunk000Sub001Block015Part011
    + surrogateDiagTailX0RatChunk000Sub001Block015Part012
    + surrogateDiagTailX0RatChunk000Sub001Block015Part013
    + surrogateDiagTailX0RatChunk000Sub001Block015Part014
    + surrogateDiagTailX0RatChunk000Sub001Block015Part015
    + surrogateDiagTailX0RatChunk000Sub001Block015Part016
    + surrogateDiagTailX0RatChunk000Sub001Block015Part017
    + surrogateDiagTailX0RatChunk000Sub001Block015Part018
    + surrogateDiagTailX0RatChunk000Sub001Block015Part019

def surrogateDiagonalTailChunk000Sub001Block015TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block015Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block015Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block015Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block015Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block015Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block015Tail : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block015Part020
    + surrogateDiagTailX0RatChunk000Sub001Block015Part021
    + surrogateDiagTailX0RatChunk000Sub001Block015Part022
    + surrogateDiagTailX0RatChunk000Sub001Block015Part023
    + surrogateDiagTailX0RatChunk000Sub001Block015Part024

def surrogateDiagonalTailChunk000Sub001Block015Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub001Block015HeadSum X0
    + surrogateDiagonalTailChunk000Sub001Block015MidSum X0
    + surrogateDiagonalTailChunk000Sub001Block015TailSum X0

def surrogateDiagTailX0RatChunk000Sub001Block015 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block015Part000
    + surrogateDiagTailX0RatChunk000Sub001Block015Part001
    + surrogateDiagTailX0RatChunk000Sub001Block015Part002
    + surrogateDiagTailX0RatChunk000Sub001Block015Part003
    + surrogateDiagTailX0RatChunk000Sub001Block015Part004
    + surrogateDiagTailX0RatChunk000Sub001Block015Part005
    + surrogateDiagTailX0RatChunk000Sub001Block015Part006
    + surrogateDiagTailX0RatChunk000Sub001Block015Part007
    + surrogateDiagTailX0RatChunk000Sub001Block015Part008
    + surrogateDiagTailX0RatChunk000Sub001Block015Part009
    + surrogateDiagTailX0RatChunk000Sub001Block015Part010
    + surrogateDiagTailX0RatChunk000Sub001Block015Part011
    + surrogateDiagTailX0RatChunk000Sub001Block015Part012
    + surrogateDiagTailX0RatChunk000Sub001Block015Part013
    + surrogateDiagTailX0RatChunk000Sub001Block015Part014
    + surrogateDiagTailX0RatChunk000Sub001Block015Part015
    + surrogateDiagTailX0RatChunk000Sub001Block015Part016
    + surrogateDiagTailX0RatChunk000Sub001Block015Part017
    + surrogateDiagTailX0RatChunk000Sub001Block015Part018
    + surrogateDiagTailX0RatChunk000Sub001Block015Part019
    + surrogateDiagTailX0RatChunk000Sub001Block015Part020
    + surrogateDiagTailX0RatChunk000Sub001Block015Part021
    + surrogateDiagTailX0RatChunk000Sub001Block015Part022
    + surrogateDiagTailX0RatChunk000Sub001Block015Part023
    + surrogateDiagTailX0RatChunk000Sub001Block015Part024

theorem surrogateDiagTailX0RatChunk000Sub001Block015_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk000Sub001Block015Head + surrogateDiagTailX0RatChunk000Sub001Block015Mid + surrogateDiagTailX0RatChunk000Sub001Block015Tail =
      surrogateDiagTailX0RatChunk000Sub001Block015 := by
  unfold surrogateDiagTailX0RatChunk000Sub001Block015Head surrogateDiagTailX0RatChunk000Sub001Block015Mid surrogateDiagTailX0RatChunk000Sub001Block015Tail surrogateDiagTailX0RatChunk000Sub001Block015
  ring

def SurrogateDiagonalTailChunk000Sub001Block015HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block015HeadSum X0 = surrogateDiagTailX0RatChunk000Sub001Block015Head

def SurrogateDiagonalTailChunk000Sub001Block015MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block015MidSum X0 = surrogateDiagTailX0RatChunk000Sub001Block015Mid

def SurrogateDiagonalTailChunk000Sub001Block015TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block015TailSum X0 = surrogateDiagTailX0RatChunk000Sub001Block015Tail

theorem surrogateDiagonalTailChunk000Sub001Block015_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk000Sub001Block015HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk000Sub001Block015MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk000Sub001Block015TailCertificateAt X0) :
    surrogateDiagonalTailChunk000Sub001Block015Sum X0 = surrogateDiagTailX0RatChunk000Sub001Block015 := by
  unfold SurrogateDiagonalTailChunk000Sub001Block015HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk000Sub001Block015MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk000Sub001Block015TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk000Sub001Block015Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk000Sub001Block015_eq_head_add_mid_add_tail

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

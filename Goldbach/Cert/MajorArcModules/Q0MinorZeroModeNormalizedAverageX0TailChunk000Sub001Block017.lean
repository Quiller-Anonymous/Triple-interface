import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0TailPilot25

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

open scoped BigOperators

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

/- Generated direct-term certificate blocks for tail chunk 000, subchunk 001, blocks [17,18). -/

/-- Block 017 covers tail-support indices [5425,5450) and q from 8970 to 9011. -/

def TailChunk000Sub001Block017Part000SupportExplicit : Finset ℕ :=
  ([8970] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block017Part000 : ℚ :=
  (604214059975 : ℚ) / 49751080166227968

def SurrogateDiagonalTailChunk000Sub001Block017Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8970
    = surrogateDiagTailX0RatChunk000Sub001Block017Part000

theorem surrogateDiagonalTailChunk000Sub001Block017Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block017Part000CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block017Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block017Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block017Part000CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block017Part000SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block017Part000] using hcert

def TailChunk000Sub001Block017Part001SupportExplicit : Finset ℕ :=
  ([8971] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block017Part001 : ℚ :=
  (2011971025 : ℚ) / 6475251220095762

def SurrogateDiagonalTailChunk000Sub001Block017Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8971
    = surrogateDiagTailX0RatChunk000Sub001Block017Part001

theorem surrogateDiagonalTailChunk000Sub001Block017Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block017Part001CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block017Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block017Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block017Part001CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block017Part001SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block017Part001] using hcert

def TailChunk000Sub001Block017Part002SupportExplicit : Finset ℕ :=
  ([8974] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block017Part002 : ℚ :=
  (478794323 : ℚ) / 241640228782080

def SurrogateDiagonalTailChunk000Sub001Block017Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8974
    = surrogateDiagTailX0RatChunk000Sub001Block017Part002

theorem surrogateDiagonalTailChunk000Sub001Block017Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block017Part002CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block017Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block017Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block017Part002CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block017Part002SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block017Part002] using hcert

def TailChunk000Sub001Block017Part003SupportExplicit : Finset ℕ :=
  ([8977] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block017Part003 : ℚ :=
  (7752940525 : ℚ) / 23344929787387008

def SurrogateDiagonalTailChunk000Sub001Block017Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8977
    = surrogateDiagTailX0RatChunk000Sub001Block017Part003

theorem surrogateDiagonalTailChunk000Sub001Block017Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block017Part003CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block017Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block017Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block017Part003CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block017Part003SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block017Part003] using hcert

def TailChunk000Sub001Block017Part004SupportExplicit : Finset ℕ :=
  ([8979] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block017Part004 : ℚ :=
  (85602689077 : ℚ) / 110097329238835200

def SurrogateDiagonalTailChunk000Sub001Block017Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8979
    = surrogateDiagTailX0RatChunk000Sub001Block017Part004

theorem surrogateDiagonalTailChunk000Sub001Block017Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block017Part004CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block017Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block017Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block017Part004CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block017Part004SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block017Part004] using hcert

def TailChunk000Sub001Block017Part005SupportExplicit : Finset ℕ :=
  ([8981] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block017Part005 : ℚ :=
  (222698770475 : ℚ) / 486308047104668736

def SurrogateDiagonalTailChunk000Sub001Block017Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8981
    = surrogateDiagTailX0RatChunk000Sub001Block017Part005

theorem surrogateDiagonalTailChunk000Sub001Block017Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block017Part005CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block017Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block017Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block017Part005CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block017Part005SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block017Part005] using hcert

def TailChunk000Sub001Block017Part006SupportExplicit : Finset ℕ :=
  ([8983] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block017Part006 : ℚ :=
  (178714424371 : ℚ) / 470119426140211200

def SurrogateDiagonalTailChunk000Sub001Block017Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8983
    = surrogateDiagTailX0RatChunk000Sub001Block017Part006

theorem surrogateDiagonalTailChunk000Sub001Block017Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block017Part006CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block017Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block017Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block017Part006CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block017Part006SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block017Part006] using hcert

def TailChunk000Sub001Block017Part007SupportExplicit : Finset ℕ :=
  ([8985] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block017Part007 : ℚ :=
  (40026363475 : ℚ) / 25187681858985984

def SurrogateDiagonalTailChunk000Sub001Block017Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8985
    = surrogateDiagTailX0RatChunk000Sub001Block017Part007

theorem surrogateDiagonalTailChunk000Sub001Block017Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block017Part007CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block017Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block017Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block017Part007CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block017Part007SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block017Part007] using hcert

def TailChunk000Sub001Block017Part008SupportExplicit : Finset ℕ :=
  ([8986] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block017Part008 : ℚ :=
  (315422640625 : ℚ) / 254522311025908512

def SurrogateDiagonalTailChunk000Sub001Block017Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8986
    = surrogateDiagTailX0RatChunk000Sub001Block017Part008

theorem surrogateDiagonalTailChunk000Sub001Block017Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block017Part008CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block017Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block017Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block017Part008CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block017Part008SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block017Part008] using hcert

def TailChunk000Sub001Block017Part009SupportExplicit : Finset ℕ :=
  ([8987] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block017Part009 : ℚ :=
  (158064487381 : ℚ) / 326718729975859200

def SurrogateDiagonalTailChunk000Sub001Block017Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8987
    = surrogateDiagTailX0RatChunk000Sub001Block017Part009

theorem surrogateDiagonalTailChunk000Sub001Block017Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block017Part009CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block017Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block017Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block017Part009CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block017Part009SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block017Part009] using hcert

def TailChunk000Sub001Block017Part010SupportExplicit : Finset ℕ :=
  ([8989] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block017Part010 : ℚ :=
  (13063540329 : ℚ) / 39987686604800000

def SurrogateDiagonalTailChunk000Sub001Block017Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8989
    = surrogateDiagTailX0RatChunk000Sub001Block017Part010

theorem surrogateDiagonalTailChunk000Sub001Block017Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block017Part010CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block017Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block017Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block017Part010CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block017Part010SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block017Part010] using hcert

def TailChunk000Sub001Block017Part011SupportExplicit : Finset ℕ :=
  ([8990] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block017Part011 : ℚ :=
  (38062874131 : ℚ) / 12748055917363200

def SurrogateDiagonalTailChunk000Sub001Block017Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8990
    = surrogateDiagTailX0RatChunk000Sub001Block017Part011

theorem surrogateDiagonalTailChunk000Sub001Block017Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block017Part011CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block017Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block017Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block017Part011CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block017Part011SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block017Part011] using hcert

def TailChunk000Sub001Block017Part012SupportExplicit : Finset ℕ :=
  ([8994] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block017Part012 : ℚ :=
  (1718625 : ℚ) / 411065628736

def SurrogateDiagonalTailChunk000Sub001Block017Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8994
    = surrogateDiagTailX0RatChunk000Sub001Block017Part012

theorem surrogateDiagonalTailChunk000Sub001Block017Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block017Part012CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block017Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block017Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block017Part012CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block017Part012SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block017Part012] using hcert

def TailChunk000Sub001Block017Part013SupportExplicit : Finset ℕ :=
  ([8995] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block017Part013 : ℚ :=
  (316709839225 : ℚ) / 395903350836559872

def SurrogateDiagonalTailChunk000Sub001Block017Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8995
    = surrogateDiagTailX0RatChunk000Sub001Block017Part013

theorem surrogateDiagonalTailChunk000Sub001Block017Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block017Part013CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block017Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block017Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block017Part013CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block017Part013SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block017Part013] using hcert

def TailChunk000Sub001Block017Part014SupportExplicit : Finset ℕ :=
  ([8997] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block017Part014 : ℚ :=
  (702456378175 : ℚ) / 808003727471968032

def SurrogateDiagonalTailChunk000Sub001Block017Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8997
    = surrogateDiagTailX0RatChunk000Sub001Block017Part014

theorem surrogateDiagonalTailChunk000Sub001Block017Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block017Part014CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block017Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block017Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block017Part014CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block017Part014SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block017Part014] using hcert

def TailChunk000Sub001Block017Part015SupportExplicit : Finset ℕ :=
  ([8998] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block017Part015 : ℚ :=
  (9265555187 : ℚ) / 5543161069731840

def SurrogateDiagonalTailChunk000Sub001Block017Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8998
    = surrogateDiagTailX0RatChunk000Sub001Block017Part015

theorem surrogateDiagonalTailChunk000Sub001Block017Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block017Part015CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block017Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block017Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block017Part015CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block017Part015SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block017Part015] using hcert

def TailChunk000Sub001Block017Part016SupportExplicit : Finset ℕ :=
  ([8999] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block017Part016 : ℚ :=
  (1265343765625 : ℚ) / 4097800611062974002

def SurrogateDiagonalTailChunk000Sub001Block017Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8999
    = surrogateDiagTailX0RatChunk000Sub001Block017Part016

theorem surrogateDiagonalTailChunk000Sub001Block017Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block017Part016CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block017Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block017Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block017Part016CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block017Part016SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block017Part016] using hcert

def TailChunk000Sub001Block017Part017SupportExplicit : Finset ℕ :=
  ([9001] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block017Part017 : ℚ :=
  (81018001 : ℚ) / 262492488000000

def SurrogateDiagonalTailChunk000Sub001Block017Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9001
    = surrogateDiagTailX0RatChunk000Sub001Block017Part017

theorem surrogateDiagonalTailChunk000Sub001Block017Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block017Part017CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block017Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block017Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block017Part017CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block017Part017SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block017Part017] using hcert

def TailChunk000Sub001Block017Part018SupportExplicit : Finset ℕ :=
  ([9002] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block017Part018 : ℚ :=
  (277444823125 : ℚ) / 137629642370149152

def SurrogateDiagonalTailChunk000Sub001Block017Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9002
    = surrogateDiagTailX0RatChunk000Sub001Block017Part018

theorem surrogateDiagonalTailChunk000Sub001Block017Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block017Part018CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block017Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block017Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block017Part018CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block017Part018SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block017Part018] using hcert

def TailChunk000Sub001Block017Part019SupportExplicit : Finset ℕ :=
  ([9003] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block017Part019 : ℚ :=
  (56271497249 : ℚ) / 64812960000000000

def SurrogateDiagonalTailChunk000Sub001Block017Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9003
    = surrogateDiagTailX0RatChunk000Sub001Block017Part019

theorem surrogateDiagonalTailChunk000Sub001Block017Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block017Part019CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block017Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block017Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block017Part019CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block017Part019SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block017Part019] using hcert

def TailChunk000Sub001Block017Part020SupportExplicit : Finset ℕ :=
  ([9005] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block017Part020 : ℚ :=
  (145872692197 : ℚ) / 268792307712000000

def SurrogateDiagonalTailChunk000Sub001Block017Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9005
    = surrogateDiagTailX0RatChunk000Sub001Block017Part020

theorem surrogateDiagonalTailChunk000Sub001Block017Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block017Part020CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block017Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block017Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block017Part020CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block017Part020SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block017Part020] using hcert

def TailChunk000Sub001Block017Part021SupportExplicit : Finset ℕ :=
  ([9006] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block017Part021 : ℚ :=
  (796130127175 : ℚ) / 155458786286389248

def SurrogateDiagonalTailChunk000Sub001Block017Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9006
    = surrogateDiagTailX0RatChunk000Sub001Block017Part021

theorem surrogateDiagonalTailChunk000Sub001Block017Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block017Part021CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block017Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block017Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block017Part021CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block017Part021SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block017Part021] using hcert

def TailChunk000Sub001Block017Part022SupportExplicit : Finset ℕ :=
  ([9007] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block017Part022 : ℚ :=
  (1267594515625 : ℚ) / 4112393254048782162

def SurrogateDiagonalTailChunk000Sub001Block017Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9007
    = surrogateDiagTailX0RatChunk000Sub001Block017Part022

theorem surrogateDiagonalTailChunk000Sub001Block017Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block017Part022CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block017Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block017Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block017Part022CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block017Part022SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block017Part022] using hcert

def TailChunk000Sub001Block017Part023SupportExplicit : Finset ℕ :=
  ([9010] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block017Part023 : ℚ :=
  (272541606375 : ℚ) / 51122122772185088

def SurrogateDiagonalTailChunk000Sub001Block017Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9010
    = surrogateDiagTailX0RatChunk000Sub001Block017Part023

theorem surrogateDiagonalTailChunk000Sub001Block017Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block017Part023CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block017Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block017Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block017Part023CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block017Part023SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block017Part023] using hcert

def TailChunk000Sub001Block017Part024SupportExplicit : Finset ℕ :=
  ([9011] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block017Part024 : ℚ :=
  (2029953025 : ℚ) / 6591526677737202

def SurrogateDiagonalTailChunk000Sub001Block017Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9011
    = surrogateDiagTailX0RatChunk000Sub001Block017Part024

theorem surrogateDiagonalTailChunk000Sub001Block017Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block017Part024CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block017Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block017Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block017Part024CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block017Part024SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block017Part024] using hcert

def surrogateDiagonalTailChunk000Sub001Block017HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block017Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block017Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block017Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block017Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block017Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block017Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block017Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block017Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block017Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block017Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block017Head : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block017Part000
    + surrogateDiagTailX0RatChunk000Sub001Block017Part001
    + surrogateDiagTailX0RatChunk000Sub001Block017Part002
    + surrogateDiagTailX0RatChunk000Sub001Block017Part003
    + surrogateDiagTailX0RatChunk000Sub001Block017Part004
    + surrogateDiagTailX0RatChunk000Sub001Block017Part005
    + surrogateDiagTailX0RatChunk000Sub001Block017Part006
    + surrogateDiagTailX0RatChunk000Sub001Block017Part007
    + surrogateDiagTailX0RatChunk000Sub001Block017Part008
    + surrogateDiagTailX0RatChunk000Sub001Block017Part009

def surrogateDiagonalTailChunk000Sub001Block017MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block017Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block017Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block017Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block017Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block017Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block017Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block017Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block017Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block017Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block017Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block017Mid : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block017Part010
    + surrogateDiagTailX0RatChunk000Sub001Block017Part011
    + surrogateDiagTailX0RatChunk000Sub001Block017Part012
    + surrogateDiagTailX0RatChunk000Sub001Block017Part013
    + surrogateDiagTailX0RatChunk000Sub001Block017Part014
    + surrogateDiagTailX0RatChunk000Sub001Block017Part015
    + surrogateDiagTailX0RatChunk000Sub001Block017Part016
    + surrogateDiagTailX0RatChunk000Sub001Block017Part017
    + surrogateDiagTailX0RatChunk000Sub001Block017Part018
    + surrogateDiagTailX0RatChunk000Sub001Block017Part019

def surrogateDiagonalTailChunk000Sub001Block017TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block017Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block017Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block017Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block017Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block017Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block017Tail : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block017Part020
    + surrogateDiagTailX0RatChunk000Sub001Block017Part021
    + surrogateDiagTailX0RatChunk000Sub001Block017Part022
    + surrogateDiagTailX0RatChunk000Sub001Block017Part023
    + surrogateDiagTailX0RatChunk000Sub001Block017Part024

def surrogateDiagonalTailChunk000Sub001Block017Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub001Block017HeadSum X0
    + surrogateDiagonalTailChunk000Sub001Block017MidSum X0
    + surrogateDiagonalTailChunk000Sub001Block017TailSum X0

def surrogateDiagTailX0RatChunk000Sub001Block017 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block017Part000
    + surrogateDiagTailX0RatChunk000Sub001Block017Part001
    + surrogateDiagTailX0RatChunk000Sub001Block017Part002
    + surrogateDiagTailX0RatChunk000Sub001Block017Part003
    + surrogateDiagTailX0RatChunk000Sub001Block017Part004
    + surrogateDiagTailX0RatChunk000Sub001Block017Part005
    + surrogateDiagTailX0RatChunk000Sub001Block017Part006
    + surrogateDiagTailX0RatChunk000Sub001Block017Part007
    + surrogateDiagTailX0RatChunk000Sub001Block017Part008
    + surrogateDiagTailX0RatChunk000Sub001Block017Part009
    + surrogateDiagTailX0RatChunk000Sub001Block017Part010
    + surrogateDiagTailX0RatChunk000Sub001Block017Part011
    + surrogateDiagTailX0RatChunk000Sub001Block017Part012
    + surrogateDiagTailX0RatChunk000Sub001Block017Part013
    + surrogateDiagTailX0RatChunk000Sub001Block017Part014
    + surrogateDiagTailX0RatChunk000Sub001Block017Part015
    + surrogateDiagTailX0RatChunk000Sub001Block017Part016
    + surrogateDiagTailX0RatChunk000Sub001Block017Part017
    + surrogateDiagTailX0RatChunk000Sub001Block017Part018
    + surrogateDiagTailX0RatChunk000Sub001Block017Part019
    + surrogateDiagTailX0RatChunk000Sub001Block017Part020
    + surrogateDiagTailX0RatChunk000Sub001Block017Part021
    + surrogateDiagTailX0RatChunk000Sub001Block017Part022
    + surrogateDiagTailX0RatChunk000Sub001Block017Part023
    + surrogateDiagTailX0RatChunk000Sub001Block017Part024

theorem surrogateDiagTailX0RatChunk000Sub001Block017_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk000Sub001Block017Head + surrogateDiagTailX0RatChunk000Sub001Block017Mid + surrogateDiagTailX0RatChunk000Sub001Block017Tail =
      surrogateDiagTailX0RatChunk000Sub001Block017 := by
  unfold surrogateDiagTailX0RatChunk000Sub001Block017Head surrogateDiagTailX0RatChunk000Sub001Block017Mid surrogateDiagTailX0RatChunk000Sub001Block017Tail surrogateDiagTailX0RatChunk000Sub001Block017
  ring

def SurrogateDiagonalTailChunk000Sub001Block017HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block017HeadSum X0 = surrogateDiagTailX0RatChunk000Sub001Block017Head

def SurrogateDiagonalTailChunk000Sub001Block017MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block017MidSum X0 = surrogateDiagTailX0RatChunk000Sub001Block017Mid

def SurrogateDiagonalTailChunk000Sub001Block017TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block017TailSum X0 = surrogateDiagTailX0RatChunk000Sub001Block017Tail

theorem surrogateDiagonalTailChunk000Sub001Block017_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk000Sub001Block017HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk000Sub001Block017MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk000Sub001Block017TailCertificateAt X0) :
    surrogateDiagonalTailChunk000Sub001Block017Sum X0 = surrogateDiagTailX0RatChunk000Sub001Block017 := by
  unfold SurrogateDiagonalTailChunk000Sub001Block017HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk000Sub001Block017MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk000Sub001Block017TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk000Sub001Block017Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk000Sub001Block017_eq_head_add_mid_add_tail

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

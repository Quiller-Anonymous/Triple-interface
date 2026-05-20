import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0TailPilot25

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

open scoped BigOperators

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

/- Generated direct-term certificate blocks for tail chunk 000, subchunk 000, blocks [108,109). -/

/- Block 108 covers tail-support indices [2700,2725) and q from 4494 to 4531. -/

def TailChunk000Sub000Block108Part000SupportExplicit : Finset ℕ :=
  ([4494] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block108Part000 : ℚ :=
  (12188150975 : ℚ) / 204562171773504

def SurrogateDiagonalTailChunk000Sub000Block108Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4494
    = surrogateDiagTailX0RatChunk000Sub000Block108Part000

theorem surrogateDiagonalTailChunk000Sub000Block108Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block108Part000CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block108Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block108Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block108Part000CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block108Part000SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block108Part000] using hcert

def TailChunk000Sub000Block108Part001SupportExplicit : Finset ℕ :=
  ([4495] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block108Part001 : ℚ :=
  (38062874131 : ℚ) / 12748055917363200

def SurrogateDiagonalTailChunk000Sub000Block108Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4495
    = surrogateDiagTailX0RatChunk000Sub000Block108Part001

theorem surrogateDiagonalTailChunk000Sub000Block108Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block108Part001CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block108Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block108Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block108Part001CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block108Part001SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block108Part001] using hcert

def TailChunk000Sub000Block108Part002SupportExplicit : Finset ℕ :=
  ([4497] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block108Part002 : ℚ :=
  (1718625 : ℚ) / 411065628736

def SurrogateDiagonalTailChunk000Sub000Block108Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4497
    = surrogateDiagTailX0RatChunk000Sub000Block108Part002

theorem surrogateDiagonalTailChunk000Sub000Block108Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block108Part002CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block108Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block108Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block108Part002CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block108Part002SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block108Part002] using hcert

def TailChunk000Sub000Block108Part003SupportExplicit : Finset ℕ :=
  ([4498] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block108Part003 : ℚ :=
  (293141313575 : ℚ) / 22690059516002304

def SurrogateDiagonalTailChunk000Sub000Block108Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4498
    = surrogateDiagTailX0RatChunk000Sub000Block108Part003

theorem surrogateDiagonalTailChunk000Sub000Block108Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block108Part003CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block108Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block108Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block108Part003CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block108Part003SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block108Part003] using hcert

def TailChunk000Sub000Block108Part004SupportExplicit : Finset ℕ :=
  ([4499] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block108Part004 : ℚ :=
  (9265555187 : ℚ) / 5543161069731840

def SurrogateDiagonalTailChunk000Sub000Block108Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4499
    = surrogateDiagTailX0RatChunk000Sub000Block108Part004

theorem surrogateDiagonalTailChunk000Sub000Block108Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block108Part004CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block108Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block108Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block108Part004CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block108Part004SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block108Part004] using hcert

def TailChunk000Sub000Block108Part005SupportExplicit : Finset ℕ :=
  ([4501] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block108Part005 : ℚ :=
  (277444823125 : ℚ) / 137629642370149152

def SurrogateDiagonalTailChunk000Sub000Block108Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4501
    = surrogateDiagTailX0RatChunk000Sub000Block108Part005

theorem surrogateDiagonalTailChunk000Sub000Block108Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block108Part005CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block108Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block108Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block108Part005CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block108Part005SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block108Part005] using hcert

def TailChunk000Sub000Block108Part006SupportExplicit : Finset ℕ :=
  ([4502] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block108Part006 : ℚ :=
  (25329937999 : ℚ) / 2563403203125000

def SurrogateDiagonalTailChunk000Sub000Block108Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4502
    = surrogateDiagTailX0RatChunk000Sub000Block108Part006

theorem surrogateDiagonalTailChunk000Sub000Block108Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block108Part006CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block108Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block108Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block108Part006CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block108Part006SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block108Part006] using hcert

def TailChunk000Sub000Block108Part007SupportExplicit : Finset ℕ :=
  ([4503] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block108Part007 : ℚ :=
  (796130127175 : ℚ) / 155458786286389248

def SurrogateDiagonalTailChunk000Sub000Block108Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4503
    = surrogateDiagTailX0RatChunk000Sub000Block108Part007

theorem surrogateDiagonalTailChunk000Sub000Block108Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block108Part007CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block108Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block108Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block108Part007CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block108Part007SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block108Part007] using hcert

def TailChunk000Sub000Block108Part008SupportExplicit : Finset ℕ :=
  ([4505] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block108Part008 : ℚ :=
  (272541606375 : ℚ) / 51122122772185088

def SurrogateDiagonalTailChunk000Sub000Block108Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4505
    = surrogateDiagTailX0RatChunk000Sub000Block108Part008

theorem surrogateDiagonalTailChunk000Sub000Block108Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block108Part008CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block108Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block108Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block108Part008CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block108Part008SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block108Part008] using hcert

def TailChunk000Sub000Block108Part009SupportExplicit : Finset ℕ :=
  ([4506] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block108Part009 : ℚ :=
  (22528341991 : ℚ) / 506351250000000

def SurrogateDiagonalTailChunk000Sub000Block108Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4506
    = surrogateDiagTailX0RatChunk000Sub000Block108Part009

theorem surrogateDiagonalTailChunk000Sub000Block108Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block108Part009CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block108Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block108Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block108Part009CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block108Part009SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block108Part009] using hcert

def TailChunk000Sub000Block108Part010SupportExplicit : Finset ℕ :=
  ([4507] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block108Part010 : ℚ :=
  (2538623298775 : ℚ) / 1030840821662184648

def SurrogateDiagonalTailChunk000Sub000Block108Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4507
    = surrogateDiagTailX0RatChunk000Sub000Block108Part010

theorem surrogateDiagonalTailChunk000Sub000Block108Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block108Part010CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block108Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block108Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block108Part010CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block108Part010SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block108Part010] using hcert

def TailChunk000Sub000Block108Part011SupportExplicit : Finset ℕ :=
  ([4510] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block108Part011 : ℚ :=
  (3731360303 : ℚ) / 131098214400000

def SurrogateDiagonalTailChunk000Sub000Block108Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4510
    = surrogateDiagTailX0RatChunk000Sub000Block108Part011

theorem surrogateDiagonalTailChunk000Sub000Block108Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block108Part011CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block108Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block108Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block108Part011CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block108Part011SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block108Part011] using hcert

def TailChunk000Sub000Block108Part012SupportExplicit : Finset ℕ :=
  ([4511] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block108Part012 : ℚ :=
  (1186170222775 : ℚ) / 743115360160401408

def SurrogateDiagonalTailChunk000Sub000Block108Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4511
    = surrogateDiagTailX0RatChunk000Sub000Block108Part012

theorem surrogateDiagonalTailChunk000Sub000Block108Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block108Part012CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block108Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block108Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block108Part012CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block108Part012SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block108Part012] using hcert

def TailChunk000Sub000Block108Part013SupportExplicit : Finset ℕ :=
  ([4513] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block108Part013 : ℚ :=
  (318237015625 : ℚ) / 259085573706350592

def SurrogateDiagonalTailChunk000Sub000Block108Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4513
    = surrogateDiagTailX0RatChunk000Sub000Block108Part013

theorem surrogateDiagonalTailChunk000Sub000Block108Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block108Part013CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block108Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block108Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block108Part013CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block108Part013SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block108Part013] using hcert

def TailChunk000Sub000Block108Part014SupportExplicit : Finset ℕ :=
  ([4514] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block108Part014 : ℚ :=
  (4899133403 : ℚ) / 435443538493440

def SurrogateDiagonalTailChunk000Sub000Block108Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4514
    = surrogateDiagTailX0RatChunk000Sub000Block108Part014

theorem surrogateDiagonalTailChunk000Sub000Block108Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block108Part014CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block108Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block108Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block108Part014CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block108Part014SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block108Part014] using hcert

def TailChunk000Sub000Block108Part015SupportExplicit : Finset ℕ :=
  ([4515] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block108Part015 : ℚ :=
  (591880201375 : ℚ) / 41303701172256768

def SurrogateDiagonalTailChunk000Sub000Block108Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4515
    = surrogateDiagTailX0RatChunk000Sub000Block108Part015

theorem surrogateDiagonalTailChunk000Sub000Block108Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block108Part015CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block108Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block108Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block108Part015CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block108Part015SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block108Part015] using hcert

def TailChunk000Sub000Block108Part016SupportExplicit : Finset ℕ :=
  ([4517] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block108Part016 : ℚ :=
  (318801390625 : ℚ) / 260005539330684192

def SurrogateDiagonalTailChunk000Sub000Block108Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4517
    = surrogateDiagTailX0RatChunk000Sub000Block108Part016

theorem surrogateDiagonalTailChunk000Sub000Block108Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block108Part016CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block108Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block108Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block108Part016CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block108Part016SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block108Part016] using hcert

def TailChunk000Sub000Block108Part017SupportExplicit : Finset ℕ :=
  ([4519] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block108Part017 : ℚ :=
  (319083765625 : ℚ) / 260466439796995122

def SurrogateDiagonalTailChunk000Sub000Block108Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4519
    = surrogateDiagTailX0RatChunk000Sub000Block108Part017

theorem surrogateDiagonalTailChunk000Sub000Block108Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block108Part017CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block108Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block108Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block108Part017CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block108Part017SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block108Part017] using hcert

def TailChunk000Sub000Block108Part018SupportExplicit : Finset ℕ :=
  ([4521] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block108Part018 : ℚ :=
  (178372913 : ℚ) / 27373634912256

def SurrogateDiagonalTailChunk000Sub000Block108Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4521
    = surrogateDiagTailX0RatChunk000Sub000Block108Part018

theorem surrogateDiagonalTailChunk000Sub000Block108Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block108Part018CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block108Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block108Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block108Part018CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block108Part018SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block108Part018] using hcert

def TailChunk000Sub000Block108Part019SupportExplicit : Finset ℕ :=
  ([4522] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block108Part019 : ℚ :=
  (168082971275 : ℚ) / 7431569723621376

def SurrogateDiagonalTailChunk000Sub000Block108Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4522
    = surrogateDiagTailX0RatChunk000Sub000Block108Part019

theorem surrogateDiagonalTailChunk000Sub000Block108Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block108Part019CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block108Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block108Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block108Part019CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block108Part019SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block108Part019] using hcert

def TailChunk000Sub000Block108Part020SupportExplicit : Finset ℕ :=
  ([4523] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block108Part020 : ℚ :=
  (319648890625 : ℚ) / 261390078748647282

def SurrogateDiagonalTailChunk000Sub000Block108Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4523
    = surrogateDiagTailX0RatChunk000Sub000Block108Part020

theorem surrogateDiagonalTailChunk000Sub000Block108Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block108Part020CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block108Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block108Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block108Part020CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block108Part020SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block108Part020] using hcert

def TailChunk000Sub000Block108Part021SupportExplicit : Finset ℕ :=
  ([4526] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block108Part021 : ℚ :=
  (7241478851 : ℚ) / 435443538493440

def SurrogateDiagonalTailChunk000Sub000Block108Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4526
    = surrogateDiagTailX0RatChunk000Sub000Block108Part021

theorem surrogateDiagonalTailChunk000Sub000Block108Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block108Part021CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block108Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block108Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block108Part021CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block108Part021SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block108Part021] using hcert

def TailChunk000Sub000Block108Part022SupportExplicit : Finset ℕ :=
  ([4529] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block108Part022 : ℚ :=
  (280906999375 : ℚ) / 141091854251664672

def SurrogateDiagonalTailChunk000Sub000Block108Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4529
    = surrogateDiagTailX0RatChunk000Sub000Block108Part022

theorem surrogateDiagonalTailChunk000Sub000Block108Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block108Part022CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block108Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block108Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block108Part022CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block108Part022SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block108Part022] using hcert

def TailChunk000Sub000Block108Part023SupportExplicit : Finset ℕ :=
  ([4530] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block108Part023 : ℚ :=
  (871229833 : ℚ) / 12962592000000

def SurrogateDiagonalTailChunk000Sub000Block108Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4530
    = surrogateDiagTailX0RatChunk000Sub000Block108Part023

theorem surrogateDiagonalTailChunk000Sub000Block108Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block108Part023CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block108Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block108Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block108Part023CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block108Part023SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block108Part023] using hcert

def TailChunk000Sub000Block108Part024SupportExplicit : Finset ℕ :=
  ([4531] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block108Part024 : ℚ :=
  (102231913725 : ℚ) / 72037829914699264

def SurrogateDiagonalTailChunk000Sub000Block108Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4531
    = surrogateDiagTailX0RatChunk000Sub000Block108Part024

theorem surrogateDiagonalTailChunk000Sub000Block108Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block108Part024CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block108Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block108Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block108Part024CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block108Part024SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block108Part024] using hcert

def surrogateDiagonalTailChunk000Sub000Block108HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block108Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block108Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block108Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block108Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block108Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block108Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block108Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block108Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block108Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block108Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block108Head : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block108Part000
    + surrogateDiagTailX0RatChunk000Sub000Block108Part001
    + surrogateDiagTailX0RatChunk000Sub000Block108Part002
    + surrogateDiagTailX0RatChunk000Sub000Block108Part003
    + surrogateDiagTailX0RatChunk000Sub000Block108Part004
    + surrogateDiagTailX0RatChunk000Sub000Block108Part005
    + surrogateDiagTailX0RatChunk000Sub000Block108Part006
    + surrogateDiagTailX0RatChunk000Sub000Block108Part007
    + surrogateDiagTailX0RatChunk000Sub000Block108Part008
    + surrogateDiagTailX0RatChunk000Sub000Block108Part009

def surrogateDiagonalTailChunk000Sub000Block108MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block108Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block108Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block108Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block108Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block108Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block108Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block108Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block108Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block108Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block108Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block108Mid : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block108Part010
    + surrogateDiagTailX0RatChunk000Sub000Block108Part011
    + surrogateDiagTailX0RatChunk000Sub000Block108Part012
    + surrogateDiagTailX0RatChunk000Sub000Block108Part013
    + surrogateDiagTailX0RatChunk000Sub000Block108Part014
    + surrogateDiagTailX0RatChunk000Sub000Block108Part015
    + surrogateDiagTailX0RatChunk000Sub000Block108Part016
    + surrogateDiagTailX0RatChunk000Sub000Block108Part017
    + surrogateDiagTailX0RatChunk000Sub000Block108Part018
    + surrogateDiagTailX0RatChunk000Sub000Block108Part019

def surrogateDiagonalTailChunk000Sub000Block108TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block108Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block108Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block108Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block108Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block108Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block108Tail : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block108Part020
    + surrogateDiagTailX0RatChunk000Sub000Block108Part021
    + surrogateDiagTailX0RatChunk000Sub000Block108Part022
    + surrogateDiagTailX0RatChunk000Sub000Block108Part023
    + surrogateDiagTailX0RatChunk000Sub000Block108Part024

def surrogateDiagonalTailChunk000Sub000Block108Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub000Block108HeadSum X0
    + surrogateDiagonalTailChunk000Sub000Block108MidSum X0
    + surrogateDiagonalTailChunk000Sub000Block108TailSum X0

def surrogateDiagTailX0RatChunk000Sub000Block108 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block108Part000
    + surrogateDiagTailX0RatChunk000Sub000Block108Part001
    + surrogateDiagTailX0RatChunk000Sub000Block108Part002
    + surrogateDiagTailX0RatChunk000Sub000Block108Part003
    + surrogateDiagTailX0RatChunk000Sub000Block108Part004
    + surrogateDiagTailX0RatChunk000Sub000Block108Part005
    + surrogateDiagTailX0RatChunk000Sub000Block108Part006
    + surrogateDiagTailX0RatChunk000Sub000Block108Part007
    + surrogateDiagTailX0RatChunk000Sub000Block108Part008
    + surrogateDiagTailX0RatChunk000Sub000Block108Part009
    + surrogateDiagTailX0RatChunk000Sub000Block108Part010
    + surrogateDiagTailX0RatChunk000Sub000Block108Part011
    + surrogateDiagTailX0RatChunk000Sub000Block108Part012
    + surrogateDiagTailX0RatChunk000Sub000Block108Part013
    + surrogateDiagTailX0RatChunk000Sub000Block108Part014
    + surrogateDiagTailX0RatChunk000Sub000Block108Part015
    + surrogateDiagTailX0RatChunk000Sub000Block108Part016
    + surrogateDiagTailX0RatChunk000Sub000Block108Part017
    + surrogateDiagTailX0RatChunk000Sub000Block108Part018
    + surrogateDiagTailX0RatChunk000Sub000Block108Part019
    + surrogateDiagTailX0RatChunk000Sub000Block108Part020
    + surrogateDiagTailX0RatChunk000Sub000Block108Part021
    + surrogateDiagTailX0RatChunk000Sub000Block108Part022
    + surrogateDiagTailX0RatChunk000Sub000Block108Part023
    + surrogateDiagTailX0RatChunk000Sub000Block108Part024

theorem surrogateDiagTailX0RatChunk000Sub000Block108_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk000Sub000Block108Head + surrogateDiagTailX0RatChunk000Sub000Block108Mid + surrogateDiagTailX0RatChunk000Sub000Block108Tail =
      surrogateDiagTailX0RatChunk000Sub000Block108 := by
  unfold surrogateDiagTailX0RatChunk000Sub000Block108Head surrogateDiagTailX0RatChunk000Sub000Block108Mid surrogateDiagTailX0RatChunk000Sub000Block108Tail surrogateDiagTailX0RatChunk000Sub000Block108
  ring

def SurrogateDiagonalTailChunk000Sub000Block108HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block108HeadSum X0 = surrogateDiagTailX0RatChunk000Sub000Block108Head

def SurrogateDiagonalTailChunk000Sub000Block108MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block108MidSum X0 = surrogateDiagTailX0RatChunk000Sub000Block108Mid

def SurrogateDiagonalTailChunk000Sub000Block108TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block108TailSum X0 = surrogateDiagTailX0RatChunk000Sub000Block108Tail

theorem surrogateDiagonalTailChunk000Sub000Block108_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk000Sub000Block108HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk000Sub000Block108MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk000Sub000Block108TailCertificateAt X0) :
    surrogateDiagonalTailChunk000Sub000Block108Sum X0 = surrogateDiagTailX0RatChunk000Sub000Block108 := by
  unfold SurrogateDiagonalTailChunk000Sub000Block108HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk000Sub000Block108MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk000Sub000Block108TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk000Sub000Block108Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk000Sub000Block108_eq_head_add_mid_add_tail

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

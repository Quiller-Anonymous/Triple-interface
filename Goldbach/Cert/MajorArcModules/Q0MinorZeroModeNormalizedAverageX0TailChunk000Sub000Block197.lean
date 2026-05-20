import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0TailPilot25

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

open scoped BigOperators

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

/- Generated direct-term certificate blocks for tail chunk 000, subchunk 000, blocks [197,198). -/

/-- Block 197 covers tail-support indices [4925,4950) and q from 8149 to 8189. -/

def TailChunk000Sub000Block197Part000SupportExplicit : Finset ℕ :=
  ([8149] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block197Part000 : ℚ :=
  (3865196917 : ℚ) / 377877558735667200

def SurrogateDiagonalTailChunk000Sub000Block197Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8149
    = surrogateDiagTailX0RatChunk000Sub000Block197Part000

theorem surrogateDiagonalTailChunk000Sub000Block197Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block197Part000CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block197Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block197Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block197Part000CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block197Part000SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block197Part000] using hcert

def TailChunk000Sub000Block197Part001SupportExplicit : Finset ℕ :=
  ([8151] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block197Part001 : ℚ :=
  (7822374797 : ℚ) / 11611827693158400

def SurrogateDiagonalTailChunk000Sub000Block197Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8151
    = surrogateDiagTailX0RatChunk000Sub000Block197Part001

theorem surrogateDiagonalTailChunk000Sub000Block197Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block197Part001CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block197Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block197Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block197Part001CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block197Part001SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block197Part001] using hcert

def TailChunk000Sub000Block197Part002SupportExplicit : Finset ℕ :=
  ([8153] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block197Part002 : ℚ :=
  (1811592197 : ℚ) / 190874115997761600

def SurrogateDiagonalTailChunk000Sub000Block197Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8153
    = surrogateDiagTailX0RatChunk000Sub000Block197Part002

theorem surrogateDiagonalTailChunk000Sub000Block197Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block197Part002CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block197Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block197Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block197Part002CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block197Part002SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block197Part002] using hcert

def TailChunk000Sub000Block197Part003SupportExplicit : Finset ℕ :=
  ([8155] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block197Part003 : ℚ :=
  (636443376025 : ℚ) / 2403387318560882688

def SurrogateDiagonalTailChunk000Sub000Block197Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8155
    = surrogateDiagTailX0RatChunk000Sub000Block197Part003

theorem surrogateDiagonalTailChunk000Sub000Block197Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block197Part003CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block197Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block197Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block197Part003CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block197Part003SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block197Part003] using hcert

def TailChunk000Sub000Block197Part004SupportExplicit : Finset ℕ :=
  ([8157] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block197Part004 : ℚ :=
  (461940332525 : ℚ) / 1091728519054922304

def SurrogateDiagonalTailChunk000Sub000Block197Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8157
    = surrogateDiagTailX0RatChunk000Sub000Block197Part004

theorem surrogateDiagonalTailChunk000Sub000Block197Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block197Part004CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block197Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block197Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block197Part004CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block197Part004SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block197Part004] using hcert

def TailChunk000Sub000Block197Part005SupportExplicit : Finset ℕ :=
  ([8158] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block197Part005 : ℚ :=
  (259972515625 : ℚ) / 172884378616140882

def SurrogateDiagonalTailChunk000Sub000Block197Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8158
    = surrogateDiagTailX0RatChunk000Sub000Block197Part005

theorem surrogateDiagonalTailChunk000Sub000Block197Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block197Part005CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block197Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block197Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block197Part005CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block197Part005SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block197Part005] using hcert

def TailChunk000Sub000Block197Part006SupportExplicit : Finset ℕ :=
  ([8159] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block197Part006 : ℚ :=
  (2938594789 : ℚ) / 393538817721139200

def SurrogateDiagonalTailChunk000Sub000Block197Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8159
    = surrogateDiagTailX0RatChunk000Sub000Block197Part006

theorem surrogateDiagonalTailChunk000Sub000Block197Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block197Part006CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block197Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block197Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block197Part006CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block197Part006SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block197Part006] using hcert

def TailChunk000Sub000Block197Part007SupportExplicit : Finset ℕ :=
  ([8161] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block197Part007 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub000Block197Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8161
    = surrogateDiagTailX0RatChunk000Sub000Block197Part007

theorem surrogateDiagonalTailChunk000Sub000Block197Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block197Part007CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block197Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block197Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block197Part007CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block197Part007SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block197Part007] using hcert

def TailChunk000Sub000Block197Part008SupportExplicit : Finset ℕ :=
  ([8162] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block197Part008 : ℚ :=
  (26265697 : ℚ) / 7290576543744

def SurrogateDiagonalTailChunk000Sub000Block197Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8162
    = surrogateDiagTailX0RatChunk000Sub000Block197Part008

theorem surrogateDiagonalTailChunk000Sub000Block197Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block197Part008CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block197Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block197Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block197Part008CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block197Part008SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block197Part008] using hcert

def TailChunk000Sub000Block197Part009SupportExplicit : Finset ℕ :=
  ([8165] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block197Part009 : ℚ :=
  (22277081341 : ℚ) / 144015653307187200

def SurrogateDiagonalTailChunk000Sub000Block197Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8165
    = surrogateDiagTailX0RatChunk000Sub000Block197Part009

theorem surrogateDiagonalTailChunk000Sub000Block197Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block197Part009CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block197Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block197Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block197Part009CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block197Part009SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block197Part009] using hcert

def TailChunk000Sub000Block197Part010SupportExplicit : Finset ℕ :=
  ([8166] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block197Part010 : ℚ :=
  (32398539937 : ℚ) / 5474726982451200

def SurrogateDiagonalTailChunk000Sub000Block197Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8166
    = surrogateDiagTailX0RatChunk000Sub000Block197Part010

theorem surrogateDiagonalTailChunk000Sub000Block197Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block197Part010CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block197Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block197Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block197Part010CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block197Part010SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block197Part010] using hcert

def TailChunk000Sub000Block197Part011SupportExplicit : Finset ℕ :=
  ([8167] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block197Part011 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub000Block197Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8167
    = surrogateDiagTailX0RatChunk000Sub000Block197Part011

theorem surrogateDiagonalTailChunk000Sub000Block197Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block197Part011CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block197Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block197Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block197Part011CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block197Part011SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block197Part011] using hcert

def TailChunk000Sub000Block197Part012SupportExplicit : Finset ℕ :=
  ([8169] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block197Part012 : ℚ :=
  (897457791475 : ℚ) / 1175110604448104448

def SurrogateDiagonalTailChunk000Sub000Block197Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8169
    = surrogateDiagTailX0RatChunk000Sub000Block197Part012

theorem surrogateDiagonalTailChunk000Sub000Block197Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block197Part012CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block197Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block197Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block197Part012CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block197Part012SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block197Part012] using hcert

def TailChunk000Sub000Block197Part013SupportExplicit : Finset ℕ :=
  ([8170] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block197Part013 : ℚ :=
  (26760911375 : ℚ) / 6534374599517184

def SurrogateDiagonalTailChunk000Sub000Block197Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8170
    = surrogateDiagTailX0RatChunk000Sub000Block197Part013

theorem surrogateDiagonalTailChunk000Sub000Block197Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block197Part013CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block197Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block197Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block197Part013CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block197Part013SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block197Part013] using hcert

def TailChunk000Sub000Block197Part014SupportExplicit : Finset ℕ :=
  ([8171] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block197Part014 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub000Block197Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8171
    = surrogateDiagTailX0RatChunk000Sub000Block197Part014

theorem surrogateDiagonalTailChunk000Sub000Block197Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block197Part014CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block197Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block197Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block197Part014CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block197Part014SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block197Part014] using hcert

def TailChunk000Sub000Block197Part015SupportExplicit : Finset ℕ :=
  ([8173] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block197Part015 : ℚ :=
  (464208261 : ℚ) / 14437206773315200

def SurrogateDiagonalTailChunk000Sub000Block197Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8173
    = surrogateDiagTailX0RatChunk000Sub000Block197Part015

theorem surrogateDiagonalTailChunk000Sub000Block197Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block197Part015CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block197Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block197Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block197Part015CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block197Part015SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block197Part015] using hcert

def TailChunk000Sub000Block197Part016SupportExplicit : Finset ℕ :=
  ([8174] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block197Part016 : ℚ :=
  (2264371213 : ℚ) / 1366454228198400

def SurrogateDiagonalTailChunk000Sub000Block197Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8174
    = surrogateDiagTailX0RatChunk000Sub000Block197Part016

theorem surrogateDiagonalTailChunk000Sub000Block197Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block197Part016CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block197Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block197Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block197Part016CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block197Part016SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block197Part016] using hcert

def TailChunk000Sub000Block197Part017SupportExplicit : Finset ℕ :=
  ([8177] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block197Part017 : ℚ :=
  (176202106325 : ℚ) / 2853722773870608384

def SurrogateDiagonalTailChunk000Sub000Block197Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8177
    = surrogateDiagTailX0RatChunk000Sub000Block197Part017

theorem surrogateDiagonalTailChunk000Sub000Block197Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block197Part017CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block197Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block197Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block197Part017CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block197Part017SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block197Part017] using hcert

def TailChunk000Sub000Block197Part018SupportExplicit : Finset ℕ :=
  ([8178] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block197Part018 : ℚ :=
  (11158770975 : ℚ) / 1595736587927552

def SurrogateDiagonalTailChunk000Sub000Block197Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8178
    = surrogateDiagTailX0RatChunk000Sub000Block197Part018

theorem surrogateDiagonalTailChunk000Sub000Block197Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block197Part018CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block197Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block197Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block197Part018CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block197Part018SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block197Part018] using hcert

def TailChunk000Sub000Block197Part019SupportExplicit : Finset ℕ :=
  ([8179] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block197Part019 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub000Block197Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8179
    = surrogateDiagTailX0RatChunk000Sub000Block197Part019

theorem surrogateDiagonalTailChunk000Sub000Block197Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block197Part019CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block197Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block197Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block197Part019CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block197Part019SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block197Part019] using hcert

def TailChunk000Sub000Block197Part020SupportExplicit : Finset ℕ :=
  ([8182] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block197Part020 : ℚ :=
  (418407025 : ℚ) / 279885295475922

def SurrogateDiagonalTailChunk000Sub000Block197Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8182
    = surrogateDiagTailX0RatChunk000Sub000Block197Part020

theorem surrogateDiagonalTailChunk000Sub000Block197Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block197Part020CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block197Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block197Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block197Part020CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block197Part020SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block197Part020] using hcert

def TailChunk000Sub000Block197Part021SupportExplicit : Finset ℕ :=
  ([8185] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block197Part021 : ℚ :=
  (251446232975 : ℚ) / 2292820340538753024

def SurrogateDiagonalTailChunk000Sub000Block197Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8185
    = surrogateDiagTailX0RatChunk000Sub000Block197Part021

theorem surrogateDiagonalTailChunk000Sub000Block197Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block197Part021CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block197Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block197Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block197Part021CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block197Part021SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block197Part021] using hcert

def TailChunk000Sub000Block197Part022SupportExplicit : Finset ℕ :=
  ([8186] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block197Part022 : ℚ :=
  (261760140625 : ℚ) / 175270718788890912

def SurrogateDiagonalTailChunk000Sub000Block197Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8186
    = surrogateDiagTailX0RatChunk000Sub000Block197Part022

theorem surrogateDiagonalTailChunk000Sub000Block197Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block197Part022CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block197Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block197Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block197Part022CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block197Part022SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block197Part022] using hcert

def TailChunk000Sub000Block197Part023SupportExplicit : Finset ℕ :=
  ([8187] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block197Part023 : ℚ :=
  (465343401275 : ℚ) / 1107884049628545024

def SurrogateDiagonalTailChunk000Sub000Block197Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8187
    = surrogateDiagTailX0RatChunk000Sub000Block197Part023

theorem surrogateDiagonalTailChunk000Sub000Block197Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block197Part023CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block197Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block197Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block197Part023CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block197Part023SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block197Part023] using hcert

def TailChunk000Sub000Block197Part024SupportExplicit : Finset ℕ :=
  ([8189] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block197Part024 : ℚ :=
  (353295989 : ℚ) / 23930922145783680

def SurrogateDiagonalTailChunk000Sub000Block197Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8189
    = surrogateDiagTailX0RatChunk000Sub000Block197Part024

theorem surrogateDiagonalTailChunk000Sub000Block197Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block197Part024CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block197Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block197Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block197Part024CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block197Part024SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block197Part024] using hcert

def surrogateDiagonalTailChunk000Sub000Block197HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block197Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block197Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block197Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block197Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block197Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block197Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block197Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block197Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block197Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block197Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block197Head : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block197Part000
    + surrogateDiagTailX0RatChunk000Sub000Block197Part001
    + surrogateDiagTailX0RatChunk000Sub000Block197Part002
    + surrogateDiagTailX0RatChunk000Sub000Block197Part003
    + surrogateDiagTailX0RatChunk000Sub000Block197Part004
    + surrogateDiagTailX0RatChunk000Sub000Block197Part005
    + surrogateDiagTailX0RatChunk000Sub000Block197Part006
    + surrogateDiagTailX0RatChunk000Sub000Block197Part007
    + surrogateDiagTailX0RatChunk000Sub000Block197Part008
    + surrogateDiagTailX0RatChunk000Sub000Block197Part009

def surrogateDiagonalTailChunk000Sub000Block197MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block197Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block197Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block197Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block197Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block197Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block197Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block197Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block197Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block197Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block197Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block197Mid : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block197Part010
    + surrogateDiagTailX0RatChunk000Sub000Block197Part011
    + surrogateDiagTailX0RatChunk000Sub000Block197Part012
    + surrogateDiagTailX0RatChunk000Sub000Block197Part013
    + surrogateDiagTailX0RatChunk000Sub000Block197Part014
    + surrogateDiagTailX0RatChunk000Sub000Block197Part015
    + surrogateDiagTailX0RatChunk000Sub000Block197Part016
    + surrogateDiagTailX0RatChunk000Sub000Block197Part017
    + surrogateDiagTailX0RatChunk000Sub000Block197Part018
    + surrogateDiagTailX0RatChunk000Sub000Block197Part019

def surrogateDiagonalTailChunk000Sub000Block197TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block197Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block197Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block197Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block197Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block197Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block197Tail : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block197Part020
    + surrogateDiagTailX0RatChunk000Sub000Block197Part021
    + surrogateDiagTailX0RatChunk000Sub000Block197Part022
    + surrogateDiagTailX0RatChunk000Sub000Block197Part023
    + surrogateDiagTailX0RatChunk000Sub000Block197Part024

def surrogateDiagonalTailChunk000Sub000Block197Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub000Block197HeadSum X0
    + surrogateDiagonalTailChunk000Sub000Block197MidSum X0
    + surrogateDiagonalTailChunk000Sub000Block197TailSum X0

def surrogateDiagTailX0RatChunk000Sub000Block197 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block197Part000
    + surrogateDiagTailX0RatChunk000Sub000Block197Part001
    + surrogateDiagTailX0RatChunk000Sub000Block197Part002
    + surrogateDiagTailX0RatChunk000Sub000Block197Part003
    + surrogateDiagTailX0RatChunk000Sub000Block197Part004
    + surrogateDiagTailX0RatChunk000Sub000Block197Part005
    + surrogateDiagTailX0RatChunk000Sub000Block197Part006
    + surrogateDiagTailX0RatChunk000Sub000Block197Part007
    + surrogateDiagTailX0RatChunk000Sub000Block197Part008
    + surrogateDiagTailX0RatChunk000Sub000Block197Part009
    + surrogateDiagTailX0RatChunk000Sub000Block197Part010
    + surrogateDiagTailX0RatChunk000Sub000Block197Part011
    + surrogateDiagTailX0RatChunk000Sub000Block197Part012
    + surrogateDiagTailX0RatChunk000Sub000Block197Part013
    + surrogateDiagTailX0RatChunk000Sub000Block197Part014
    + surrogateDiagTailX0RatChunk000Sub000Block197Part015
    + surrogateDiagTailX0RatChunk000Sub000Block197Part016
    + surrogateDiagTailX0RatChunk000Sub000Block197Part017
    + surrogateDiagTailX0RatChunk000Sub000Block197Part018
    + surrogateDiagTailX0RatChunk000Sub000Block197Part019
    + surrogateDiagTailX0RatChunk000Sub000Block197Part020
    + surrogateDiagTailX0RatChunk000Sub000Block197Part021
    + surrogateDiagTailX0RatChunk000Sub000Block197Part022
    + surrogateDiagTailX0RatChunk000Sub000Block197Part023
    + surrogateDiagTailX0RatChunk000Sub000Block197Part024

theorem surrogateDiagTailX0RatChunk000Sub000Block197_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk000Sub000Block197Head + surrogateDiagTailX0RatChunk000Sub000Block197Mid + surrogateDiagTailX0RatChunk000Sub000Block197Tail =
      surrogateDiagTailX0RatChunk000Sub000Block197 := by
  unfold surrogateDiagTailX0RatChunk000Sub000Block197Head surrogateDiagTailX0RatChunk000Sub000Block197Mid surrogateDiagTailX0RatChunk000Sub000Block197Tail surrogateDiagTailX0RatChunk000Sub000Block197
  ring

def SurrogateDiagonalTailChunk000Sub000Block197HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block197HeadSum X0 = surrogateDiagTailX0RatChunk000Sub000Block197Head

def SurrogateDiagonalTailChunk000Sub000Block197MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block197MidSum X0 = surrogateDiagTailX0RatChunk000Sub000Block197Mid

def SurrogateDiagonalTailChunk000Sub000Block197TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block197TailSum X0 = surrogateDiagTailX0RatChunk000Sub000Block197Tail

theorem surrogateDiagonalTailChunk000Sub000Block197_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk000Sub000Block197HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk000Sub000Block197MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk000Sub000Block197TailCertificateAt X0) :
    surrogateDiagonalTailChunk000Sub000Block197Sum X0 = surrogateDiagTailX0RatChunk000Sub000Block197 := by
  unfold SurrogateDiagonalTailChunk000Sub000Block197HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk000Sub000Block197MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk000Sub000Block197TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk000Sub000Block197Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk000Sub000Block197_eq_head_add_mid_add_tail

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

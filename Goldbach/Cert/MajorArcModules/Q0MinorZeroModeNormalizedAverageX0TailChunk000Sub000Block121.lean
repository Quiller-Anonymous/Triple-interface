import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0TailPilot25

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

open scoped BigOperators

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

/- Generated direct-term certificate blocks for tail chunk 000, subchunk 000, blocks [121,122). -/

/- Block 121 covers tail-support indices [3025,3050) and q from 5021 to 5069. -/

def TailChunk000Sub000Block121Part000SupportExplicit : Finset ℕ :=
  ([5021] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block121Part000 : ℚ :=
  (630261025 : ℚ) / 635187172192032

def SurrogateDiagonalTailChunk000Sub000Block121Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5021
    = surrogateDiagTailX0RatChunk000Sub000Block121Part000

theorem surrogateDiagonalTailChunk000Sub000Block121Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block121Part000CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block121Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block121Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block121Part000CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block121Part000SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block121Part000] using hcert

def TailChunk000Sub000Block121Part001SupportExplicit : Finset ℕ :=
  ([5023] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block121Part001 : ℚ :=
  (394227015625 : ℚ) / 397625017348059282

def SurrogateDiagonalTailChunk000Sub000Block121Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5023
    = surrogateDiagTailX0RatChunk000Sub000Block121Part001

theorem surrogateDiagonalTailChunk000Sub000Block121Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block121Part001CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block121Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block121Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block121Part001CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block121Part001SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block121Part001] using hcert

def TailChunk000Sub000Block121Part002SupportExplicit : Finset ℕ :=
  ([5026] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block121Part002 : ℚ :=
  (74985014825 : ℚ) / 5914546595344512

def SurrogateDiagonalTailChunk000Sub000Block121Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5026
    = surrogateDiagTailX0RatChunk000Sub000Block121Part002

theorem surrogateDiagonalTailChunk000Sub000Block121Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block121Part002CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block121Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block121Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block121Part002CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block121Part002SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block121Part002] using hcert

def TailChunk000Sub000Block121Part003SupportExplicit : Finset ℕ :=
  ([5027] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block121Part003 : ℚ :=
  (4713709 : ℚ) / 3556416741120

def SurrogateDiagonalTailChunk000Sub000Block121Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5027
    = surrogateDiagTailX0RatChunk000Sub000Block121Part003

theorem surrogateDiagonalTailChunk000Sub000Block121Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block121Part003CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block121Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block121Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block121Part003CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block121Part003SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block121Part003] using hcert

def TailChunk000Sub000Block121Part004SupportExplicit : Finset ℕ :=
  ([5029] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block121Part004 : ℚ :=
  (766380149375 : ℚ) / 706726947052705344

def SurrogateDiagonalTailChunk000Sub000Block121Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5029
    = surrogateDiagTailX0RatChunk000Sub000Block121Part004

theorem surrogateDiagonalTailChunk000Sub000Block121Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block121Part004CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block121Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block121Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block121Part004CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block121Part004SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block121Part004] using hcert

def TailChunk000Sub000Block121Part005SupportExplicit : Finset ℕ :=
  ([5030] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block121Part005 : ℚ :=
  (307814150825 : ℚ) / 20325989510145024

def SurrogateDiagonalTailChunk000Sub000Block121Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5030
    = surrogateDiagTailX0RatChunk000Sub000Block121Part005

theorem surrogateDiagonalTailChunk000Sub000Block121Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block121Part005CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block121Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block121Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block121Part005CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block121Part005SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block121Part005] using hcert

def TailChunk000Sub000Block121Part006SupportExplicit : Finset ℕ :=
  ([5033] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block121Part006 : ℚ :=
  (75299629825 : ℚ) / 47847266563484736

def SurrogateDiagonalTailChunk000Sub000Block121Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5033
    = surrogateDiagTailX0RatChunk000Sub000Block121Part006

theorem surrogateDiagonalTailChunk000Sub000Block121Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block121Part006CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block121Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block121Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block121Part006CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block121Part006SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block121Part006] using hcert

def TailChunk000Sub000Block121Part007SupportExplicit : Finset ℕ :=
  ([5034] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block121Part007 : ℚ :=
  (105461475 : ℚ) / 3945173084288

def SurrogateDiagonalTailChunk000Sub000Block121Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5034
    = surrogateDiagTailX0RatChunk000Sub000Block121Part007

theorem surrogateDiagonalTailChunk000Sub000Block121Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block121Part007CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block121Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block121Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block121Part007CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block121Part007SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block121Part007] using hcert

def TailChunk000Sub000Block121Part008SupportExplicit : Finset ℕ :=
  ([5035] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block121Part008 : ℚ :=
  (147259322975 : ℚ) / 61415816804499456

def SurrogateDiagonalTailChunk000Sub000Block121Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5035
    = surrogateDiagTailX0RatChunk000Sub000Block121Part008

theorem surrogateDiagonalTailChunk000Sub000Block121Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block121Part008CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block121Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block121Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block121Part008CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block121Part008SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block121Part008] using hcert

def TailChunk000Sub000Block121Part009SupportExplicit : Finset ℕ :=
  ([5037] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block121Part009 : ℚ :=
  (498036815225 : ℚ) / 125932421670764544

def SurrogateDiagonalTailChunk000Sub000Block121Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5037
    = surrogateDiagTailX0RatChunk000Sub000Block121Part009

theorem surrogateDiagonalTailChunk000Sub000Block121Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block121Part009CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block121Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block121Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block121Part009CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block121Part009SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block121Part009] using hcert

def TailChunk000Sub000Block121Part010SupportExplicit : Finset ℕ :=
  ([5038] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block121Part010 : ℚ :=
  (5744301629 : ℚ) / 540575344650240

def SurrogateDiagonalTailChunk000Sub000Block121Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5038
    = surrogateDiagTailX0RatChunk000Sub000Block121Part010

theorem surrogateDiagonalTailChunk000Sub000Block121Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block121Part010CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block121Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block121Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block121Part010CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block121Part010SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block121Part010] using hcert

def TailChunk000Sub000Block121Part011SupportExplicit : Finset ℕ :=
  ([5039] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block121Part011 : ℚ :=
  (396742515625 : ℚ) / 402716589415650642

def SurrogateDiagonalTailChunk000Sub000Block121Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5039
    = surrogateDiagTailX0RatChunk000Sub000Block121Part011

theorem surrogateDiagonalTailChunk000Sub000Block121Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block121Part011CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block121Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block121Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block121Part011CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block121Part011SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block121Part011] using hcert

def TailChunk000Sub000Block121Part012SupportExplicit : Finset ℕ :=
  ([5042] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block121Part012 : ℚ :=
  (31770849559 : ℚ) / 4033564567603200

def SurrogateDiagonalTailChunk000Sub000Block121Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5042
    = surrogateDiagTailX0RatChunk000Sub000Block121Part012

theorem surrogateDiagonalTailChunk000Sub000Block121Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block121Part012CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block121Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block121Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block121Part012CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block121Part012SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block121Part012] using hcert

def TailChunk000Sub000Block121Part013SupportExplicit : Finset ℕ :=
  ([5045] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block121Part013 : ℚ :=
  (635792007875 : ℚ) / 330429609378054144

def SurrogateDiagonalTailChunk000Sub000Block121Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5045
    = surrogateDiagTailX0RatChunk000Sub000Block121Part013

theorem surrogateDiagonalTailChunk000Sub000Block121Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block121Part013CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block121Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block121Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block121Part013CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block121Part013SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block121Part013] using hcert

def TailChunk000Sub000Block121Part014SupportExplicit : Finset ℕ :=
  ([5051] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block121Part014 : ℚ :=
  (25512601 : ℚ) / 26020303270050

def SurrogateDiagonalTailChunk000Sub000Block121Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5051
    = surrogateDiagTailX0RatChunk000Sub000Block121Part014

theorem surrogateDiagonalTailChunk000Sub000Block121Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block121Part014CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block121Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block121Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block121Part014CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block121Part014SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block121Part014] using hcert

def TailChunk000Sub000Block121Part015SupportExplicit : Finset ℕ :=
  ([5053] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block121Part015 : ℚ :=
  (12280320563 : ℚ) / 11159941625216640

def SurrogateDiagonalTailChunk000Sub000Block121Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5053
    = surrogateDiagTailX0RatChunk000Sub000Block121Part015

theorem surrogateDiagonalTailChunk000Sub000Block121Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block121Part015CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block121Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block121Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block121Part015CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block121Part015SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block121Part015] using hcert

def TailChunk000Sub000Block121Part016SupportExplicit : Finset ℕ :=
  ([5055] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block121Part016 : ℚ :=
  (121340352325 : ℚ) / 18648584656257024

def SurrogateDiagonalTailChunk000Sub000Block121Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5055
    = surrogateDiagTailX0RatChunk000Sub000Block121Part016

theorem surrogateDiagonalTailChunk000Sub000Block121Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block121Part016CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block121Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block121Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block121Part016CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block121Part016SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block121Part016] using hcert

def TailChunk000Sub000Block121Part017SupportExplicit : Finset ℕ :=
  ([5057] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block121Part017 : ℚ :=
  (735921029675 : ℚ) / 587555302224052224

def SurrogateDiagonalTailChunk000Sub000Block121Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5057
    = surrogateDiagTailX0RatChunk000Sub000Block121Part017

theorem surrogateDiagonalTailChunk000Sub000Block121Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block121Part017CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block121Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block121Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block121Part017CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block121Part017SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block121Part017] using hcert

def TailChunk000Sub000Block121Part018SupportExplicit : Finset ℕ :=
  ([5059] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block121Part018 : ℚ :=
  (399898140625 : ℚ) / 409149634537004562

def SurrogateDiagonalTailChunk000Sub000Block121Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5059
    = surrogateDiagTailX0RatChunk000Sub000Block121Part018

theorem surrogateDiagonalTailChunk000Sub000Block121Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block121Part018CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block121Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block121Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block121Part018CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block121Part018SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block121Part018] using hcert

def TailChunk000Sub000Block121Part019SupportExplicit : Finset ℕ :=
  ([5061] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block121Part019 : ℚ :=
  (485831 : ℚ) / 91729428480

def SurrogateDiagonalTailChunk000Sub000Block121Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5061
    = surrogateDiagTailX0RatChunk000Sub000Block121Part019

theorem surrogateDiagonalTailChunk000Sub000Block121Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block121Part019CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block121Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block121Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block121Part019CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block121Part019SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block121Part019] using hcert

def TailChunk000Sub000Block121Part020SupportExplicit : Finset ℕ :=
  ([5062] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block121Part020 : ℚ :=
  (32023399039 : ℚ) / 4097971511416200

def SurrogateDiagonalTailChunk000Sub000Block121Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5062
    = surrogateDiagTailX0RatChunk000Sub000Block121Part020

theorem surrogateDiagonalTailChunk000Sub000Block121Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block121Part020CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block121Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block121Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block121Part020CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block121Part020SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block121Part020] using hcert

def TailChunk000Sub000Block121Part021SupportExplicit : Finset ℕ :=
  ([5063] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block121Part021 : ℚ :=
  (31130693213 : ℚ) / 29303349546009600

def SurrogateDiagonalTailChunk000Sub000Block121Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5063
    = surrogateDiagTailX0RatChunk000Sub000Block121Part021

theorem surrogateDiagonalTailChunk000Sub000Block121Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block121Part021CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block121Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block121Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block121Part021CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block121Part021SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block121Part021] using hcert

def TailChunk000Sub000Block121Part022SupportExplicit : Finset ℕ :=
  ([5065] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block121Part022 : ℚ :=
  (640843017875 : ℚ) / 335705826215215104

def SurrogateDiagonalTailChunk000Sub000Block121Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5065
    = surrogateDiagTailX0RatChunk000Sub000Block121Part022

theorem surrogateDiagonalTailChunk000Sub000Block121Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block121Part022CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block121Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block121Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block121Part022CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block121Part022SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block121Part022] using hcert

def TailChunk000Sub000Block121Part023SupportExplicit : Finset ℕ :=
  ([5066] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block121Part023 : ℚ :=
  (249950042475 : ℚ) / 26207910463799296

def SurrogateDiagonalTailChunk000Sub000Block121Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5066
    = surrogateDiagTailX0RatChunk000Sub000Block121Part023

theorem surrogateDiagonalTailChunk000Sub000Block121Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block121Part023CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block121Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block121Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block121Part023CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block121Part023SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block121Part023] using hcert

def TailChunk000Sub000Block121Part024SupportExplicit : Finset ℕ :=
  ([5069] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block121Part024 : ℚ :=
  (19151334125 : ℚ) / 17738115423141888

def SurrogateDiagonalTailChunk000Sub000Block121Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5069
    = surrogateDiagTailX0RatChunk000Sub000Block121Part024

theorem surrogateDiagonalTailChunk000Sub000Block121Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block121Part024CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block121Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block121Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block121Part024CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block121Part024SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block121Part024] using hcert

def surrogateDiagonalTailChunk000Sub000Block121HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block121Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block121Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block121Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block121Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block121Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block121Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block121Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block121Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block121Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block121Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block121Head : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block121Part000
    + surrogateDiagTailX0RatChunk000Sub000Block121Part001
    + surrogateDiagTailX0RatChunk000Sub000Block121Part002
    + surrogateDiagTailX0RatChunk000Sub000Block121Part003
    + surrogateDiagTailX0RatChunk000Sub000Block121Part004
    + surrogateDiagTailX0RatChunk000Sub000Block121Part005
    + surrogateDiagTailX0RatChunk000Sub000Block121Part006
    + surrogateDiagTailX0RatChunk000Sub000Block121Part007
    + surrogateDiagTailX0RatChunk000Sub000Block121Part008
    + surrogateDiagTailX0RatChunk000Sub000Block121Part009

def surrogateDiagonalTailChunk000Sub000Block121MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block121Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block121Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block121Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block121Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block121Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block121Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block121Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block121Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block121Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block121Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block121Mid : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block121Part010
    + surrogateDiagTailX0RatChunk000Sub000Block121Part011
    + surrogateDiagTailX0RatChunk000Sub000Block121Part012
    + surrogateDiagTailX0RatChunk000Sub000Block121Part013
    + surrogateDiagTailX0RatChunk000Sub000Block121Part014
    + surrogateDiagTailX0RatChunk000Sub000Block121Part015
    + surrogateDiagTailX0RatChunk000Sub000Block121Part016
    + surrogateDiagTailX0RatChunk000Sub000Block121Part017
    + surrogateDiagTailX0RatChunk000Sub000Block121Part018
    + surrogateDiagTailX0RatChunk000Sub000Block121Part019

def surrogateDiagonalTailChunk000Sub000Block121TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block121Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block121Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block121Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block121Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block121Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block121Tail : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block121Part020
    + surrogateDiagTailX0RatChunk000Sub000Block121Part021
    + surrogateDiagTailX0RatChunk000Sub000Block121Part022
    + surrogateDiagTailX0RatChunk000Sub000Block121Part023
    + surrogateDiagTailX0RatChunk000Sub000Block121Part024

def surrogateDiagonalTailChunk000Sub000Block121Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub000Block121HeadSum X0
    + surrogateDiagonalTailChunk000Sub000Block121MidSum X0
    + surrogateDiagonalTailChunk000Sub000Block121TailSum X0

def surrogateDiagTailX0RatChunk000Sub000Block121 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block121Part000
    + surrogateDiagTailX0RatChunk000Sub000Block121Part001
    + surrogateDiagTailX0RatChunk000Sub000Block121Part002
    + surrogateDiagTailX0RatChunk000Sub000Block121Part003
    + surrogateDiagTailX0RatChunk000Sub000Block121Part004
    + surrogateDiagTailX0RatChunk000Sub000Block121Part005
    + surrogateDiagTailX0RatChunk000Sub000Block121Part006
    + surrogateDiagTailX0RatChunk000Sub000Block121Part007
    + surrogateDiagTailX0RatChunk000Sub000Block121Part008
    + surrogateDiagTailX0RatChunk000Sub000Block121Part009
    + surrogateDiagTailX0RatChunk000Sub000Block121Part010
    + surrogateDiagTailX0RatChunk000Sub000Block121Part011
    + surrogateDiagTailX0RatChunk000Sub000Block121Part012
    + surrogateDiagTailX0RatChunk000Sub000Block121Part013
    + surrogateDiagTailX0RatChunk000Sub000Block121Part014
    + surrogateDiagTailX0RatChunk000Sub000Block121Part015
    + surrogateDiagTailX0RatChunk000Sub000Block121Part016
    + surrogateDiagTailX0RatChunk000Sub000Block121Part017
    + surrogateDiagTailX0RatChunk000Sub000Block121Part018
    + surrogateDiagTailX0RatChunk000Sub000Block121Part019
    + surrogateDiagTailX0RatChunk000Sub000Block121Part020
    + surrogateDiagTailX0RatChunk000Sub000Block121Part021
    + surrogateDiagTailX0RatChunk000Sub000Block121Part022
    + surrogateDiagTailX0RatChunk000Sub000Block121Part023
    + surrogateDiagTailX0RatChunk000Sub000Block121Part024

theorem surrogateDiagTailX0RatChunk000Sub000Block121_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk000Sub000Block121Head + surrogateDiagTailX0RatChunk000Sub000Block121Mid + surrogateDiagTailX0RatChunk000Sub000Block121Tail =
      surrogateDiagTailX0RatChunk000Sub000Block121 := by
  unfold surrogateDiagTailX0RatChunk000Sub000Block121Head surrogateDiagTailX0RatChunk000Sub000Block121Mid surrogateDiagTailX0RatChunk000Sub000Block121Tail surrogateDiagTailX0RatChunk000Sub000Block121
  ring

def SurrogateDiagonalTailChunk000Sub000Block121HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block121HeadSum X0 = surrogateDiagTailX0RatChunk000Sub000Block121Head

def SurrogateDiagonalTailChunk000Sub000Block121MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block121MidSum X0 = surrogateDiagTailX0RatChunk000Sub000Block121Mid

def SurrogateDiagonalTailChunk000Sub000Block121TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block121TailSum X0 = surrogateDiagTailX0RatChunk000Sub000Block121Tail

theorem surrogateDiagonalTailChunk000Sub000Block121_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk000Sub000Block121HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk000Sub000Block121MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk000Sub000Block121TailCertificateAt X0) :
    surrogateDiagonalTailChunk000Sub000Block121Sum X0 = surrogateDiagTailX0RatChunk000Sub000Block121 := by
  unfold SurrogateDiagonalTailChunk000Sub000Block121HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk000Sub000Block121MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk000Sub000Block121TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk000Sub000Block121Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk000Sub000Block121_eq_head_add_mid_add_tail

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

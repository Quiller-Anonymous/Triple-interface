import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0TailPilot25

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

open scoped BigOperators

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

/- Generated direct-term certificate blocks for tail chunk 000, subchunk 000, blocks [29,30). -/

/- Block 029 covers tail-support indices [725,750) and q from 1243 to 1283. -/

def TailChunk000Sub000Block029Part000SupportExplicit : Finset ℕ :=
  ([1243] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block029Part000 : ℚ :=
  (465218547 : ℚ) / 5246113546240

def SurrogateDiagonalTailChunk000Sub000Block029Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1243
    = surrogateDiagTailX0RatChunk000Sub000Block029Part000

theorem surrogateDiagonalTailChunk000Sub000Block029Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block029Part000CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block029Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block029Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block029Part000CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block029Part000SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block029Part000] using hcert

def TailChunk000Sub000Block029Part001SupportExplicit : Finset ℕ :=
  ([1245] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block029Part001 : ℚ :=
  (204230961775 : ℚ) / 463065276776448

def SurrogateDiagonalTailChunk000Sub000Block029Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1245
    = surrogateDiagTailX0RatChunk000Sub000Block029Part001

theorem surrogateDiagonalTailChunk000Sub000Block029Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block029Part001CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block029Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block029Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block029Part001CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block029Part001SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block029Part001] using hcert

def TailChunk000Sub000Block029Part002SupportExplicit : Finset ℕ :=
  ([1246] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block029Part002 : ℚ :=
  (164994274825 : ℚ) / 194340156899328

def SurrogateDiagonalTailChunk000Sub000Block029Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1246
    = surrogateDiagTailX0RatChunk000Sub000Block029Part002

theorem surrogateDiagonalTailChunk000Sub000Block029Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block029Part002CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block029Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block029Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block029Part002CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block029Part002SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block029Part002] using hcert

def TailChunk000Sub000Block029Part003SupportExplicit : Finset ℕ :=
  ([1247] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block029Part003 : ℚ :=
  (6792635825 : ℚ) / 88565052828672

def SurrogateDiagonalTailChunk000Sub000Block029Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1247
    = surrogateDiagTailX0RatChunk000Sub000Block029Part003

theorem surrogateDiagonalTailChunk000Sub000Block029Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block029Part003CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block029Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block029Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block029Part003CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block029Part003SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block029Part003] using hcert

def TailChunk000Sub000Block029Part004SupportExplicit : Finset ℕ :=
  ([1249] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block029Part004 : ℚ :=
  (194883124925 : ℚ) / 3032879842197504

def SurrogateDiagonalTailChunk000Sub000Block029Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1249
    = surrogateDiagTailX0RatChunk000Sub000Block029Part004

theorem surrogateDiagonalTailChunk000Sub000Block029Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block029Part004CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block029Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block029Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block029Part004CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block029Part004SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block029Part004] using hcert

def TailChunk000Sub000Block029Part005SupportExplicit : Finset ℕ :=
  ([1253] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block029Part005 : ℚ :=
  (37179205175 : ℚ) / 361467587221632

def SurrogateDiagonalTailChunk000Sub000Block029Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1253
    = surrogateDiagTailX0RatChunk000Sub000Block029Part005

theorem surrogateDiagonalTailChunk000Sub000Block029Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block029Part005CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block029Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block029Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block029Part005CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block029Part005SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block029Part005] using hcert

def TailChunk000Sub000Block029Part006SupportExplicit : Finset ℕ :=
  ([1254] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block029Part006 : ℚ :=
  (376181017 : ℚ) / 139995993600

def SurrogateDiagonalTailChunk000Sub000Block029Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1254
    = surrogateDiagTailX0RatChunk000Sub000Block029Part006

theorem surrogateDiagonalTailChunk000Sub000Block029Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block029Part006CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block029Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block029Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block029Part006CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block029Part006SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block029Part006] using hcert

def TailChunk000Sub000Block029Part007SupportExplicit : Finset ℕ :=
  ([1255] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block029Part007 : ℚ :=
  (6198020357 : ℚ) / 50010000000000

def SurrogateDiagonalTailChunk000Sub000Block029Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1255
    = surrogateDiagTailX0RatChunk000Sub000Block029Part007

theorem surrogateDiagonalTailChunk000Sub000Block029Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block029Part007CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block029Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block029Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block029Part007CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block029Part007SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block029Part007] using hcert

def TailChunk000Sub000Block029Part008SupportExplicit : Finset ℕ :=
  ([1257] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block029Part008 : ℚ :=
  (52541925 : ℚ) / 244227809408

def SurrogateDiagonalTailChunk000Sub000Block029Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1257
    = surrogateDiagTailX0RatChunk000Sub000Block029Part008

theorem surrogateDiagonalTailChunk000Sub000Block029Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block029Part008CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block029Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block029Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block029Part008CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block029Part008SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block029Part008] using hcert

def TailChunk000Sub000Block029Part009SupportExplicit : Finset ℕ :=
  ([1258] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block029Part009 : ℚ :=
  (90536718725 : ℚ) / 137621661548544

def SurrogateDiagonalTailChunk000Sub000Block029Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1258
    = surrogateDiagTailX0RatChunk000Sub000Block029Part009

theorem surrogateDiagonalTailChunk000Sub000Block029Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block029Part009CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block029Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block029Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block029Part009CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block029Part009SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block029Part009] using hcert

def TailChunk000Sub000Block029Part010SupportExplicit : Finset ℕ :=
  ([1259] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block029Part010 : ℚ :=
  (198016243925 : ℚ) / 3131262144823524

def SurrogateDiagonalTailChunk000Sub000Block029Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1259
    = surrogateDiagTailX0RatChunk000Sub000Block029Part010

theorem surrogateDiagonalTailChunk000Sub000Block029Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block029Part010CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block029Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block029Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block029Part010CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block029Part010SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block029Part010] using hcert

def TailChunk000Sub000Block029Part011SupportExplicit : Finset ℕ :=
  ([1261] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block029Part011 : ℚ :=
  (90802781875 : ℚ) / 1100973292388352

def SurrogateDiagonalTailChunk000Sub000Block029Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1261
    = surrogateDiagTailX0RatChunk000Sub000Block029Part011

theorem surrogateDiagonalTailChunk000Sub000Block029Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block029Part011CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block029Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block029Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block029Part011CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block029Part011SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block029Part011] using hcert

def TailChunk000Sub000Block029Part012SupportExplicit : Finset ℕ :=
  ([1262] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block029Part012 : ℚ :=
  (1988017873 : ℚ) / 3939027898050

def SurrogateDiagonalTailChunk000Sub000Block029Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1262
    = surrogateDiagTailX0RatChunk000Sub000Block029Part012

theorem surrogateDiagonalTailChunk000Sub000Block029Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block029Part012CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block029Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block029Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block029Part012CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block029Part012SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block029Part012] using hcert

def TailChunk000Sub000Block029Part013SupportExplicit : Finset ℕ :=
  ([1263] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block029Part013 : ℚ :=
  (707263 : ℚ) / 3319142400

def SurrogateDiagonalTailChunk000Sub000Block029Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1263
    = surrogateDiagTailX0RatChunk000Sub000Block029Part013

theorem surrogateDiagonalTailChunk000Sub000Block029Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block029Part013CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block029Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block029Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block029Part013CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block029Part013SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block029Part013] using hcert

def TailChunk000Sub000Block029Part014SupportExplicit : Finset ℕ :=
  ([1265] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block029Part014 : ℚ :=
  (11125089961 : ℚ) / 59981529907200

def SurrogateDiagonalTailChunk000Sub000Block029Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1265
    = surrogateDiagTailX0RatChunk000Sub000Block029Part014

theorem surrogateDiagonalTailChunk000Sub000Block029Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block029Part014CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block029Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block029Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block029Part014CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block029Part014SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block029Part014] using hcert

def TailChunk000Sub000Block029Part015SupportExplicit : Finset ℕ :=
  ([1266] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block029Part015 : ℚ :=
  (16879 : ℚ) / 9878400

def SurrogateDiagonalTailChunk000Sub000Block029Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1266
    = surrogateDiagTailX0RatChunk000Sub000Block029Part015

theorem surrogateDiagonalTailChunk000Sub000Block029Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block029Part015CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block029Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block029Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block029Part015CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block029Part015SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block029Part015] using hcert

def TailChunk000Sub000Block029Part016SupportExplicit : Finset ℕ :=
  ([1267] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block029Part016 : ℚ :=
  (168954247 : ℚ) / 1679951923200

def SurrogateDiagonalTailChunk000Sub000Block029Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1267
    = surrogateDiagTailX0RatChunk000Sub000Block029Part016

theorem surrogateDiagonalTailChunk000Sub000Block029Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block029Part016CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block029Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block029Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block029Part016CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block029Part016SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block029Part016] using hcert

def TailChunk000Sub000Block029Part017SupportExplicit : Finset ℕ :=
  ([1270] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block029Part017 : ℚ :=
  (8835579175 : ℚ) / 8963476816896

def SurrogateDiagonalTailChunk000Sub000Block029Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1270
    = surrogateDiagTailX0RatChunk000Sub000Block029Part017

theorem surrogateDiagonalTailChunk000Sub000Block029Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block029Part017CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block029Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block029Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block029Part017CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block029Part017SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block029Part017] using hcert

def TailChunk000Sub000Block029Part018SupportExplicit : Finset ℕ :=
  ([1271] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block029Part018 : ℚ :=
  (15240098179 : ℚ) / 207401472000000

def SurrogateDiagonalTailChunk000Sub000Block029Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1271
    = surrogateDiagTailX0RatChunk000Sub000Block029Part018

theorem surrogateDiagonalTailChunk000Sub000Block029Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block029Part018CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block029Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block029Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block029Part018CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block029Part018SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block029Part018] using hcert

def TailChunk000Sub000Block029Part019SupportExplicit : Finset ℕ :=
  ([1273] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block029Part019 : ℚ :=
  (377777664925 : ℚ) / 4980725661783168

def SurrogateDiagonalTailChunk000Sub000Block029Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1273
    = surrogateDiagTailX0RatChunk000Sub000Block029Part019

theorem surrogateDiagonalTailChunk000Sub000Block029Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block029Part019CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block029Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block029Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block029Part019CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block029Part019SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block029Part019] using hcert

def TailChunk000Sub000Block029Part020SupportExplicit : Finset ℕ :=
  ([1277] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block029Part020 : ℚ :=
  (203718820325 : ℚ) / 3314359097991744

def SurrogateDiagonalTailChunk000Sub000Block029Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1277
    = surrogateDiagTailX0RatChunk000Sub000Block029Part020

theorem surrogateDiagonalTailChunk000Sub000Block029Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block029Part020CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block029Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block029Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block029Part020CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block029Part020SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block029Part020] using hcert

def TailChunk000Sub000Block029Part021SupportExplicit : Finset ℕ :=
  ([1279] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block029Part021 : ℚ :=
  (204357436925 : ℚ) / 3335187684976164

def SurrogateDiagonalTailChunk000Sub000Block029Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1279
    = surrogateDiagTailX0RatChunk000Sub000Block029Part021

theorem surrogateDiagonalTailChunk000Sub000Block029Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block029Part021CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block029Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block029Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block029Part021CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block029Part021SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block029Part021] using hcert

def TailChunk000Sub000Block029Part022SupportExplicit : Finset ℕ :=
  ([1281] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block029Part022 : ℚ :=
  (9176280529 : ℚ) / 26879230771200

def SurrogateDiagonalTailChunk000Sub000Block029Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1281
    = surrogateDiagTailX0RatChunk000Sub000Block029Part022

theorem surrogateDiagonalTailChunk000Sub000Block029Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block029Part022CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block029Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block029Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block029Part022CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block029Part022SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block029Part022] using hcert

def TailChunk000Sub000Block029Part023SupportExplicit : Finset ℕ :=
  ([1282] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block029Part023 : ℚ :=
  (7181788999 : ℚ) / 16780571443200

def SurrogateDiagonalTailChunk000Sub000Block029Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1282
    = surrogateDiagTailX0RatChunk000Sub000Block029Part023

theorem surrogateDiagonalTailChunk000Sub000Block029Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block029Part023CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block029Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block029Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block029Part023CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block029Part023SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block029Part023] using hcert

def TailChunk000Sub000Block029Part024SupportExplicit : Finset ℕ :=
  ([1283] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block029Part024 : ℚ :=
  (205637668325 : ℚ) / 3377139216004644

def SurrogateDiagonalTailChunk000Sub000Block029Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1283
    = surrogateDiagTailX0RatChunk000Sub000Block029Part024

theorem surrogateDiagonalTailChunk000Sub000Block029Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block029Part024CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block029Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block029Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block029Part024CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block029Part024SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block029Part024] using hcert

def surrogateDiagonalTailChunk000Sub000Block029HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block029Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block029Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block029Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block029Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block029Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block029Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block029Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block029Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block029Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block029Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block029Head : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block029Part000
    + surrogateDiagTailX0RatChunk000Sub000Block029Part001
    + surrogateDiagTailX0RatChunk000Sub000Block029Part002
    + surrogateDiagTailX0RatChunk000Sub000Block029Part003
    + surrogateDiagTailX0RatChunk000Sub000Block029Part004
    + surrogateDiagTailX0RatChunk000Sub000Block029Part005
    + surrogateDiagTailX0RatChunk000Sub000Block029Part006
    + surrogateDiagTailX0RatChunk000Sub000Block029Part007
    + surrogateDiagTailX0RatChunk000Sub000Block029Part008
    + surrogateDiagTailX0RatChunk000Sub000Block029Part009

def surrogateDiagonalTailChunk000Sub000Block029MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block029Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block029Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block029Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block029Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block029Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block029Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block029Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block029Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block029Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block029Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block029Mid : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block029Part010
    + surrogateDiagTailX0RatChunk000Sub000Block029Part011
    + surrogateDiagTailX0RatChunk000Sub000Block029Part012
    + surrogateDiagTailX0RatChunk000Sub000Block029Part013
    + surrogateDiagTailX0RatChunk000Sub000Block029Part014
    + surrogateDiagTailX0RatChunk000Sub000Block029Part015
    + surrogateDiagTailX0RatChunk000Sub000Block029Part016
    + surrogateDiagTailX0RatChunk000Sub000Block029Part017
    + surrogateDiagTailX0RatChunk000Sub000Block029Part018
    + surrogateDiagTailX0RatChunk000Sub000Block029Part019

def surrogateDiagonalTailChunk000Sub000Block029TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block029Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block029Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block029Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block029Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block029Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block029Tail : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block029Part020
    + surrogateDiagTailX0RatChunk000Sub000Block029Part021
    + surrogateDiagTailX0RatChunk000Sub000Block029Part022
    + surrogateDiagTailX0RatChunk000Sub000Block029Part023
    + surrogateDiagTailX0RatChunk000Sub000Block029Part024

def surrogateDiagonalTailChunk000Sub000Block029Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub000Block029HeadSum X0
    + surrogateDiagonalTailChunk000Sub000Block029MidSum X0
    + surrogateDiagonalTailChunk000Sub000Block029TailSum X0

def surrogateDiagTailX0RatChunk000Sub000Block029 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block029Part000
    + surrogateDiagTailX0RatChunk000Sub000Block029Part001
    + surrogateDiagTailX0RatChunk000Sub000Block029Part002
    + surrogateDiagTailX0RatChunk000Sub000Block029Part003
    + surrogateDiagTailX0RatChunk000Sub000Block029Part004
    + surrogateDiagTailX0RatChunk000Sub000Block029Part005
    + surrogateDiagTailX0RatChunk000Sub000Block029Part006
    + surrogateDiagTailX0RatChunk000Sub000Block029Part007
    + surrogateDiagTailX0RatChunk000Sub000Block029Part008
    + surrogateDiagTailX0RatChunk000Sub000Block029Part009
    + surrogateDiagTailX0RatChunk000Sub000Block029Part010
    + surrogateDiagTailX0RatChunk000Sub000Block029Part011
    + surrogateDiagTailX0RatChunk000Sub000Block029Part012
    + surrogateDiagTailX0RatChunk000Sub000Block029Part013
    + surrogateDiagTailX0RatChunk000Sub000Block029Part014
    + surrogateDiagTailX0RatChunk000Sub000Block029Part015
    + surrogateDiagTailX0RatChunk000Sub000Block029Part016
    + surrogateDiagTailX0RatChunk000Sub000Block029Part017
    + surrogateDiagTailX0RatChunk000Sub000Block029Part018
    + surrogateDiagTailX0RatChunk000Sub000Block029Part019
    + surrogateDiagTailX0RatChunk000Sub000Block029Part020
    + surrogateDiagTailX0RatChunk000Sub000Block029Part021
    + surrogateDiagTailX0RatChunk000Sub000Block029Part022
    + surrogateDiagTailX0RatChunk000Sub000Block029Part023
    + surrogateDiagTailX0RatChunk000Sub000Block029Part024

theorem surrogateDiagTailX0RatChunk000Sub000Block029_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk000Sub000Block029Head + surrogateDiagTailX0RatChunk000Sub000Block029Mid + surrogateDiagTailX0RatChunk000Sub000Block029Tail =
      surrogateDiagTailX0RatChunk000Sub000Block029 := by
  unfold surrogateDiagTailX0RatChunk000Sub000Block029Head surrogateDiagTailX0RatChunk000Sub000Block029Mid surrogateDiagTailX0RatChunk000Sub000Block029Tail surrogateDiagTailX0RatChunk000Sub000Block029
  ring

def SurrogateDiagonalTailChunk000Sub000Block029HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block029HeadSum X0 = surrogateDiagTailX0RatChunk000Sub000Block029Head

def SurrogateDiagonalTailChunk000Sub000Block029MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block029MidSum X0 = surrogateDiagTailX0RatChunk000Sub000Block029Mid

def SurrogateDiagonalTailChunk000Sub000Block029TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block029TailSum X0 = surrogateDiagTailX0RatChunk000Sub000Block029Tail

theorem surrogateDiagonalTailChunk000Sub000Block029_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk000Sub000Block029HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk000Sub000Block029MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk000Sub000Block029TailCertificateAt X0) :
    surrogateDiagonalTailChunk000Sub000Block029Sum X0 = surrogateDiagTailX0RatChunk000Sub000Block029 := by
  unfold SurrogateDiagonalTailChunk000Sub000Block029HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk000Sub000Block029MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk000Sub000Block029TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk000Sub000Block029Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk000Sub000Block029_eq_head_add_mid_add_tail

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

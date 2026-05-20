import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0TailPilot25

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

open scoped BigOperators

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

/- Generated direct-term certificate blocks for tail chunk 000, subchunk 001, blocks [120,130). -/

/-- Block 120 covers tail-support indices [8000,8025) and q from 13213 to 13251. -/

def TailChunk000Sub001Block120Part000SupportExplicit : Finset ℕ :=
  ([13213] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block120Part000 : ℚ :=
  (84604541351 : ℚ) / 564334825887498240

def SurrogateDiagonalTailChunk000Sub001Block120Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13213
    = surrogateDiagTailX0RatChunk000Sub001Block120Part000

theorem surrogateDiagonalTailChunk000Sub001Block120Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block120Part000CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block120Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block120Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block120Part000CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block120Part000SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block120Part000] using hcert

def TailChunk000Sub001Block120Part001SupportExplicit : Finset ℕ :=
  ([13214] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block120Part001 : ℚ :=
  (682069515625 : ℚ) / 1190477372029642962

def SurrogateDiagonalTailChunk000Sub001Block120Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13214
    = surrogateDiagTailX0RatChunk000Sub001Block120Part001

theorem surrogateDiagonalTailChunk000Sub001Block120Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block120Part001CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block120Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block120Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block120Part001CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block120Part001SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block120Part001] using hcert

def TailChunk000Sub001Block120Part002SupportExplicit : Finset ℕ :=
  ([13215] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block120Part002 : ℚ :=
  (9298721811 : ℚ) / 16378956433326080

def SurrogateDiagonalTailChunk000Sub001Block120Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13215
    = surrogateDiagTailX0RatChunk000Sub001Block120Part002

theorem surrogateDiagonalTailChunk000Sub001Block120Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block120Part002CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block120Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block120Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block120Part002CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block120Part002SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block120Part002] using hcert

def TailChunk000Sub001Block120Part003SupportExplicit : Finset ℕ :=
  ([13217] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block120Part003 : ℚ :=
  (2729517015625 : ℚ) / 19070715506034081792

def SurrogateDiagonalTailChunk000Sub001Block120Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13217
    = surrogateDiagTailX0RatChunk000Sub001Block120Part003

theorem surrogateDiagonalTailChunk000Sub001Block120Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block120Part003CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block120Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block120Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block120Part003CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block120Part003SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block120Part003] using hcert

def TailChunk000Sub001Block120Part004SupportExplicit : Finset ℕ :=
  ([13218] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block120Part004 : ℚ :=
  (60630875 : ℚ) / 31347866973888

def SurrogateDiagonalTailChunk000Sub001Block120Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13218
    = surrogateDiagTailX0RatChunk000Sub001Block120Part004

theorem surrogateDiagonalTailChunk000Sub001Block120Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block120Part004CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block120Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block120Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block120Part004CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block120Part004SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block120Part004] using hcert

def TailChunk000Sub001Block120Part005SupportExplicit : Finset ℕ :=
  ([13219] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block120Part005 : ℚ :=
  (2730343140625 : ℚ) / 19082262143412434322

def SurrogateDiagonalTailChunk000Sub001Block120Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13219
    = surrogateDiagTailX0RatChunk000Sub001Block120Part005

theorem surrogateDiagonalTailChunk000Sub001Block120Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block120Part005CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block120Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block120Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block120Part005CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block120Part005SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block120Part005] using hcert

def TailChunk000Sub001Block120Part006SupportExplicit : Finset ℕ :=
  ([13222] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block120Part006 : ℚ :=
  (97343592367 : ℚ) / 129625920000000000

def SurrogateDiagonalTailChunk000Sub001Block120Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13222
    = surrogateDiagTailX0RatChunk000Sub001Block120Part006

theorem surrogateDiagonalTailChunk000Sub001Block120Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block120Part006CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block120Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block120Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block120Part006CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block120Part006SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block120Part006] using hcert

def TailChunk000Sub001Block120Part007SupportExplicit : Finset ℕ :=
  ([13223] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block120Part007 : ℚ :=
  (2117160841075 : ℚ) / 10293897249404485632

def SurrogateDiagonalTailChunk000Sub001Block120Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13223
    = surrogateDiagTailX0RatChunk000Sub001Block120Part007

theorem surrogateDiagonalTailChunk000Sub001Block120Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block120Part007CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block120Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block120Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block120Part007CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block120Part007SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block120Part007] using hcert

def TailChunk000Sub001Block120Part008SupportExplicit : Finset ℕ :=
  ([13226] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block120Part008 : ℚ :=
  (2527068375175 : ℚ) / 3713929811589070848

def SurrogateDiagonalTailChunk000Sub001Block120Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13226
    = surrogateDiagTailX0RatChunk000Sub001Block120Part008

theorem surrogateDiagonalTailChunk000Sub001Block120Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block120Part008CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block120Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block120Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block120Part008CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block120Part008SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block120Part008] using hcert

def TailChunk000Sub001Block120Part009SupportExplicit : Finset ℕ :=
  ([13227] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block120Part009 : ℚ :=
  (4858240559125 : ℚ) / 15104737593661882368

def SurrogateDiagonalTailChunk000Sub001Block120Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13227
    = surrogateDiagTailX0RatChunk000Sub001Block120Part009

theorem surrogateDiagonalTailChunk000Sub001Block120Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block120Part009CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block120Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block120Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block120Part009CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block120Part009SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block120Part009] using hcert

def TailChunk000Sub001Block120Part010SupportExplicit : Finset ℕ :=
  ([13229] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block120Part010 : ℚ :=
  (2734475640625 : ℚ) / 19140073999750240032

def SurrogateDiagonalTailChunk000Sub001Block120Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13229
    = surrogateDiagTailX0RatChunk000Sub001Block120Part010

theorem surrogateDiagonalTailChunk000Sub001Block120Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block120Part010CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block120Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block120Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block120Part010CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block120Part010SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block120Part010] using hcert

def TailChunk000Sub001Block120Part011SupportExplicit : Finset ℕ :=
  ([13231] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block120Part011 : ℚ :=
  (425351942299 : ℚ) / 2856671220000000000

def SurrogateDiagonalTailChunk000Sub001Block120Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13231
    = surrogateDiagTailX0RatChunk000Sub001Block120Part011

theorem surrogateDiagonalTailChunk000Sub001Block120Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block120Part011CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block120Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block120Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block120Part011CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block120Part011SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block120Part011] using hcert

def TailChunk000Sub001Block120Part012SupportExplicit : Finset ℕ :=
  ([13233] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block120Part012 : ℚ :=
  (168640724413 : ℚ) / 409681920000000000

def SurrogateDiagonalTailChunk000Sub001Block120Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13233
    = surrogateDiagTailX0RatChunk000Sub001Block120Part012

theorem surrogateDiagonalTailChunk000Sub001Block120Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block120Part012CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block120Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block120Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block120Part012CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block120Part012SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block120Part012] using hcert

def TailChunk000Sub001Block120Part013SupportExplicit : Finset ℕ :=
  ([13234] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block120Part013 : ℚ :=
  (2471946239575 : ℚ) / 3453080414483939328

def SurrogateDiagonalTailChunk000Sub001Block120Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13234
    = surrogateDiagTailX0RatChunk000Sub001Block120Part013

theorem surrogateDiagonalTailChunk000Sub001Block120Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block120Part013CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block120Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block120Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block120Part013CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block120Part013SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block120Part013] using hcert

def TailChunk000Sub001Block120Part014SupportExplicit : Finset ℕ :=
  ([13235] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block120Part014 : ℚ :=
  (7440848767525 : ℚ) / 31378066826881517568

def SurrogateDiagonalTailChunk000Sub001Block120Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13235
    = surrogateDiagTailX0RatChunk000Sub001Block120Part014

theorem surrogateDiagonalTailChunk000Sub001Block120Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block120Part014CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block120Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block120Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block120Part014CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block120Part014SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block120Part014] using hcert

def TailChunk000Sub001Block120Part015SupportExplicit : Finset ℕ :=
  ([13237] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block120Part015 : ℚ :=
  (15708528011 : ℚ) / 68038052889600000

def SurrogateDiagonalTailChunk000Sub001Block120Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13237
    = surrogateDiagTailX0RatChunk000Sub001Block120Part015

theorem surrogateDiagonalTailChunk000Sub001Block120Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block120Part015CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block120Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block120Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block120Part015CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block120Part015SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block120Part015] using hcert

def TailChunk000Sub001Block120Part016SupportExplicit : Finset ℕ :=
  ([13238] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block120Part016 : ℚ :=
  (684549390625 : ℚ) / 1199151123961948722

def SurrogateDiagonalTailChunk000Sub001Block120Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13238
    = surrogateDiagTailX0RatChunk000Sub001Block120Part016

theorem surrogateDiagonalTailChunk000Sub001Block120Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block120Part016CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block120Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block120Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block120Part016CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block120Part016SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block120Part016] using hcert

def TailChunk000Sub001Block120Part017SupportExplicit : Finset ℕ :=
  ([13241] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block120Part017 : ℚ :=
  (4383102025 : ℚ) / 30735394415473152

def SurrogateDiagonalTailChunk000Sub001Block120Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13241
    = surrogateDiagTailX0RatChunk000Sub001Block120Part017

theorem surrogateDiagonalTailChunk000Sub001Block120Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block120Part017CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block120Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block120Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block120Part017CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block120Part017SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block120Part017] using hcert

def TailChunk000Sub001Block120Part018SupportExplicit : Finset ℕ :=
  ([13242] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block120Part018 : ℚ :=
  (380407363525 : ℚ) / 236869357819644192

def SurrogateDiagonalTailChunk000Sub001Block120Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13242
    = surrogateDiagTailX0RatChunk000Sub001Block120Part018

theorem surrogateDiagonalTailChunk000Sub001Block120Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block120Part018CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block120Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block120Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block120Part018CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block120Part018SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block120Part018] using hcert

def TailChunk000Sub001Block120Part019SupportExplicit : Finset ℕ :=
  ([13243] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block120Part019 : ℚ :=
  (349662545953 : ℚ) / 1761557267821363200

def SurrogateDiagonalTailChunk000Sub001Block120Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13243
    = surrogateDiagTailX0RatChunk000Sub001Block120Part019

theorem surrogateDiagonalTailChunk000Sub001Block120Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block120Part019CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block120Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block120Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block120Part019CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block120Part019SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block120Part019] using hcert

def TailChunk000Sub001Block120Part020SupportExplicit : Finset ℕ :=
  ([13245] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block120Part020 : ℚ :=
  (3454432921075 : ℚ) / 6198136657161781248

def SurrogateDiagonalTailChunk000Sub001Block120Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13245
    = surrogateDiagTailX0RatChunk000Sub001Block120Part020

theorem surrogateDiagonalTailChunk000Sub001Block120Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block120Part020CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block120Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block120Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block120Part020CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block120Part020SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block120Part020] using hcert

def TailChunk000Sub001Block120Part021SupportExplicit : Finset ℕ :=
  ([13246] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block120Part021 : ℚ :=
  (97463729975 : ℚ) / 156153997679745024

def SurrogateDiagonalTailChunk000Sub001Block120Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13246
    = surrogateDiagTailX0RatChunk000Sub001Block120Part021

theorem surrogateDiagonalTailChunk000Sub001Block120Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block120Part021CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block120Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block120Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block120Part021CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block120Part021SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block120Part021] using hcert

def TailChunk000Sub001Block120Part022SupportExplicit : Finset ℕ :=
  ([13247] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block120Part022 : ℚ :=
  (1598471554075 : ℚ) / 9280934436636822528

def SurrogateDiagonalTailChunk000Sub001Block120Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13247
    = surrogateDiagTailX0RatChunk000Sub001Block120Part022

theorem surrogateDiagonalTailChunk000Sub001Block120Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block120Part022CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block120Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block120Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block120Part022CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block120Part022SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block120Part022] using hcert

def TailChunk000Sub001Block120Part023SupportExplicit : Finset ℕ :=
  ([13249] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block120Part023 : ℚ :=
  (2742750015625 : ℚ) / 19256091694703050752

def SurrogateDiagonalTailChunk000Sub001Block120Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13249
    = surrogateDiagTailX0RatChunk000Sub001Block120Part023

theorem surrogateDiagonalTailChunk000Sub001Block120Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block120Part023CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block120Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block120Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block120Part023CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block120Part023SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block120Part023] using hcert

def TailChunk000Sub001Block120Part024SupportExplicit : Finset ℕ :=
  ([13251] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block120Part024 : ℚ :=
  (10923978329 : ℚ) / 23337052141132800

def SurrogateDiagonalTailChunk000Sub001Block120Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13251
    = surrogateDiagTailX0RatChunk000Sub001Block120Part024

theorem surrogateDiagonalTailChunk000Sub001Block120Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block120Part024CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block120Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block120Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block120Part024CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block120Part024SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block120Part024] using hcert

def surrogateDiagonalTailChunk000Sub001Block120HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block120Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block120Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block120Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block120Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block120Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block120Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block120Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block120Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block120Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block120Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block120Head : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block120Part000
    + surrogateDiagTailX0RatChunk000Sub001Block120Part001
    + surrogateDiagTailX0RatChunk000Sub001Block120Part002
    + surrogateDiagTailX0RatChunk000Sub001Block120Part003
    + surrogateDiagTailX0RatChunk000Sub001Block120Part004
    + surrogateDiagTailX0RatChunk000Sub001Block120Part005
    + surrogateDiagTailX0RatChunk000Sub001Block120Part006
    + surrogateDiagTailX0RatChunk000Sub001Block120Part007
    + surrogateDiagTailX0RatChunk000Sub001Block120Part008
    + surrogateDiagTailX0RatChunk000Sub001Block120Part009

def surrogateDiagonalTailChunk000Sub001Block120MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block120Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block120Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block120Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block120Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block120Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block120Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block120Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block120Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block120Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block120Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block120Mid : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block120Part010
    + surrogateDiagTailX0RatChunk000Sub001Block120Part011
    + surrogateDiagTailX0RatChunk000Sub001Block120Part012
    + surrogateDiagTailX0RatChunk000Sub001Block120Part013
    + surrogateDiagTailX0RatChunk000Sub001Block120Part014
    + surrogateDiagTailX0RatChunk000Sub001Block120Part015
    + surrogateDiagTailX0RatChunk000Sub001Block120Part016
    + surrogateDiagTailX0RatChunk000Sub001Block120Part017
    + surrogateDiagTailX0RatChunk000Sub001Block120Part018
    + surrogateDiagTailX0RatChunk000Sub001Block120Part019

def surrogateDiagonalTailChunk000Sub001Block120TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block120Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block120Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block120Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block120Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block120Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block120Tail : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block120Part020
    + surrogateDiagTailX0RatChunk000Sub001Block120Part021
    + surrogateDiagTailX0RatChunk000Sub001Block120Part022
    + surrogateDiagTailX0RatChunk000Sub001Block120Part023
    + surrogateDiagTailX0RatChunk000Sub001Block120Part024

def surrogateDiagonalTailChunk000Sub001Block120Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub001Block120HeadSum X0
    + surrogateDiagonalTailChunk000Sub001Block120MidSum X0
    + surrogateDiagonalTailChunk000Sub001Block120TailSum X0

def surrogateDiagTailX0RatChunk000Sub001Block120 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block120Part000
    + surrogateDiagTailX0RatChunk000Sub001Block120Part001
    + surrogateDiagTailX0RatChunk000Sub001Block120Part002
    + surrogateDiagTailX0RatChunk000Sub001Block120Part003
    + surrogateDiagTailX0RatChunk000Sub001Block120Part004
    + surrogateDiagTailX0RatChunk000Sub001Block120Part005
    + surrogateDiagTailX0RatChunk000Sub001Block120Part006
    + surrogateDiagTailX0RatChunk000Sub001Block120Part007
    + surrogateDiagTailX0RatChunk000Sub001Block120Part008
    + surrogateDiagTailX0RatChunk000Sub001Block120Part009
    + surrogateDiagTailX0RatChunk000Sub001Block120Part010
    + surrogateDiagTailX0RatChunk000Sub001Block120Part011
    + surrogateDiagTailX0RatChunk000Sub001Block120Part012
    + surrogateDiagTailX0RatChunk000Sub001Block120Part013
    + surrogateDiagTailX0RatChunk000Sub001Block120Part014
    + surrogateDiagTailX0RatChunk000Sub001Block120Part015
    + surrogateDiagTailX0RatChunk000Sub001Block120Part016
    + surrogateDiagTailX0RatChunk000Sub001Block120Part017
    + surrogateDiagTailX0RatChunk000Sub001Block120Part018
    + surrogateDiagTailX0RatChunk000Sub001Block120Part019
    + surrogateDiagTailX0RatChunk000Sub001Block120Part020
    + surrogateDiagTailX0RatChunk000Sub001Block120Part021
    + surrogateDiagTailX0RatChunk000Sub001Block120Part022
    + surrogateDiagTailX0RatChunk000Sub001Block120Part023
    + surrogateDiagTailX0RatChunk000Sub001Block120Part024

theorem surrogateDiagTailX0RatChunk000Sub001Block120_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk000Sub001Block120Head + surrogateDiagTailX0RatChunk000Sub001Block120Mid + surrogateDiagTailX0RatChunk000Sub001Block120Tail =
      surrogateDiagTailX0RatChunk000Sub001Block120 := by
  unfold surrogateDiagTailX0RatChunk000Sub001Block120Head surrogateDiagTailX0RatChunk000Sub001Block120Mid surrogateDiagTailX0RatChunk000Sub001Block120Tail surrogateDiagTailX0RatChunk000Sub001Block120
  ring

def SurrogateDiagonalTailChunk000Sub001Block120HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block120HeadSum X0 = surrogateDiagTailX0RatChunk000Sub001Block120Head

def SurrogateDiagonalTailChunk000Sub001Block120MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block120MidSum X0 = surrogateDiagTailX0RatChunk000Sub001Block120Mid

def SurrogateDiagonalTailChunk000Sub001Block120TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block120TailSum X0 = surrogateDiagTailX0RatChunk000Sub001Block120Tail

theorem surrogateDiagonalTailChunk000Sub001Block120_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk000Sub001Block120HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk000Sub001Block120MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk000Sub001Block120TailCertificateAt X0) :
    surrogateDiagonalTailChunk000Sub001Block120Sum X0 = surrogateDiagTailX0RatChunk000Sub001Block120 := by
  unfold SurrogateDiagonalTailChunk000Sub001Block120HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk000Sub001Block120MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk000Sub001Block120TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk000Sub001Block120Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk000Sub001Block120_eq_head_add_mid_add_tail

/-- Block 121 covers tail-support indices [8025,8050) and q from 13253 to 13291. -/

def TailChunk000Sub001Block121Part000SupportExplicit : Finset ℕ :=
  ([13253] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block121Part000 : ℚ :=
  (10328721174325 : ℚ) / 66453575808267583488

def SurrogateDiagonalTailChunk000Sub001Block121Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13253
    = surrogateDiagTailX0RatChunk000Sub001Block121Part000

theorem surrogateDiagonalTailChunk000Sub001Block121Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block121Part000CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block121Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block121Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block121Part000CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block121Part000SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block121Part000] using hcert

def TailChunk000Sub001Block121Part001SupportExplicit : Finset ℕ :=
  ([13255] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block121Part001 : ℚ :=
  (7130525719 : ℚ) / 23597678592000000

def SurrogateDiagonalTailChunk000Sub001Block121Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13255
    = surrogateDiagTailX0RatChunk000Sub001Block121Part001

theorem surrogateDiagonalTailChunk000Sub001Block121Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block121Part001CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block121Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block121Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block121Part001CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block121Part001SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block121Part001] using hcert

def TailChunk000Sub001Block121Part002SupportExplicit : Finset ℕ :=
  ([13258] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block121Part002 : ℚ :=
  (2295541862575 : ℚ) / 2595352823232732288

def SurrogateDiagonalTailChunk000Sub001Block121Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13258
    = surrogateDiagTailX0RatChunk000Sub001Block121Part002

theorem surrogateDiagonalTailChunk000Sub001Block121Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block121Part002CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block121Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block121Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block121Part002CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block121Part002SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block121Part002] using hcert

def TailChunk000Sub001Block121Part003SupportExplicit : Finset ℕ :=
  ([13259] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block121Part003 : ℚ :=
  (2746891890625 : ℚ) / 19314297930537483762

def SurrogateDiagonalTailChunk000Sub001Block121Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13259
    = surrogateDiagTailX0RatChunk000Sub001Block121Part003

theorem surrogateDiagonalTailChunk000Sub001Block121Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block121Part003CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block121Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block121Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block121Part003CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block121Part003SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block121Part003] using hcert

def TailChunk000Sub001Block121Part004SupportExplicit : Finset ℕ :=
  ([13261] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block121Part004 : ℚ :=
  (10675433973175 : ℚ) / 71945628206341029888

def SurrogateDiagonalTailChunk000Sub001Block121Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13261
    = surrogateDiagTailX0RatChunk000Sub001Block121Part004

theorem surrogateDiagonalTailChunk000Sub001Block121Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block121Part004CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block121Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block121Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block121Part004CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block121Part004SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block121Part004] using hcert

def TailChunk000Sub001Block121Part005SupportExplicit : Finset ℕ :=
  ([13262] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block121Part005 : ℚ :=
  (142045935875 : ℚ) / 213875653714707456

def SurrogateDiagonalTailChunk000Sub001Block121Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13262
    = surrogateDiagTailX0RatChunk000Sub001Block121Part005

theorem surrogateDiagonalTailChunk000Sub001Block121Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block121Part005CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block121Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block121Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block121Part005CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block121Part005SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block121Part005] using hcert

def TailChunk000Sub001Block121Part006SupportExplicit : Finset ℕ :=
  ([13263] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block121Part006 : ℚ :=
  (195388982317 : ℚ) / 610795614631987200

def SurrogateDiagonalTailChunk000Sub001Block121Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13263
    = surrogateDiagTailX0RatChunk000Sub001Block121Part006

theorem surrogateDiagonalTailChunk000Sub001Block121Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block121Part006CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block121Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block121Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block121Part006CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block121Part006SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block121Part006] using hcert

def TailChunk000Sub001Block121Part007SupportExplicit : Finset ℕ :=
  ([13265] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block121Part007 : ℚ :=
  (2919718821725 : ℚ) / 8468549480974270464

def SurrogateDiagonalTailChunk000Sub001Block121Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13265
    = surrogateDiagTailX0RatChunk000Sub001Block121Part007

theorem surrogateDiagonalTailChunk000Sub001Block121Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block121Part007CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block121Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block121Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block121Part007CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block121Part007SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block121Part007] using hcert

def TailChunk000Sub001Block121Part008SupportExplicit : Finset ℕ :=
  ([13267] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block121Part008 : ℚ :=
  (2750207640625 : ℚ) / 19360957846913135442

def SurrogateDiagonalTailChunk000Sub001Block121Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13267
    = surrogateDiagTailX0RatChunk000Sub001Block121Part008

theorem surrogateDiagonalTailChunk000Sub001Block121Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block121Part008CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block121Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block121Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block121Part008CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block121Part008SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block121Part008] using hcert

def TailChunk000Sub001Block121Part009SupportExplicit : Finset ℕ :=
  ([13269] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block121Part009 : ℚ :=
  (444467777975 : ℚ) / 1390686085524624768

def SurrogateDiagonalTailChunk000Sub001Block121Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13269
    = surrogateDiagTailX0RatChunk000Sub001Block121Part009

theorem surrogateDiagonalTailChunk000Sub001Block121Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block121Part009CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block121Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block121Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block121Part009CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block121Part009SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block121Part009] using hcert

def TailChunk000Sub001Block121Part010SupportExplicit : Finset ℕ :=
  ([13270] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block121Part010 : ℚ :=
  (174133210325 : ℚ) / 164914815950636544

def SurrogateDiagonalTailChunk000Sub001Block121Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13270
    = surrogateDiagTailX0RatChunk000Sub001Block121Part010

theorem surrogateDiagonalTailChunk000Sub001Block121Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block121Part010CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block121Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block121Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block121Part010CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block121Part010SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block121Part010] using hcert

def TailChunk000Sub001Block121Part011SupportExplicit : Finset ℕ :=
  ([13271] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block121Part011 : ℚ :=
  (10504288675 : ℚ) / 66334773554970624

def SurrogateDiagonalTailChunk000Sub001Block121Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13271
    = surrogateDiagTailX0RatChunk000Sub001Block121Part011

theorem surrogateDiagonalTailChunk000Sub001Block121Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block121Part011CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block121Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block121Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block121Part011CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block121Part011SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block121Part011] using hcert

def TailChunk000Sub001Block121Part012SupportExplicit : Finset ℕ :=
  ([13273] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block121Part012 : ℚ :=
  (192570732053 : ℚ) / 1122490116620697600

def SurrogateDiagonalTailChunk000Sub001Block121Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13273
    = surrogateDiagTailX0RatChunk000Sub001Block121Part012

theorem surrogateDiagonalTailChunk000Sub001Block121Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block121Part012CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block121Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block121Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block121Part012CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block121Part012SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block121Part012] using hcert

def TailChunk000Sub001Block121Part013SupportExplicit : Finset ℕ :=
  ([13274] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block121Part013 : ℚ :=
  (688277640625 : ℚ) / 1212250514096254752

def SurrogateDiagonalTailChunk000Sub001Block121Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13274
    = surrogateDiagTailX0RatChunk000Sub001Block121Part013

theorem surrogateDiagonalTailChunk000Sub001Block121Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block121Part013CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block121Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block121Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block121Part013CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block121Part013SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block121Part013] using hcert

def TailChunk000Sub001Block121Part014SupportExplicit : Finset ℕ :=
  ([13277] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block121Part014 : ℚ :=
  (331858147603 : ℚ) / 1573834063872000000

def SurrogateDiagonalTailChunk000Sub001Block121Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13277
    = surrogateDiagTailX0RatChunk000Sub001Block121Part014

theorem surrogateDiagonalTailChunk000Sub001Block121Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block121Part014CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block121Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block121Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block121Part014CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block121Part014SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block121Part014] using hcert

def TailChunk000Sub001Block121Part015SupportExplicit : Finset ℕ :=
  ([13278] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block121Part015 : ℚ :=
  (535125 : ℚ) / 279194180608

def SurrogateDiagonalTailChunk000Sub001Block121Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13278
    = surrogateDiagTailX0RatChunk000Sub001Block121Part015

theorem surrogateDiagonalTailChunk000Sub001Block121Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block121Part015CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block121Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block121Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block121Part015CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block121Part015SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block121Part015] using hcert

def TailChunk000Sub001Block121Part016SupportExplicit : Finset ℕ :=
  ([13281] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block121Part016 : ℚ :=
  (931586801825 : ℚ) / 2027858050035744768

def SurrogateDiagonalTailChunk000Sub001Block121Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13281
    = surrogateDiagTailX0RatChunk000Sub001Block121Part016

theorem surrogateDiagonalTailChunk000Sub001Block121Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block121Part016CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block121Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block121Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block121Part016CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block121Part016SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block121Part016] using hcert

def TailChunk000Sub001Block121Part017SupportExplicit : Finset ℕ :=
  ([13282] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block121Part017 : ℚ :=
  (656154170425 : ℚ) / 1038337122004180992

def SurrogateDiagonalTailChunk000Sub001Block121Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13282
    = surrogateDiagTailX0RatChunk000Sub001Block121Part017

theorem surrogateDiagonalTailChunk000Sub001Block121Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block121Part017CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block121Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block121Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block121Part017CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block121Part017SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block121Part017] using hcert

def TailChunk000Sub001Block121Part018SupportExplicit : Finset ℕ :=
  ([13283] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block121Part018 : ℚ :=
  (82014221975 : ℚ) / 538963058500768656

def SurrogateDiagonalTailChunk000Sub001Block121Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13283
    = surrogateDiagTailX0RatChunk000Sub001Block121Part018

theorem surrogateDiagonalTailChunk000Sub001Block121Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block121Part018CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block121Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block121Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block121Part018CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block121Part018SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block121Part018] using hcert

def TailChunk000Sub001Block121Part019SupportExplicit : Finset ℕ :=
  ([13285] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block121Part019 : ℚ :=
  (7497187820275 : ℚ) / 31855109844592754688

def SurrogateDiagonalTailChunk000Sub001Block121Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13285
    = surrogateDiagTailX0RatChunk000Sub001Block121Part019

theorem surrogateDiagonalTailChunk000Sub001Block121Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block121Part019CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block121Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block121Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block121Part019CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block121Part019SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block121Part019] using hcert

def TailChunk000Sub001Block121Part020SupportExplicit : Finset ℕ :=
  ([13286] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block121Part020 : ℚ :=
  (514393733575 : ℚ) / 451467860709998592

def SurrogateDiagonalTailChunk000Sub001Block121Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13286
    = surrogateDiagTailX0RatChunk000Sub001Block121Part020

theorem surrogateDiagonalTailChunk000Sub001Block121Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block121Part020CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block121Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block121Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block121Part020CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block121Part020SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block121Part020] using hcert

def TailChunk000Sub001Block121Part021SupportExplicit : Finset ℕ :=
  ([13287] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block121Part021 : ℚ :=
  (2910574328975 : ℚ) / 6737746925015737344

def SurrogateDiagonalTailChunk000Sub001Block121Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13287
    = surrogateDiagTailX0RatChunk000Sub001Block121Part021

theorem surrogateDiagonalTailChunk000Sub001Block121Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block121Part021CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block121Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block121Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block121Part021CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block121Part021SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block121Part021] using hcert

def TailChunk000Sub001Block121Part022SupportExplicit : Finset ℕ :=
  ([13289] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block121Part022 : ℚ :=
  (157739768675 : ℚ) / 1068460599605723136

def SurrogateDiagonalTailChunk000Sub001Block121Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13289
    = surrogateDiagTailX0RatChunk000Sub001Block121Part022

theorem surrogateDiagonalTailChunk000Sub001Block121Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block121Part022CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block121Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block121Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block121Part022CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block121Part022SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block121Part022] using hcert

def TailChunk000Sub001Block121Part023SupportExplicit : Finset ℕ :=
  ([13290] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block121Part023 : ℚ :=
  (102162664575 : ℚ) / 65151532227411968

def SurrogateDiagonalTailChunk000Sub001Block121Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13290
    = surrogateDiagTailX0RatChunk000Sub001Block121Part023

theorem surrogateDiagonalTailChunk000Sub001Block121Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block121Part023CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block121Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block121Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block121Part023CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block121Part023SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block121Part023] using hcert

def TailChunk000Sub001Block121Part024SupportExplicit : Finset ℕ :=
  ([13291] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block121Part024 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block121Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13291
    = surrogateDiagTailX0RatChunk000Sub001Block121Part024

theorem surrogateDiagonalTailChunk000Sub001Block121Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block121Part024CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block121Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block121Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block121Part024CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block121Part024SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block121Part024] using hcert

def surrogateDiagonalTailChunk000Sub001Block121HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block121Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block121Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block121Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block121Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block121Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block121Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block121Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block121Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block121Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block121Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block121Head : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block121Part000
    + surrogateDiagTailX0RatChunk000Sub001Block121Part001
    + surrogateDiagTailX0RatChunk000Sub001Block121Part002
    + surrogateDiagTailX0RatChunk000Sub001Block121Part003
    + surrogateDiagTailX0RatChunk000Sub001Block121Part004
    + surrogateDiagTailX0RatChunk000Sub001Block121Part005
    + surrogateDiagTailX0RatChunk000Sub001Block121Part006
    + surrogateDiagTailX0RatChunk000Sub001Block121Part007
    + surrogateDiagTailX0RatChunk000Sub001Block121Part008
    + surrogateDiagTailX0RatChunk000Sub001Block121Part009

def surrogateDiagonalTailChunk000Sub001Block121MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block121Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block121Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block121Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block121Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block121Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block121Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block121Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block121Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block121Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block121Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block121Mid : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block121Part010
    + surrogateDiagTailX0RatChunk000Sub001Block121Part011
    + surrogateDiagTailX0RatChunk000Sub001Block121Part012
    + surrogateDiagTailX0RatChunk000Sub001Block121Part013
    + surrogateDiagTailX0RatChunk000Sub001Block121Part014
    + surrogateDiagTailX0RatChunk000Sub001Block121Part015
    + surrogateDiagTailX0RatChunk000Sub001Block121Part016
    + surrogateDiagTailX0RatChunk000Sub001Block121Part017
    + surrogateDiagTailX0RatChunk000Sub001Block121Part018
    + surrogateDiagTailX0RatChunk000Sub001Block121Part019

def surrogateDiagonalTailChunk000Sub001Block121TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block121Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block121Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block121Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block121Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block121Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block121Tail : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block121Part020
    + surrogateDiagTailX0RatChunk000Sub001Block121Part021
    + surrogateDiagTailX0RatChunk000Sub001Block121Part022
    + surrogateDiagTailX0RatChunk000Sub001Block121Part023
    + surrogateDiagTailX0RatChunk000Sub001Block121Part024

def surrogateDiagonalTailChunk000Sub001Block121Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub001Block121HeadSum X0
    + surrogateDiagonalTailChunk000Sub001Block121MidSum X0
    + surrogateDiagonalTailChunk000Sub001Block121TailSum X0

def surrogateDiagTailX0RatChunk000Sub001Block121 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block121Part000
    + surrogateDiagTailX0RatChunk000Sub001Block121Part001
    + surrogateDiagTailX0RatChunk000Sub001Block121Part002
    + surrogateDiagTailX0RatChunk000Sub001Block121Part003
    + surrogateDiagTailX0RatChunk000Sub001Block121Part004
    + surrogateDiagTailX0RatChunk000Sub001Block121Part005
    + surrogateDiagTailX0RatChunk000Sub001Block121Part006
    + surrogateDiagTailX0RatChunk000Sub001Block121Part007
    + surrogateDiagTailX0RatChunk000Sub001Block121Part008
    + surrogateDiagTailX0RatChunk000Sub001Block121Part009
    + surrogateDiagTailX0RatChunk000Sub001Block121Part010
    + surrogateDiagTailX0RatChunk000Sub001Block121Part011
    + surrogateDiagTailX0RatChunk000Sub001Block121Part012
    + surrogateDiagTailX0RatChunk000Sub001Block121Part013
    + surrogateDiagTailX0RatChunk000Sub001Block121Part014
    + surrogateDiagTailX0RatChunk000Sub001Block121Part015
    + surrogateDiagTailX0RatChunk000Sub001Block121Part016
    + surrogateDiagTailX0RatChunk000Sub001Block121Part017
    + surrogateDiagTailX0RatChunk000Sub001Block121Part018
    + surrogateDiagTailX0RatChunk000Sub001Block121Part019
    + surrogateDiagTailX0RatChunk000Sub001Block121Part020
    + surrogateDiagTailX0RatChunk000Sub001Block121Part021
    + surrogateDiagTailX0RatChunk000Sub001Block121Part022
    + surrogateDiagTailX0RatChunk000Sub001Block121Part023
    + surrogateDiagTailX0RatChunk000Sub001Block121Part024

theorem surrogateDiagTailX0RatChunk000Sub001Block121_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk000Sub001Block121Head + surrogateDiagTailX0RatChunk000Sub001Block121Mid + surrogateDiagTailX0RatChunk000Sub001Block121Tail =
      surrogateDiagTailX0RatChunk000Sub001Block121 := by
  unfold surrogateDiagTailX0RatChunk000Sub001Block121Head surrogateDiagTailX0RatChunk000Sub001Block121Mid surrogateDiagTailX0RatChunk000Sub001Block121Tail surrogateDiagTailX0RatChunk000Sub001Block121
  ring

def SurrogateDiagonalTailChunk000Sub001Block121HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block121HeadSum X0 = surrogateDiagTailX0RatChunk000Sub001Block121Head

def SurrogateDiagonalTailChunk000Sub001Block121MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block121MidSum X0 = surrogateDiagTailX0RatChunk000Sub001Block121Mid

def SurrogateDiagonalTailChunk000Sub001Block121TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block121TailSum X0 = surrogateDiagTailX0RatChunk000Sub001Block121Tail

theorem surrogateDiagonalTailChunk000Sub001Block121_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk000Sub001Block121HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk000Sub001Block121MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk000Sub001Block121TailCertificateAt X0) :
    surrogateDiagonalTailChunk000Sub001Block121Sum X0 = surrogateDiagTailX0RatChunk000Sub001Block121 := by
  unfold SurrogateDiagonalTailChunk000Sub001Block121HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk000Sub001Block121MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk000Sub001Block121TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk000Sub001Block121Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk000Sub001Block121_eq_head_add_mid_add_tail

/-- Block 122 covers tail-support indices [8050,8075) and q from 13295 to 13334. -/

def TailChunk000Sub001Block122Part000SupportExplicit : Finset ℕ :=
  ([13295] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block122Part000 : ℚ :=
  (442811105125 : ℚ) / 31951167401318565888

def SurrogateDiagonalTailChunk000Sub001Block122Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13295
    = surrogateDiagTailX0RatChunk000Sub001Block122Part000

theorem surrogateDiagonalTailChunk000Sub001Block122Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block122Part000CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block122Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block122Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block122Part000CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block122Part000SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block122Part000] using hcert

def TailChunk000Sub001Block122Part001SupportExplicit : Finset ℕ :=
  ([13297] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block122Part001 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block122Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13297
    = surrogateDiagTailX0RatChunk000Sub001Block122Part001

theorem surrogateDiagonalTailChunk000Sub001Block122Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block122Part001CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block122Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block122Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block122Part001CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block122Part001SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block122Part001] using hcert

def TailChunk000Sub001Block122Part002SupportExplicit : Finset ℕ :=
  ([13298] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block122Part002 : ℚ :=
  (64980803 : ℚ) / 5511082284057600

def SurrogateDiagonalTailChunk000Sub001Block122Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13298
    = surrogateDiagTailX0RatChunk000Sub001Block122Part002

theorem surrogateDiagonalTailChunk000Sub001Block122Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block122Part002CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block122Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block122Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block122Part002CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block122Part002SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block122Part002] using hcert

def TailChunk000Sub001Block122Part003SupportExplicit : Finset ℕ :=
  ([13299] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block122Part003 : ℚ :=
  (16689801259 : ℚ) / 89597435904000000

def SurrogateDiagonalTailChunk000Sub001Block122Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13299
    = surrogateDiagTailX0RatChunk000Sub001Block122Part003

theorem surrogateDiagonalTailChunk000Sub001Block122Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block122Part003CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block122Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block122Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block122Part003CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block122Part003SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block122Part003] using hcert

def TailChunk000Sub001Block122Part004SupportExplicit : Finset ℕ :=
  ([13301] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block122Part004 : ℚ :=
  (51743312375 : ℚ) / 35401741226347097664

def SurrogateDiagonalTailChunk000Sub001Block122Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13301
    = surrogateDiagTailX0RatChunk000Sub001Block122Part004

theorem surrogateDiagonalTailChunk000Sub001Block122Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block122Part004CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block122Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block122Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block122Part004CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block122Part004SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block122Part004] using hcert

def TailChunk000Sub001Block122Part005SupportExplicit : Finset ℕ :=
  ([13303] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block122Part005 : ℚ :=
  (1204119243 : ℚ) / 952223740000000000

def SurrogateDiagonalTailChunk000Sub001Block122Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13303
    = surrogateDiagTailX0RatChunk000Sub001Block122Part005

theorem surrogateDiagonalTailChunk000Sub001Block122Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block122Part005CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block122Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block122Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block122Part005CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block122Part005SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block122Part005] using hcert

def TailChunk000Sub001Block122Part006SupportExplicit : Finset ℕ :=
  ([13305] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block122Part006 : ℚ :=
  (442399955175 : ℚ) / 2103780569634144256

def SurrogateDiagonalTailChunk000Sub001Block122Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13305
    = surrogateDiagTailX0RatChunk000Sub001Block122Part006

theorem surrogateDiagonalTailChunk000Sub001Block122Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block122Part006CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block122Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block122Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block122Part006CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block122Part006SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block122Part006] using hcert

def TailChunk000Sub001Block122Part007SupportExplicit : Finset ℕ :=
  ([13306] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block122Part007 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block122Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13306
    = surrogateDiagTailX0RatChunk000Sub001Block122Part007

theorem surrogateDiagonalTailChunk000Sub001Block122Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block122Part007CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block122Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block122Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block122Part007CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block122Part007SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block122Part007] using hcert

def TailChunk000Sub001Block122Part008SupportExplicit : Finset ℕ :=
  ([13307] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block122Part008 : ℚ :=
  (9060690647 : ℚ) / 844648976016000000

def SurrogateDiagonalTailChunk000Sub001Block122Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13307
    = surrogateDiagTailX0RatChunk000Sub001Block122Part008

theorem surrogateDiagonalTailChunk000Sub001Block122Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block122Part008CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block122Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block122Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block122Part008CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block122Part008SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block122Part008] using hcert

def TailChunk000Sub001Block122Part009SupportExplicit : Finset ℕ :=
  ([13309] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block122Part009 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block122Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13309
    = surrogateDiagTailX0RatChunk000Sub001Block122Part009

theorem surrogateDiagonalTailChunk000Sub001Block122Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block122Part009CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block122Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block122Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block122Part009CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block122Part009SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block122Part009] using hcert

def TailChunk000Sub001Block122Part010SupportExplicit : Finset ℕ :=
  ([13313] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block122Part010 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block122Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13313
    = surrogateDiagTailX0RatChunk000Sub001Block122Part010

theorem surrogateDiagonalTailChunk000Sub001Block122Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block122Part010CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block122Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block122Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block122Part010CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block122Part010SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block122Part010] using hcert

def TailChunk000Sub001Block122Part011SupportExplicit : Finset ℕ :=
  ([13314] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block122Part011 : ℚ :=
  (652615371475 : ℚ) / 517011464570830848

def SurrogateDiagonalTailChunk000Sub001Block122Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13314
    = surrogateDiagTailX0RatChunk000Sub001Block122Part011

theorem surrogateDiagonalTailChunk000Sub001Block122Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block122Part011CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block122Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block122Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block122Part011CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block122Part011SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block122Part011] using hcert

def TailChunk000Sub001Block122Part012SupportExplicit : Finset ℕ :=
  ([13315] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block122Part012 : ℚ :=
  (886853670025 : ℚ) / 32143934078938564608

def SurrogateDiagonalTailChunk000Sub001Block122Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13315
    = surrogateDiagTailX0RatChunk000Sub001Block122Part012

theorem surrogateDiagonalTailChunk000Sub001Block122Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block122Part012CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block122Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block122Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block122Part012CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block122Part012SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block122Part012] using hcert

def TailChunk000Sub001Block122Part013SupportExplicit : Finset ℕ :=
  ([13317] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block122Part013 : ℚ :=
  (624295498925 : ℚ) / 6368138261277179904

def SurrogateDiagonalTailChunk000Sub001Block122Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13317
    = surrogateDiagTailX0RatChunk000Sub001Block122Part013

theorem surrogateDiagonalTailChunk000Sub001Block122Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block122Part013CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block122Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block122Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block122Part013CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block122Part013SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block122Part013] using hcert

def TailChunk000Sub001Block122Part014SupportExplicit : Finset ℕ :=
  ([13318] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block122Part014 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block122Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13318
    = surrogateDiagTailX0RatChunk000Sub001Block122Part014

theorem surrogateDiagonalTailChunk000Sub001Block122Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block122Part014CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block122Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block122Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block122Part014CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block122Part014SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block122Part014] using hcert

def TailChunk000Sub001Block122Part015SupportExplicit : Finset ℕ :=
  ([13319] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block122Part015 : ℚ :=
  (8789597767 : ℚ) / 2520977854752000000

def SurrogateDiagonalTailChunk000Sub001Block122Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13319
    = surrogateDiagTailX0RatChunk000Sub001Block122Part015

theorem surrogateDiagonalTailChunk000Sub001Block122Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block122Part015CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block122Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block122Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block122Part015CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block122Part015SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block122Part015] using hcert

def TailChunk000Sub001Block122Part016SupportExplicit : Finset ℕ :=
  ([13321] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block122Part016 : ℚ :=
  (2099341079 : ℚ) / 63027943100006400

def SurrogateDiagonalTailChunk000Sub001Block122Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13321
    = surrogateDiagTailX0RatChunk000Sub001Block122Part016

theorem surrogateDiagonalTailChunk000Sub001Block122Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block122Part016CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block122Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block122Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block122Part016CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block122Part016SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block122Part016] using hcert

def TailChunk000Sub001Block122Part017SupportExplicit : Finset ℕ :=
  ([13322] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block122Part017 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block122Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13322
    = surrogateDiagTailX0RatChunk000Sub001Block122Part017

theorem surrogateDiagonalTailChunk000Sub001Block122Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block122Part017CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block122Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block122Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block122Part017CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block122Part017SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block122Part017] using hcert

def TailChunk000Sub001Block122Part018SupportExplicit : Finset ℕ :=
  ([13323] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block122Part018 : ℚ :=
  (2465450153 : ℚ) / 31096300013199360

def SurrogateDiagonalTailChunk000Sub001Block122Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13323
    = surrogateDiagTailX0RatChunk000Sub001Block122Part018

theorem surrogateDiagonalTailChunk000Sub001Block122Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block122Part018CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block122Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block122Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block122Part018CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block122Part018SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block122Part018] using hcert

def TailChunk000Sub001Block122Part019SupportExplicit : Finset ℕ :=
  ([13326] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block122Part019 : ℚ :=
  (12331033859 : ℚ) / 19435187508249600

def SurrogateDiagonalTailChunk000Sub001Block122Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13326
    = surrogateDiagTailX0RatChunk000Sub001Block122Part019

theorem surrogateDiagonalTailChunk000Sub001Block122Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block122Part019CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block122Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block122Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block122Part019CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block122Part019SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block122Part019] using hcert

def TailChunk000Sub001Block122Part020SupportExplicit : Finset ℕ :=
  ([13327] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block122Part020 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block122Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13327
    = surrogateDiagTailX0RatChunk000Sub001Block122Part020

theorem surrogateDiagonalTailChunk000Sub001Block122Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block122Part020CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block122Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block122Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block122Part020CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block122Part020SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block122Part020] using hcert

def TailChunk000Sub001Block122Part021SupportExplicit : Finset ℕ :=
  ([13330] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block122Part021 : ℚ :=
  (7721324747 : ℚ) / 32268516540825600

def SurrogateDiagonalTailChunk000Sub001Block122Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13330
    = surrogateDiagTailX0RatChunk000Sub001Block122Part021

theorem surrogateDiagonalTailChunk000Sub001Block122Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block122Part021CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block122Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block122Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block122Part021CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block122Part021SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block122Part021] using hcert

def TailChunk000Sub001Block122Part022SupportExplicit : Finset ℕ :=
  ([13331] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block122Part022 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block122Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13331
    = surrogateDiagTailX0RatChunk000Sub001Block122Part022

theorem surrogateDiagonalTailChunk000Sub001Block122Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block122Part022CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block122Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block122Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block122Part022CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block122Part022SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block122Part022] using hcert

def TailChunk000Sub001Block122Part023SupportExplicit : Finset ℕ :=
  ([13333] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block122Part023 : ℚ :=
  (40842666875 : ℚ) / 36461402207083681344

def SurrogateDiagonalTailChunk000Sub001Block122Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13333
    = surrogateDiagTailX0RatChunk000Sub001Block122Part023

theorem surrogateDiagonalTailChunk000Sub001Block122Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block122Part023CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block122Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block122Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block122Part023CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block122Part023SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block122Part023] using hcert

def TailChunk000Sub001Block122Part024SupportExplicit : Finset ℕ :=
  ([13334] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block122Part024 : ℚ :=
  (96083740525 : ℚ) / 159020418647064576

def SurrogateDiagonalTailChunk000Sub001Block122Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13334
    = surrogateDiagTailX0RatChunk000Sub001Block122Part024

theorem surrogateDiagonalTailChunk000Sub001Block122Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block122Part024CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block122Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block122Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block122Part024CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block122Part024SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block122Part024] using hcert

def surrogateDiagonalTailChunk000Sub001Block122HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block122Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block122Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block122Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block122Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block122Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block122Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block122Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block122Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block122Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block122Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block122Head : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block122Part000
    + surrogateDiagTailX0RatChunk000Sub001Block122Part001
    + surrogateDiagTailX0RatChunk000Sub001Block122Part002
    + surrogateDiagTailX0RatChunk000Sub001Block122Part003
    + surrogateDiagTailX0RatChunk000Sub001Block122Part004
    + surrogateDiagTailX0RatChunk000Sub001Block122Part005
    + surrogateDiagTailX0RatChunk000Sub001Block122Part006
    + surrogateDiagTailX0RatChunk000Sub001Block122Part007
    + surrogateDiagTailX0RatChunk000Sub001Block122Part008
    + surrogateDiagTailX0RatChunk000Sub001Block122Part009

def surrogateDiagonalTailChunk000Sub001Block122MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block122Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block122Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block122Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block122Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block122Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block122Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block122Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block122Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block122Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block122Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block122Mid : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block122Part010
    + surrogateDiagTailX0RatChunk000Sub001Block122Part011
    + surrogateDiagTailX0RatChunk000Sub001Block122Part012
    + surrogateDiagTailX0RatChunk000Sub001Block122Part013
    + surrogateDiagTailX0RatChunk000Sub001Block122Part014
    + surrogateDiagTailX0RatChunk000Sub001Block122Part015
    + surrogateDiagTailX0RatChunk000Sub001Block122Part016
    + surrogateDiagTailX0RatChunk000Sub001Block122Part017
    + surrogateDiagTailX0RatChunk000Sub001Block122Part018
    + surrogateDiagTailX0RatChunk000Sub001Block122Part019

def surrogateDiagonalTailChunk000Sub001Block122TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block122Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block122Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block122Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block122Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block122Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block122Tail : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block122Part020
    + surrogateDiagTailX0RatChunk000Sub001Block122Part021
    + surrogateDiagTailX0RatChunk000Sub001Block122Part022
    + surrogateDiagTailX0RatChunk000Sub001Block122Part023
    + surrogateDiagTailX0RatChunk000Sub001Block122Part024

def surrogateDiagonalTailChunk000Sub001Block122Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub001Block122HeadSum X0
    + surrogateDiagonalTailChunk000Sub001Block122MidSum X0
    + surrogateDiagonalTailChunk000Sub001Block122TailSum X0

def surrogateDiagTailX0RatChunk000Sub001Block122 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block122Part000
    + surrogateDiagTailX0RatChunk000Sub001Block122Part001
    + surrogateDiagTailX0RatChunk000Sub001Block122Part002
    + surrogateDiagTailX0RatChunk000Sub001Block122Part003
    + surrogateDiagTailX0RatChunk000Sub001Block122Part004
    + surrogateDiagTailX0RatChunk000Sub001Block122Part005
    + surrogateDiagTailX0RatChunk000Sub001Block122Part006
    + surrogateDiagTailX0RatChunk000Sub001Block122Part007
    + surrogateDiagTailX0RatChunk000Sub001Block122Part008
    + surrogateDiagTailX0RatChunk000Sub001Block122Part009
    + surrogateDiagTailX0RatChunk000Sub001Block122Part010
    + surrogateDiagTailX0RatChunk000Sub001Block122Part011
    + surrogateDiagTailX0RatChunk000Sub001Block122Part012
    + surrogateDiagTailX0RatChunk000Sub001Block122Part013
    + surrogateDiagTailX0RatChunk000Sub001Block122Part014
    + surrogateDiagTailX0RatChunk000Sub001Block122Part015
    + surrogateDiagTailX0RatChunk000Sub001Block122Part016
    + surrogateDiagTailX0RatChunk000Sub001Block122Part017
    + surrogateDiagTailX0RatChunk000Sub001Block122Part018
    + surrogateDiagTailX0RatChunk000Sub001Block122Part019
    + surrogateDiagTailX0RatChunk000Sub001Block122Part020
    + surrogateDiagTailX0RatChunk000Sub001Block122Part021
    + surrogateDiagTailX0RatChunk000Sub001Block122Part022
    + surrogateDiagTailX0RatChunk000Sub001Block122Part023
    + surrogateDiagTailX0RatChunk000Sub001Block122Part024

theorem surrogateDiagTailX0RatChunk000Sub001Block122_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk000Sub001Block122Head + surrogateDiagTailX0RatChunk000Sub001Block122Mid + surrogateDiagTailX0RatChunk000Sub001Block122Tail =
      surrogateDiagTailX0RatChunk000Sub001Block122 := by
  unfold surrogateDiagTailX0RatChunk000Sub001Block122Head surrogateDiagTailX0RatChunk000Sub001Block122Mid surrogateDiagTailX0RatChunk000Sub001Block122Tail surrogateDiagTailX0RatChunk000Sub001Block122
  ring

def SurrogateDiagonalTailChunk000Sub001Block122HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block122HeadSum X0 = surrogateDiagTailX0RatChunk000Sub001Block122Head

def SurrogateDiagonalTailChunk000Sub001Block122MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block122MidSum X0 = surrogateDiagTailX0RatChunk000Sub001Block122Mid

def SurrogateDiagonalTailChunk000Sub001Block122TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block122TailSum X0 = surrogateDiagTailX0RatChunk000Sub001Block122Tail

theorem surrogateDiagonalTailChunk000Sub001Block122_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk000Sub001Block122HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk000Sub001Block122MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk000Sub001Block122TailCertificateAt X0) :
    surrogateDiagonalTailChunk000Sub001Block122Sum X0 = surrogateDiagTailX0RatChunk000Sub001Block122 := by
  unfold SurrogateDiagonalTailChunk000Sub001Block122HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk000Sub001Block122MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk000Sub001Block122TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk000Sub001Block122Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk000Sub001Block122_eq_head_add_mid_add_tail

/-- Block 123 covers tail-support indices [8075,8100) and q from 13335 to 13379. -/

def TailChunk000Sub001Block123Part000SupportExplicit : Finset ℕ :=
  ([13335] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block123Part000 : ℚ :=
  (1282984978525 : ℚ) / 3345599794952798208

def SurrogateDiagonalTailChunk000Sub001Block123Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13335
    = surrogateDiagTailX0RatChunk000Sub001Block123Part000

theorem surrogateDiagonalTailChunk000Sub001Block123Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block123Part000CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block123Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block123Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block123Part000CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block123Part000SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block123Part000] using hcert

def TailChunk000Sub001Block123Part001SupportExplicit : Finset ℕ :=
  ([13337] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block123Part001 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block123Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13337
    = surrogateDiagTailX0RatChunk000Sub001Block123Part001

theorem surrogateDiagonalTailChunk000Sub001Block123Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block123Part001CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block123Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block123Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block123Part001CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block123Part001SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block123Part001] using hcert

def TailChunk000Sub001Block123Part002SupportExplicit : Finset ℕ :=
  ([13339] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block123Part002 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block123Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13339
    = surrogateDiagTailX0RatChunk000Sub001Block123Part002

theorem surrogateDiagonalTailChunk000Sub001Block123Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block123Part002CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block123Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block123Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block123Part002CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block123Part002SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block123Part002] using hcert

def TailChunk000Sub001Block123Part003SupportExplicit : Finset ℕ :=
  ([13341] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block123Part003 : ℚ :=
  (618028663175 : ℚ) / 7816182286893724224

def SurrogateDiagonalTailChunk000Sub001Block123Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13341
    = surrogateDiagTailX0RatChunk000Sub001Block123Part003

theorem surrogateDiagonalTailChunk000Sub001Block123Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block123Part003CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block123Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block123Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block123Part003CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block123Part003SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block123Part003] using hcert

def TailChunk000Sub001Block123Part004SupportExplicit : Finset ℕ :=
  ([13342] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block123Part004 : ℚ :=
  (133414112375 : ℚ) / 156577996805013504

def SurrogateDiagonalTailChunk000Sub001Block123Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13342
    = surrogateDiagTailX0RatChunk000Sub001Block123Part004

theorem surrogateDiagonalTailChunk000Sub001Block123Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block123Part004CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block123Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block123Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block123Part004CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block123Part004SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block123Part004] using hcert

def TailChunk000Sub001Block123Part005SupportExplicit : Finset ℕ :=
  ([13343] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block123Part005 : ℚ :=
  (14805717541 : ℚ) / 2158228034431027200

def SurrogateDiagonalTailChunk000Sub001Block123Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13343
    = surrogateDiagTailX0RatChunk000Sub001Block123Part005

theorem surrogateDiagonalTailChunk000Sub001Block123Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block123Part005CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block123Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block123Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block123Part005CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block123Part005SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block123Part005] using hcert

def TailChunk000Sub001Block123Part006SupportExplicit : Finset ℕ :=
  ([13345] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block123Part006 : ℚ :=
  (1003864996525 : ℚ) / 24845351667281952768

def SurrogateDiagonalTailChunk000Sub001Block123Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13345
    = surrogateDiagTailX0RatChunk000Sub001Block123Part006

theorem surrogateDiagonalTailChunk000Sub001Block123Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block123Part006CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block123Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block123Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block123Part006CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block123Part006SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block123Part006] using hcert

def TailChunk000Sub001Block123Part007SupportExplicit : Finset ℕ :=
  ([13346] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block123Part007 : ℚ :=
  (695764515625 : ℚ) / 1238770966440517632

def SurrogateDiagonalTailChunk000Sub001Block123Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13346
    = surrogateDiagTailX0RatChunk000Sub001Block123Part007

theorem surrogateDiagonalTailChunk000Sub001Block123Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block123Part007CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block123Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block123Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block123Part007CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block123Part007SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block123Part007] using hcert

def TailChunk000Sub001Block123Part008SupportExplicit : Finset ℕ :=
  ([13349] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block123Part008 : ℚ :=
  (227944230875 : ℚ) / 21384221781850058304

def SurrogateDiagonalTailChunk000Sub001Block123Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13349
    = surrogateDiagTailX0RatChunk000Sub001Block123Part008

theorem surrogateDiagonalTailChunk000Sub001Block123Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block123Part008CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block123Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block123Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block123Part008CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block123Part008SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block123Part008] using hcert

def TailChunk000Sub001Block123Part009SupportExplicit : Finset ℕ :=
  ([13353] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block123Part009 : ℚ :=
  (990625061 : ℚ) / 12550957889640000

def SurrogateDiagonalTailChunk000Sub001Block123Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13353
    = surrogateDiagTailX0RatChunk000Sub001Block123Part009

theorem surrogateDiagonalTailChunk000Sub001Block123Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block123Part009CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block123Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block123Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block123Part009CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block123Part009SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block123Part009] using hcert

def TailChunk000Sub001Block123Part010SupportExplicit : Finset ℕ :=
  ([13354] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block123Part010 : ℚ :=
  (98378498851 : ℚ) / 134889252151939200

def SurrogateDiagonalTailChunk000Sub001Block123Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13354
    = surrogateDiagTailX0RatChunk000Sub001Block123Part010

theorem surrogateDiagonalTailChunk000Sub001Block123Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block123Part010CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block123Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block123Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block123Part010CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block123Part010SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block123Part010] using hcert

def TailChunk000Sub001Block123Part011SupportExplicit : Finset ℕ :=
  ([13355] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block123Part011 : ℚ :=
  (11895794683 : ℚ) / 433761104665958400

def SurrogateDiagonalTailChunk000Sub001Block123Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13355
    = surrogateDiagTailX0RatChunk000Sub001Block123Part011

theorem surrogateDiagonalTailChunk000Sub001Block123Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block123Part011CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block123Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block123Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block123Part011CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block123Part011SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block123Part011] using hcert

def TailChunk000Sub001Block123Part012SupportExplicit : Finset ℕ :=
  ([13358] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block123Part012 : ℚ :=
  (697016265625 : ℚ) / 1243232991521338482

def SurrogateDiagonalTailChunk000Sub001Block123Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13358
    = surrogateDiagTailX0RatChunk000Sub001Block123Part012

theorem surrogateDiagonalTailChunk000Sub001Block123Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block123Part012CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block123Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block123Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block123Part012CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block123Part012SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block123Part012] using hcert

def TailChunk000Sub001Block123Part013SupportExplicit : Finset ℕ :=
  ([13359] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block123Part013 : ℚ :=
  (49862903131 : ℚ) / 557367729271603200

def SurrogateDiagonalTailChunk000Sub001Block123Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13359
    = surrogateDiagTailX0RatChunk000Sub001Block123Part013

theorem surrogateDiagonalTailChunk000Sub001Block123Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block123Part013CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block123Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block123Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block123Part013CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block123Part013SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block123Part013] using hcert

def TailChunk000Sub001Block123Part014SupportExplicit : Finset ℕ :=
  ([13361] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block123Part014 : ℚ :=
  (908162189 : ℚ) / 461630442627000000

def SurrogateDiagonalTailChunk000Sub001Block123Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13361
    = surrogateDiagTailX0RatChunk000Sub001Block123Part014

theorem surrogateDiagonalTailChunk000Sub001Block123Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block123Part014CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block123Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block123Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block123Part014CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block123Part014SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block123Part014] using hcert

def TailChunk000Sub001Block123Part015SupportExplicit : Finset ℕ :=
  ([13362] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block123Part015 : ℚ :=
  (28700056643 : ℚ) / 14977184405913600

def SurrogateDiagonalTailChunk000Sub001Block123Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13362
    = surrogateDiagTailX0RatChunk000Sub001Block123Part015

theorem surrogateDiagonalTailChunk000Sub001Block123Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block123Part015CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block123Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block123Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block123Part015CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block123Part015SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block123Part015] using hcert

def TailChunk000Sub001Block123Part016SupportExplicit : Finset ℕ :=
  ([13363] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block123Part016 : ℚ :=
  (22425422975 : ℚ) / 953400757118059008

def SurrogateDiagonalTailChunk000Sub001Block123Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13363
    = surrogateDiagTailX0RatChunk000Sub001Block123Part016

theorem surrogateDiagonalTailChunk000Sub001Block123Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block123Part016CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block123Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block123Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block123Part016CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block123Part016SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block123Part016] using hcert

def TailChunk000Sub001Block123Part017SupportExplicit : Finset ℕ :=
  ([13366] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block123Part017 : ℚ :=
  (8955048647 : ℚ) / 14696219424153600

def SurrogateDiagonalTailChunk000Sub001Block123Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13366
    = surrogateDiagTailX0RatChunk000Sub001Block123Part017

theorem surrogateDiagonalTailChunk000Sub001Block123Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block123Part017CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block123Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block123Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block123Part017CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block123Part017SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block123Part017] using hcert

def TailChunk000Sub001Block123Part018SupportExplicit : Finset ℕ :=
  ([13367] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block123Part018 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block123Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13367
    = surrogateDiagTailX0RatChunk000Sub001Block123Part018

theorem surrogateDiagonalTailChunk000Sub001Block123Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block123Part018CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block123Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block123Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block123Part018CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block123Part018SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block123Part018] using hcert

def TailChunk000Sub001Block123Part019SupportExplicit : Finset ℕ :=
  ([13369] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block123Part019 : ℚ :=
  (2052202317 : ℚ) / 917548538058342400

def SurrogateDiagonalTailChunk000Sub001Block123Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13369
    = surrogateDiagTailX0RatChunk000Sub001Block123Part019

theorem surrogateDiagonalTailChunk000Sub001Block123Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block123Part019CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block123Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block123Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block123Part019CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block123Part019SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block123Part019] using hcert

def TailChunk000Sub001Block123Part020SupportExplicit : Finset ℕ :=
  ([13370] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block123Part020 : ℚ :=
  (13888502129 : ℚ) / 8649205514403840

def SurrogateDiagonalTailChunk000Sub001Block123Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13370
    = surrogateDiagTailX0RatChunk000Sub001Block123Part020

theorem surrogateDiagonalTailChunk000Sub001Block123Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block123Part020CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block123Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block123Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block123Part020CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block123Part020SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block123Part020] using hcert

def TailChunk000Sub001Block123Part021SupportExplicit : Finset ℕ :=
  ([13371] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block123Part021 : ℚ :=
  (310405269025 : ℚ) / 3943370460749832192

def SurrogateDiagonalTailChunk000Sub001Block123Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13371
    = surrogateDiagTailX0RatChunk000Sub001Block123Part021

theorem surrogateDiagonalTailChunk000Sub001Block123Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block123Part021CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block123Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block123Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block123Part021CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block123Part021SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block123Part021] using hcert

def TailChunk000Sub001Block123Part022SupportExplicit : Finset ℕ :=
  ([13373] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block123Part022 : ℚ :=
  (436048441 : ℚ) / 287429134493632320

def SurrogateDiagonalTailChunk000Sub001Block123Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13373
    = surrogateDiagTailX0RatChunk000Sub001Block123Part022

theorem surrogateDiagonalTailChunk000Sub001Block123Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block123Part022CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block123Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block123Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block123Part022CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block123Part022SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block123Part022] using hcert

def TailChunk000Sub001Block123Part023SupportExplicit : Finset ℕ :=
  ([13378] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block123Part023 : ℚ :=
  (699105015625 : ℚ) / 1250696473445793792

def SurrogateDiagonalTailChunk000Sub001Block123Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13378
    = surrogateDiagTailX0RatChunk000Sub001Block123Part023

theorem surrogateDiagonalTailChunk000Sub001Block123Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block123Part023CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block123Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block123Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block123Part023CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block123Part023SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block123Part023] using hcert

def TailChunk000Sub001Block123Part024SupportExplicit : Finset ℕ :=
  ([13379] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block123Part024 : ℚ :=
  (13135571375 : ℚ) / 3474757240563695616

def SurrogateDiagonalTailChunk000Sub001Block123Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13379
    = surrogateDiagTailX0RatChunk000Sub001Block123Part024

theorem surrogateDiagonalTailChunk000Sub001Block123Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block123Part024CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block123Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block123Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block123Part024CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block123Part024SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block123Part024] using hcert

def surrogateDiagonalTailChunk000Sub001Block123HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block123Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block123Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block123Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block123Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block123Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block123Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block123Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block123Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block123Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block123Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block123Head : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block123Part000
    + surrogateDiagTailX0RatChunk000Sub001Block123Part001
    + surrogateDiagTailX0RatChunk000Sub001Block123Part002
    + surrogateDiagTailX0RatChunk000Sub001Block123Part003
    + surrogateDiagTailX0RatChunk000Sub001Block123Part004
    + surrogateDiagTailX0RatChunk000Sub001Block123Part005
    + surrogateDiagTailX0RatChunk000Sub001Block123Part006
    + surrogateDiagTailX0RatChunk000Sub001Block123Part007
    + surrogateDiagTailX0RatChunk000Sub001Block123Part008
    + surrogateDiagTailX0RatChunk000Sub001Block123Part009

def surrogateDiagonalTailChunk000Sub001Block123MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block123Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block123Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block123Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block123Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block123Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block123Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block123Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block123Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block123Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block123Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block123Mid : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block123Part010
    + surrogateDiagTailX0RatChunk000Sub001Block123Part011
    + surrogateDiagTailX0RatChunk000Sub001Block123Part012
    + surrogateDiagTailX0RatChunk000Sub001Block123Part013
    + surrogateDiagTailX0RatChunk000Sub001Block123Part014
    + surrogateDiagTailX0RatChunk000Sub001Block123Part015
    + surrogateDiagTailX0RatChunk000Sub001Block123Part016
    + surrogateDiagTailX0RatChunk000Sub001Block123Part017
    + surrogateDiagTailX0RatChunk000Sub001Block123Part018
    + surrogateDiagTailX0RatChunk000Sub001Block123Part019

def surrogateDiagonalTailChunk000Sub001Block123TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block123Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block123Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block123Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block123Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block123Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block123Tail : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block123Part020
    + surrogateDiagTailX0RatChunk000Sub001Block123Part021
    + surrogateDiagTailX0RatChunk000Sub001Block123Part022
    + surrogateDiagTailX0RatChunk000Sub001Block123Part023
    + surrogateDiagTailX0RatChunk000Sub001Block123Part024

def surrogateDiagonalTailChunk000Sub001Block123Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub001Block123HeadSum X0
    + surrogateDiagonalTailChunk000Sub001Block123MidSum X0
    + surrogateDiagonalTailChunk000Sub001Block123TailSum X0

def surrogateDiagTailX0RatChunk000Sub001Block123 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block123Part000
    + surrogateDiagTailX0RatChunk000Sub001Block123Part001
    + surrogateDiagTailX0RatChunk000Sub001Block123Part002
    + surrogateDiagTailX0RatChunk000Sub001Block123Part003
    + surrogateDiagTailX0RatChunk000Sub001Block123Part004
    + surrogateDiagTailX0RatChunk000Sub001Block123Part005
    + surrogateDiagTailX0RatChunk000Sub001Block123Part006
    + surrogateDiagTailX0RatChunk000Sub001Block123Part007
    + surrogateDiagTailX0RatChunk000Sub001Block123Part008
    + surrogateDiagTailX0RatChunk000Sub001Block123Part009
    + surrogateDiagTailX0RatChunk000Sub001Block123Part010
    + surrogateDiagTailX0RatChunk000Sub001Block123Part011
    + surrogateDiagTailX0RatChunk000Sub001Block123Part012
    + surrogateDiagTailX0RatChunk000Sub001Block123Part013
    + surrogateDiagTailX0RatChunk000Sub001Block123Part014
    + surrogateDiagTailX0RatChunk000Sub001Block123Part015
    + surrogateDiagTailX0RatChunk000Sub001Block123Part016
    + surrogateDiagTailX0RatChunk000Sub001Block123Part017
    + surrogateDiagTailX0RatChunk000Sub001Block123Part018
    + surrogateDiagTailX0RatChunk000Sub001Block123Part019
    + surrogateDiagTailX0RatChunk000Sub001Block123Part020
    + surrogateDiagTailX0RatChunk000Sub001Block123Part021
    + surrogateDiagTailX0RatChunk000Sub001Block123Part022
    + surrogateDiagTailX0RatChunk000Sub001Block123Part023
    + surrogateDiagTailX0RatChunk000Sub001Block123Part024

theorem surrogateDiagTailX0RatChunk000Sub001Block123_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk000Sub001Block123Head + surrogateDiagTailX0RatChunk000Sub001Block123Mid + surrogateDiagTailX0RatChunk000Sub001Block123Tail =
      surrogateDiagTailX0RatChunk000Sub001Block123 := by
  unfold surrogateDiagTailX0RatChunk000Sub001Block123Head surrogateDiagTailX0RatChunk000Sub001Block123Mid surrogateDiagTailX0RatChunk000Sub001Block123Tail surrogateDiagTailX0RatChunk000Sub001Block123
  ring

def SurrogateDiagonalTailChunk000Sub001Block123HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block123HeadSum X0 = surrogateDiagTailX0RatChunk000Sub001Block123Head

def SurrogateDiagonalTailChunk000Sub001Block123MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block123MidSum X0 = surrogateDiagTailX0RatChunk000Sub001Block123Mid

def SurrogateDiagonalTailChunk000Sub001Block123TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block123TailSum X0 = surrogateDiagTailX0RatChunk000Sub001Block123Tail

theorem surrogateDiagonalTailChunk000Sub001Block123_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk000Sub001Block123HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk000Sub001Block123MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk000Sub001Block123TailCertificateAt X0) :
    surrogateDiagonalTailChunk000Sub001Block123Sum X0 = surrogateDiagTailX0RatChunk000Sub001Block123 := by
  unfold SurrogateDiagonalTailChunk000Sub001Block123HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk000Sub001Block123MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk000Sub001Block123TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk000Sub001Block123Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk000Sub001Block123_eq_head_add_mid_add_tail

/-- Block 124 covers tail-support indices [8100,8125) and q from 13381 to 13417. -/

def TailChunk000Sub001Block124Part000SupportExplicit : Finset ℕ :=
  ([13381] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block124Part000 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block124Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13381
    = surrogateDiagTailX0RatChunk000Sub001Block124Part000

theorem surrogateDiagonalTailChunk000Sub001Block124Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block124Part000CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block124Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block124Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block124Part000CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block124Part000SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block124Part000] using hcert

def TailChunk000Sub001Block124Part001SupportExplicit : Finset ℕ :=
  ([13382] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block124Part001 : ℚ :=
  (1119237025 : ℚ) / 2003509108907442

def SurrogateDiagonalTailChunk000Sub001Block124Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13382
    = surrogateDiagTailX0RatChunk000Sub001Block124Part001

theorem surrogateDiagonalTailChunk000Sub001Block124Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block124Part001CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block124Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block124Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block124Part001CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block124Part001SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block124Part001] using hcert

def TailChunk000Sub001Block124Part002SupportExplicit : Finset ℕ :=
  ([13385] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block124Part002 : ℚ :=
  (298731099175 : ℚ) / 10941831080113176576

def SurrogateDiagonalTailChunk000Sub001Block124Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13385
    = surrogateDiagTailX0RatChunk000Sub001Block124Part002

theorem surrogateDiagonalTailChunk000Sub001Block124Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block124Part002CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block124Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block124Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block124Part002CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block124Part002SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block124Part002] using hcert

def TailChunk000Sub001Block124Part003SupportExplicit : Finset ℕ :=
  ([13386] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block124Part003 : ℚ :=
  (1464130628875 : ℚ) / 796017282659647488

def SurrogateDiagonalTailChunk000Sub001Block124Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13386
    = surrogateDiagTailX0RatChunk000Sub001Block124Part003

theorem surrogateDiagonalTailChunk000Sub001Block124Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block124Part003CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block124Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block124Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block124Part003CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block124Part003SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block124Part003] using hcert

def TailChunk000Sub001Block124Part004SupportExplicit : Finset ℕ :=
  ([13387] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block124Part004 : ℚ :=
  (4967593047 : ℚ) / 728953617016422400

def SurrogateDiagonalTailChunk000Sub001Block124Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13387
    = surrogateDiagTailX0RatChunk000Sub001Block124Part004

theorem surrogateDiagonalTailChunk000Sub001Block124Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block124Part004CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block124Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block124Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block124Part004CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block124Part004SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block124Part004] using hcert

def TailChunk000Sub001Block124Part005SupportExplicit : Finset ℕ :=
  ([13389] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block124Part005 : ℚ :=
  (622482662975 : ℚ) / 7929304751624276544

def SurrogateDiagonalTailChunk000Sub001Block124Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13389
    = surrogateDiagTailX0RatChunk000Sub001Block124Part005

theorem surrogateDiagonalTailChunk000Sub001Block124Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block124Part005CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block124Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block124Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block124Part005CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block124Part005SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block124Part005] using hcert

def TailChunk000Sub001Block124Part006SupportExplicit : Finset ℕ :=
  ([13390] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block124Part006 : ℚ :=
  (106148734175 : ℚ) / 79821519404138496

def SurrogateDiagonalTailChunk000Sub001Block124Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13390
    = surrogateDiagTailX0RatChunk000Sub001Block124Part006

theorem surrogateDiagonalTailChunk000Sub001Block124Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block124Part006CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block124Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block124Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block124Part006CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block124Part006SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block124Part006] using hcert

def TailChunk000Sub001Block124Part007SupportExplicit : Finset ℕ :=
  ([13391] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block124Part007 : ℚ :=
  (229375694675 : ℚ) / 21654762079927025664

def SurrogateDiagonalTailChunk000Sub001Block124Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13391
    = surrogateDiagTailX0RatChunk000Sub001Block124Part007

theorem surrogateDiagonalTailChunk000Sub001Block124Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block124Part007CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block124Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block124Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block124Part007CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block124Part007SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block124Part007] using hcert

def TailChunk000Sub001Block124Part008SupportExplicit : Finset ℕ :=
  ([13393] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block124Part008 : ℚ :=
  (88110805525 : ℚ) / 73819753341150776448

def SurrogateDiagonalTailChunk000Sub001Block124Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13393
    = surrogateDiagTailX0RatChunk000Sub001Block124Part008

theorem surrogateDiagonalTailChunk000Sub001Block124Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block124Part008CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block124Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block124Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block124Part008CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block124Part008SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block124Part008] using hcert

def TailChunk000Sub001Block124Part009SupportExplicit : Finset ℕ :=
  ([13394] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block124Part009 : ℚ :=
  (3986275657 : ℚ) / 6531653077401600

def SurrogateDiagonalTailChunk000Sub001Block124Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13394
    = surrogateDiagTailX0RatChunk000Sub001Block124Part009

theorem surrogateDiagonalTailChunk000Sub001Block124Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block124Part009CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block124Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block124Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block124Part009CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block124Part009SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block124Part009] using hcert

def TailChunk000Sub001Block124Part010SupportExplicit : Finset ℕ :=
  ([13395] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block124Part010 : ℚ :=
  (1948159561675 : ℚ) / 4814022923675762688

def SurrogateDiagonalTailChunk000Sub001Block124Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13395
    = surrogateDiagTailX0RatChunk000Sub001Block124Part010

theorem surrogateDiagonalTailChunk000Sub001Block124Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block124Part010CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block124Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block124Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block124Part010CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block124Part010SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block124Part010] using hcert

def TailChunk000Sub001Block124Part011SupportExplicit : Finset ℕ :=
  ([13397] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block124Part011 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block124Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13397
    = surrogateDiagTailX0RatChunk000Sub001Block124Part011

theorem surrogateDiagonalTailChunk000Sub001Block124Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block124Part011CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block124Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block124Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block124Part011CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block124Part011SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block124Part011] using hcert

def TailChunk000Sub001Block124Part012SupportExplicit : Finset ℕ :=
  ([13398] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block124Part012 : ℚ :=
  (26092319879 : ℚ) / 6374027958681600

def SurrogateDiagonalTailChunk000Sub001Block124Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13398
    = surrogateDiagTailX0RatChunk000Sub001Block124Part012

theorem surrogateDiagonalTailChunk000Sub001Block124Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block124Part012CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block124Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block124Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block124Part012CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block124Part012SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block124Part012] using hcert

def TailChunk000Sub001Block124Part013SupportExplicit : Finset ℕ :=
  ([13399] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block124Part013 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block124Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13399
    = surrogateDiagTailX0RatChunk000Sub001Block124Part013

theorem surrogateDiagonalTailChunk000Sub001Block124Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block124Part013CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block124Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block124Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block124Part013CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block124Part013SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block124Part013] using hcert

def TailChunk000Sub001Block124Part014SupportExplicit : Finset ℕ :=
  ([13402] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block124Part014 : ℚ :=
  (44903401 : ℚ) / 80620604896800

def SurrogateDiagonalTailChunk000Sub001Block124Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13402
    = surrogateDiagTailX0RatChunk000Sub001Block124Part014

theorem surrogateDiagonalTailChunk000Sub001Block124Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block124Part014CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block124Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block124Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block124Part014CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block124Part014SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block124Part014] using hcert

def TailChunk000Sub001Block124Part015SupportExplicit : Finset ℕ :=
  ([13403] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block124Part015 : ℚ :=
  (2680150427 : ℚ) / 466864367885936640

def SurrogateDiagonalTailChunk000Sub001Block124Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13403
    = surrogateDiagTailX0RatChunk000Sub001Block124Part015

theorem surrogateDiagonalTailChunk000Sub001Block124Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block124Part015CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block124Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block124Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block124Part015CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block124Part015SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block124Part015] using hcert

def TailChunk000Sub001Block124Part016SupportExplicit : Finset ℕ :=
  ([13405] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block124Part016 : ℚ :=
  (519035842025 : ℚ) / 8832736643272556544

def SurrogateDiagonalTailChunk000Sub001Block124Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13405
    = surrogateDiagTailX0RatChunk000Sub001Block124Part016

theorem surrogateDiagonalTailChunk000Sub001Block124Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block124Part016CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block124Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block124Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block124Part016CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block124Part016SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block124Part016] using hcert

def TailChunk000Sub001Block124Part017SupportExplicit : Finset ℕ :=
  ([13406] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block124Part017 : ℚ :=
  (702034515625 : ℚ) / 1261201740894206802

def SurrogateDiagonalTailChunk000Sub001Block124Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13406
    = surrogateDiagTailX0RatChunk000Sub001Block124Part017

theorem surrogateDiagonalTailChunk000Sub001Block124Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block124Part017CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block124Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block124Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block124Part017CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block124Part017SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block124Part017] using hcert

def TailChunk000Sub001Block124Part018SupportExplicit : Finset ℕ :=
  ([13407] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block124Part018 : ℚ :=
  (96872540779 : ℚ) / 557367729271603200

def SurrogateDiagonalTailChunk000Sub001Block124Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13407
    = surrogateDiagTailX0RatChunk000Sub001Block124Part018

theorem surrogateDiagonalTailChunk000Sub001Block124Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block124Part018CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block124Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block124Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block124Part018CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block124Part018SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block124Part018] using hcert

def TailChunk000Sub001Block124Part019SupportExplicit : Finset ℕ :=
  ([13409] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block124Part019 : ℚ :=
  (22487600071 : ℚ) / 1713132475679539200

def SurrogateDiagonalTailChunk000Sub001Block124Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13409
    = surrogateDiagTailX0RatChunk000Sub001Block124Part019

theorem surrogateDiagonalTailChunk000Sub001Block124Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block124Part019CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block124Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block124Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block124Part019CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block124Part019SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block124Part019] using hcert

def TailChunk000Sub001Block124Part020SupportExplicit : Finset ℕ :=
  ([13411] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block124Part020 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block124Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13411
    = surrogateDiagTailX0RatChunk000Sub001Block124Part020

theorem surrogateDiagonalTailChunk000Sub001Block124Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block124Part020CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block124Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block124Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block124Part020CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block124Part020SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block124Part020] using hcert

def TailChunk000Sub001Block124Part021SupportExplicit : Finset ℕ :=
  ([13413] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block124Part021 : ℚ :=
  (1275544682725 : ℚ) / 12354692410893139968

def SurrogateDiagonalTailChunk000Sub001Block124Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13413
    = surrogateDiagTailX0RatChunk000Sub001Block124Part021

theorem surrogateDiagonalTailChunk000Sub001Block124Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block124Part021CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block124Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block124Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block124Part021CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block124Part021SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block124Part021] using hcert

def TailChunk000Sub001Block124Part022SupportExplicit : Finset ℕ :=
  ([13414] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block124Part022 : ℚ :=
  (1307906380625 : ℚ) / 2014918746732232704

def SurrogateDiagonalTailChunk000Sub001Block124Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13414
    = surrogateDiagTailX0RatChunk000Sub001Block124Part022

theorem surrogateDiagonalTailChunk000Sub001Block124Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block124Part022CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block124Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block124Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block124Part022CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block124Part022SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block124Part022] using hcert

def TailChunk000Sub001Block124Part023SupportExplicit : Finset ℕ :=
  ([13415] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block124Part023 : ℚ :=
  (300070330675 : ℚ) / 11040294631669733376

def SurrogateDiagonalTailChunk000Sub001Block124Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13415
    = surrogateDiagTailX0RatChunk000Sub001Block124Part023

theorem surrogateDiagonalTailChunk000Sub001Block124Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block124Part023CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block124Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block124Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block124Part023CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block124Part023SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block124Part023] using hcert

def TailChunk000Sub001Block124Part024SupportExplicit : Finset ℕ :=
  ([13417] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block124Part024 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block124Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13417
    = surrogateDiagTailX0RatChunk000Sub001Block124Part024

theorem surrogateDiagonalTailChunk000Sub001Block124Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block124Part024CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block124Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block124Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block124Part024CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block124Part024SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block124Part024] using hcert

def surrogateDiagonalTailChunk000Sub001Block124HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block124Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block124Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block124Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block124Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block124Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block124Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block124Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block124Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block124Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block124Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block124Head : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block124Part000
    + surrogateDiagTailX0RatChunk000Sub001Block124Part001
    + surrogateDiagTailX0RatChunk000Sub001Block124Part002
    + surrogateDiagTailX0RatChunk000Sub001Block124Part003
    + surrogateDiagTailX0RatChunk000Sub001Block124Part004
    + surrogateDiagTailX0RatChunk000Sub001Block124Part005
    + surrogateDiagTailX0RatChunk000Sub001Block124Part006
    + surrogateDiagTailX0RatChunk000Sub001Block124Part007
    + surrogateDiagTailX0RatChunk000Sub001Block124Part008
    + surrogateDiagTailX0RatChunk000Sub001Block124Part009

def surrogateDiagonalTailChunk000Sub001Block124MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block124Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block124Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block124Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block124Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block124Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block124Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block124Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block124Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block124Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block124Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block124Mid : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block124Part010
    + surrogateDiagTailX0RatChunk000Sub001Block124Part011
    + surrogateDiagTailX0RatChunk000Sub001Block124Part012
    + surrogateDiagTailX0RatChunk000Sub001Block124Part013
    + surrogateDiagTailX0RatChunk000Sub001Block124Part014
    + surrogateDiagTailX0RatChunk000Sub001Block124Part015
    + surrogateDiagTailX0RatChunk000Sub001Block124Part016
    + surrogateDiagTailX0RatChunk000Sub001Block124Part017
    + surrogateDiagTailX0RatChunk000Sub001Block124Part018
    + surrogateDiagTailX0RatChunk000Sub001Block124Part019

def surrogateDiagonalTailChunk000Sub001Block124TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block124Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block124Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block124Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block124Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block124Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block124Tail : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block124Part020
    + surrogateDiagTailX0RatChunk000Sub001Block124Part021
    + surrogateDiagTailX0RatChunk000Sub001Block124Part022
    + surrogateDiagTailX0RatChunk000Sub001Block124Part023
    + surrogateDiagTailX0RatChunk000Sub001Block124Part024

def surrogateDiagonalTailChunk000Sub001Block124Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub001Block124HeadSum X0
    + surrogateDiagonalTailChunk000Sub001Block124MidSum X0
    + surrogateDiagonalTailChunk000Sub001Block124TailSum X0

def surrogateDiagTailX0RatChunk000Sub001Block124 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block124Part000
    + surrogateDiagTailX0RatChunk000Sub001Block124Part001
    + surrogateDiagTailX0RatChunk000Sub001Block124Part002
    + surrogateDiagTailX0RatChunk000Sub001Block124Part003
    + surrogateDiagTailX0RatChunk000Sub001Block124Part004
    + surrogateDiagTailX0RatChunk000Sub001Block124Part005
    + surrogateDiagTailX0RatChunk000Sub001Block124Part006
    + surrogateDiagTailX0RatChunk000Sub001Block124Part007
    + surrogateDiagTailX0RatChunk000Sub001Block124Part008
    + surrogateDiagTailX0RatChunk000Sub001Block124Part009
    + surrogateDiagTailX0RatChunk000Sub001Block124Part010
    + surrogateDiagTailX0RatChunk000Sub001Block124Part011
    + surrogateDiagTailX0RatChunk000Sub001Block124Part012
    + surrogateDiagTailX0RatChunk000Sub001Block124Part013
    + surrogateDiagTailX0RatChunk000Sub001Block124Part014
    + surrogateDiagTailX0RatChunk000Sub001Block124Part015
    + surrogateDiagTailX0RatChunk000Sub001Block124Part016
    + surrogateDiagTailX0RatChunk000Sub001Block124Part017
    + surrogateDiagTailX0RatChunk000Sub001Block124Part018
    + surrogateDiagTailX0RatChunk000Sub001Block124Part019
    + surrogateDiagTailX0RatChunk000Sub001Block124Part020
    + surrogateDiagTailX0RatChunk000Sub001Block124Part021
    + surrogateDiagTailX0RatChunk000Sub001Block124Part022
    + surrogateDiagTailX0RatChunk000Sub001Block124Part023
    + surrogateDiagTailX0RatChunk000Sub001Block124Part024

theorem surrogateDiagTailX0RatChunk000Sub001Block124_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk000Sub001Block124Head + surrogateDiagTailX0RatChunk000Sub001Block124Mid + surrogateDiagTailX0RatChunk000Sub001Block124Tail =
      surrogateDiagTailX0RatChunk000Sub001Block124 := by
  unfold surrogateDiagTailX0RatChunk000Sub001Block124Head surrogateDiagTailX0RatChunk000Sub001Block124Mid surrogateDiagTailX0RatChunk000Sub001Block124Tail surrogateDiagTailX0RatChunk000Sub001Block124
  ring

def SurrogateDiagonalTailChunk000Sub001Block124HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block124HeadSum X0 = surrogateDiagTailX0RatChunk000Sub001Block124Head

def SurrogateDiagonalTailChunk000Sub001Block124MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block124MidSum X0 = surrogateDiagTailX0RatChunk000Sub001Block124Mid

def SurrogateDiagonalTailChunk000Sub001Block124TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block124TailSum X0 = surrogateDiagTailX0RatChunk000Sub001Block124Tail

theorem surrogateDiagonalTailChunk000Sub001Block124_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk000Sub001Block124HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk000Sub001Block124MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk000Sub001Block124TailCertificateAt X0) :
    surrogateDiagonalTailChunk000Sub001Block124Sum X0 = surrogateDiagTailX0RatChunk000Sub001Block124 := by
  unfold SurrogateDiagonalTailChunk000Sub001Block124HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk000Sub001Block124MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk000Sub001Block124TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk000Sub001Block124Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk000Sub001Block124_eq_head_add_mid_add_tail

/-- Block 125 covers tail-support indices [8125,8150) and q from 13418 to 13462. -/

def TailChunk000Sub001Block125Part000SupportExplicit : Finset ℕ :=
  ([13418] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block125Part000 : ℚ :=
  (703291890625 : ℚ) / 1265724198899495712

def SurrogateDiagonalTailChunk000Sub001Block125Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13418
    = surrogateDiagTailX0RatChunk000Sub001Block125Part000

theorem surrogateDiagonalTailChunk000Sub001Block125Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block125Part000CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block125Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block125Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block125Part000CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block125Part000SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block125Part000] using hcert

def TailChunk000Sub001Block125Part001SupportExplicit : Finset ℕ :=
  ([13421] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block125Part001 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block125Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13421
    = surrogateDiagTailX0RatChunk000Sub001Block125Part001

theorem surrogateDiagonalTailChunk000Sub001Block125Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block125Part001CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block125Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block125Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block125Part001CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block125Part001SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block125Part001] using hcert

def TailChunk000Sub001Block125Part002SupportExplicit : Finset ℕ :=
  ([13422] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block125Part002 : ℚ :=
  (781639933175 : ℚ) / 500039189688689664

def SurrogateDiagonalTailChunk000Sub001Block125Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13422
    = surrogateDiagTailX0RatChunk000Sub001Block125Part002

theorem surrogateDiagonalTailChunk000Sub001Block125Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block125Part002CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block125Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block125Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block125Part002CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block125Part002SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block125Part002] using hcert

def TailChunk000Sub001Block125Part003SupportExplicit : Finset ℕ :=
  ([13423] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block125Part003 : ℚ :=
  (596078731 : ℚ) / 282167412943749120

def SurrogateDiagonalTailChunk000Sub001Block125Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13423
    = surrogateDiagTailX0RatChunk000Sub001Block125Part003

theorem surrogateDiagonalTailChunk000Sub001Block125Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block125Part003CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block125Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block125Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block125Part003CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block125Part003SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block125Part003] using hcert

def TailChunk000Sub001Block125Part004SupportExplicit : Finset ℕ :=
  ([13427] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block125Part004 : ℚ :=
  (14107308125 : ℚ) / 6365524607007971328

def SurrogateDiagonalTailChunk000Sub001Block125Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13427
    = surrogateDiagTailX0RatChunk000Sub001Block125Part004

theorem surrogateDiagonalTailChunk000Sub001Block125Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block125Part004CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block125Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block125Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block125Part004CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block125Part004SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block125Part004] using hcert

def TailChunk000Sub001Block125Part005SupportExplicit : Finset ℕ :=
  ([13429] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block125Part005 : ℚ :=
  (134924710325 : ℚ) / 29406317132738985984

def SurrogateDiagonalTailChunk000Sub001Block125Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13429
    = surrogateDiagTailX0RatChunk000Sub001Block125Part005

theorem surrogateDiagonalTailChunk000Sub001Block125Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block125Part005CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block125Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block125Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block125Part005CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block125Part005SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block125Part005] using hcert

def TailChunk000Sub001Block125Part006SupportExplicit : Finset ℕ :=
  ([13430] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block125Part006 : ℚ :=
  (1960512982825 : ℚ) / 1552834479205122048

def SurrogateDiagonalTailChunk000Sub001Block125Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13430
    = surrogateDiagTailX0RatChunk000Sub001Block125Part006

theorem surrogateDiagonalTailChunk000Sub001Block125Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block125Part006CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block125Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block125Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block125Part006CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block125Part006SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block125Part006] using hcert

def TailChunk000Sub001Block125Part007SupportExplicit : Finset ℕ :=
  ([13433] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block125Part007 : ℚ :=
  (685852157 : ℚ) / 28349188704000000

def SurrogateDiagonalTailChunk000Sub001Block125Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13433
    = surrogateDiagTailX0RatChunk000Sub001Block125Part007

theorem surrogateDiagonalTailChunk000Sub001Block125Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block125Part007CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block125Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block125Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block125Part007CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block125Part007SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block125Part007] using hcert

def TailChunk000Sub001Block125Part008SupportExplicit : Finset ℕ :=
  ([13434] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block125Part008 : ℚ :=
  (391519140925 : ℚ) / 250915320216797472

def SurrogateDiagonalTailChunk000Sub001Block125Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13434
    = surrogateDiagTailX0RatChunk000Sub001Block125Part008

theorem surrogateDiagonalTailChunk000Sub001Block125Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block125Part008CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block125Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block125Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block125Part008CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block125Part008SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block125Part008] using hcert

def TailChunk000Sub001Block125Part009SupportExplicit : Finset ℕ :=
  ([13435] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block125Part009 : ℚ :=
  (150721033875 : ℚ) / 11106305178091657216

def SurrogateDiagonalTailChunk000Sub001Block125Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13435
    = surrogateDiagTailX0RatChunk000Sub001Block125Part009

theorem surrogateDiagonalTailChunk000Sub001Block125Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block125Part009CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block125Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block125Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block125Part009CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block125Part009SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block125Part009] using hcert

def TailChunk000Sub001Block125Part010SupportExplicit : Finset ℕ :=
  ([13438] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block125Part010 : ℚ :=
  (705390015625 : ℚ) / 1273288643408930322

def SurrogateDiagonalTailChunk000Sub001Block125Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13438
    = surrogateDiagTailX0RatChunk000Sub001Block125Part010

theorem surrogateDiagonalTailChunk000Sub001Block125Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block125Part010CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block125Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block125Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block125Part010CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block125Part010SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block125Part010] using hcert

def TailChunk000Sub001Block125Part011SupportExplicit : Finset ℕ :=
  ([13439] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block125Part011 : ℚ :=
  (328873933 : ℚ) / 337396105728000000

def SurrogateDiagonalTailChunk000Sub001Block125Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13439
    = surrogateDiagTailX0RatChunk000Sub001Block125Part011

theorem surrogateDiagonalTailChunk000Sub001Block125Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block125Part011CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block125Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block125Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block125Part011CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block125Part011SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block125Part011] using hcert

def TailChunk000Sub001Block125Part012SupportExplicit : Finset ℕ :=
  ([13441] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block125Part012 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block125Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13441
    = surrogateDiagTailX0RatChunk000Sub001Block125Part012

theorem surrogateDiagonalTailChunk000Sub001Block125Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block125Part012CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block125Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block125Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block125Part012CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block125Part012SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block125Part012] using hcert

def TailChunk000Sub001Block125Part013SupportExplicit : Finset ℕ :=
  ([13442] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block125Part013 : ℚ :=
  (5846156977 : ℚ) / 6190873101434880

def SurrogateDiagonalTailChunk000Sub001Block125Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13442
    = surrogateDiagTailX0RatChunk000Sub001Block125Part013

theorem surrogateDiagonalTailChunk000Sub001Block125Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block125Part013CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block125Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block125Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block125Part013CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block125Part013SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block125Part013] using hcert

def TailChunk000Sub001Block125Part014SupportExplicit : Finset ℕ :=
  ([13443] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block125Part014 : ℚ :=
  (358578593 : ℚ) / 4604588804014080

def SurrogateDiagonalTailChunk000Sub001Block125Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13443
    = surrogateDiagTailX0RatChunk000Sub001Block125Part014

theorem surrogateDiagonalTailChunk000Sub001Block125Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block125Part014CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block125Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block125Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block125Part014CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block125Part014SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block125Part014] using hcert

def TailChunk000Sub001Block125Part015SupportExplicit : Finset ℕ :=
  ([13445] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block125Part015 : ℚ :=
  (301412561575 : ℚ) / 11139421234670862336

def SurrogateDiagonalTailChunk000Sub001Block125Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13445
    = surrogateDiagTailX0RatChunk000Sub001Block125Part015

theorem surrogateDiagonalTailChunk000Sub001Block125Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block125Part015CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block125Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block125Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block125Part015CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block125Part015SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block125Part015] using hcert

def TailChunk000Sub001Block125Part016SupportExplicit : Finset ℕ :=
  ([13447] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block125Part016 : ℚ :=
  (629672664625 : ℚ) / 33418263704012587008

def SurrogateDiagonalTailChunk000Sub001Block125Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13447
    = surrogateDiagTailX0RatChunk000Sub001Block125Part016

theorem surrogateDiagonalTailChunk000Sub001Block125Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block125Part016CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block125Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block125Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block125Part016CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block125Part016SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block125Part016] using hcert

def TailChunk000Sub001Block125Part017SupportExplicit : Finset ℕ :=
  ([13449] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block125Part017 : ℚ :=
  (628072662725 : ℚ) / 8072429385624035904

def SurrogateDiagonalTailChunk000Sub001Block125Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13449
    = surrogateDiagTailX0RatChunk000Sub001Block125Part017

theorem surrogateDiagonalTailChunk000Sub001Block125Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block125Part017CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block125Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block125Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block125Part017CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block125Part017SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block125Part017] using hcert

def TailChunk000Sub001Block125Part018SupportExplicit : Finset ℕ :=
  ([13451] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block125Part018 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block125Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13451
    = surrogateDiagTailX0RatChunk000Sub001Block125Part018

theorem surrogateDiagonalTailChunk000Sub001Block125Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block125Part018CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block125Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block125Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block125Part018CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block125Part018SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block125Part018] using hcert

def TailChunk000Sub001Block125Part019SupportExplicit : Finset ℕ :=
  ([13453] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block125Part019 : ℚ :=
  (5016323727 : ℚ) / 743447694692310400

def SurrogateDiagonalTailChunk000Sub001Block125Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13453
    = surrogateDiagTailX0RatChunk000Sub001Block125Part019

theorem surrogateDiagonalTailChunk000Sub001Block125Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block125Part019CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block125Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block125Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block125Part019CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block125Part019SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block125Part019] using hcert

def TailChunk000Sub001Block125Part020SupportExplicit : Finset ℕ :=
  ([13457] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block125Part020 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block125Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13457
    = surrogateDiagTailX0RatChunk000Sub001Block125Part020

theorem surrogateDiagonalTailChunk000Sub001Block125Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block125Part020CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block125Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block125Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block125Part020CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block125Part020SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block125Part020] using hcert

def TailChunk000Sub001Block125Part021SupportExplicit : Finset ℕ :=
  ([13458] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block125Part021 : ℚ :=
  (188558625 : ℚ) / 101065382584384

def SurrogateDiagonalTailChunk000Sub001Block125Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13458
    = surrogateDiagTailX0RatChunk000Sub001Block125Part021

theorem surrogateDiagonalTailChunk000Sub001Block125Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block125Part021CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block125Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block125Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block125Part021CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block125Part021SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block125Part021] using hcert

def TailChunk000Sub001Block125Part022SupportExplicit : Finset ℕ :=
  ([13459] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block125Part022 : ℚ :=
  (55126170725 : ℚ) / 36864844036900798464

def SurrogateDiagonalTailChunk000Sub001Block125Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13459
    = surrogateDiagTailX0RatChunk000Sub001Block125Part022

theorem surrogateDiagonalTailChunk000Sub001Block125Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block125Part022CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block125Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block125Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block125Part022CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block125Part022SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block125Part022] using hcert

def TailChunk000Sub001Block125Part023SupportExplicit : Finset ℕ :=
  ([13461] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block125Part023 : ℚ :=
  (1826085167 : ℚ) / 12887478868377600

def SurrogateDiagonalTailChunk000Sub001Block125Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13461
    = surrogateDiagTailX0RatChunk000Sub001Block125Part023

theorem surrogateDiagonalTailChunk000Sub001Block125Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block125Part023CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block125Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block125Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block125Part023CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block125Part023SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block125Part023] using hcert

def TailChunk000Sub001Block125Part024SupportExplicit : Finset ℕ :=
  ([13462] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block125Part024 : ℚ :=
  (1368724559375 : ℚ) / 2304052752306299904

def SurrogateDiagonalTailChunk000Sub001Block125Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13462
    = surrogateDiagTailX0RatChunk000Sub001Block125Part024

theorem surrogateDiagonalTailChunk000Sub001Block125Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block125Part024CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block125Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block125Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block125Part024CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block125Part024SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block125Part024] using hcert

def surrogateDiagonalTailChunk000Sub001Block125HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block125Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block125Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block125Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block125Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block125Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block125Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block125Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block125Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block125Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block125Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block125Head : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block125Part000
    + surrogateDiagTailX0RatChunk000Sub001Block125Part001
    + surrogateDiagTailX0RatChunk000Sub001Block125Part002
    + surrogateDiagTailX0RatChunk000Sub001Block125Part003
    + surrogateDiagTailX0RatChunk000Sub001Block125Part004
    + surrogateDiagTailX0RatChunk000Sub001Block125Part005
    + surrogateDiagTailX0RatChunk000Sub001Block125Part006
    + surrogateDiagTailX0RatChunk000Sub001Block125Part007
    + surrogateDiagTailX0RatChunk000Sub001Block125Part008
    + surrogateDiagTailX0RatChunk000Sub001Block125Part009

def surrogateDiagonalTailChunk000Sub001Block125MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block125Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block125Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block125Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block125Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block125Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block125Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block125Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block125Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block125Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block125Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block125Mid : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block125Part010
    + surrogateDiagTailX0RatChunk000Sub001Block125Part011
    + surrogateDiagTailX0RatChunk000Sub001Block125Part012
    + surrogateDiagTailX0RatChunk000Sub001Block125Part013
    + surrogateDiagTailX0RatChunk000Sub001Block125Part014
    + surrogateDiagTailX0RatChunk000Sub001Block125Part015
    + surrogateDiagTailX0RatChunk000Sub001Block125Part016
    + surrogateDiagTailX0RatChunk000Sub001Block125Part017
    + surrogateDiagTailX0RatChunk000Sub001Block125Part018
    + surrogateDiagTailX0RatChunk000Sub001Block125Part019

def surrogateDiagonalTailChunk000Sub001Block125TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block125Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block125Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block125Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block125Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block125Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block125Tail : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block125Part020
    + surrogateDiagTailX0RatChunk000Sub001Block125Part021
    + surrogateDiagTailX0RatChunk000Sub001Block125Part022
    + surrogateDiagTailX0RatChunk000Sub001Block125Part023
    + surrogateDiagTailX0RatChunk000Sub001Block125Part024

def surrogateDiagonalTailChunk000Sub001Block125Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub001Block125HeadSum X0
    + surrogateDiagonalTailChunk000Sub001Block125MidSum X0
    + surrogateDiagonalTailChunk000Sub001Block125TailSum X0

def surrogateDiagTailX0RatChunk000Sub001Block125 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block125Part000
    + surrogateDiagTailX0RatChunk000Sub001Block125Part001
    + surrogateDiagTailX0RatChunk000Sub001Block125Part002
    + surrogateDiagTailX0RatChunk000Sub001Block125Part003
    + surrogateDiagTailX0RatChunk000Sub001Block125Part004
    + surrogateDiagTailX0RatChunk000Sub001Block125Part005
    + surrogateDiagTailX0RatChunk000Sub001Block125Part006
    + surrogateDiagTailX0RatChunk000Sub001Block125Part007
    + surrogateDiagTailX0RatChunk000Sub001Block125Part008
    + surrogateDiagTailX0RatChunk000Sub001Block125Part009
    + surrogateDiagTailX0RatChunk000Sub001Block125Part010
    + surrogateDiagTailX0RatChunk000Sub001Block125Part011
    + surrogateDiagTailX0RatChunk000Sub001Block125Part012
    + surrogateDiagTailX0RatChunk000Sub001Block125Part013
    + surrogateDiagTailX0RatChunk000Sub001Block125Part014
    + surrogateDiagTailX0RatChunk000Sub001Block125Part015
    + surrogateDiagTailX0RatChunk000Sub001Block125Part016
    + surrogateDiagTailX0RatChunk000Sub001Block125Part017
    + surrogateDiagTailX0RatChunk000Sub001Block125Part018
    + surrogateDiagTailX0RatChunk000Sub001Block125Part019
    + surrogateDiagTailX0RatChunk000Sub001Block125Part020
    + surrogateDiagTailX0RatChunk000Sub001Block125Part021
    + surrogateDiagTailX0RatChunk000Sub001Block125Part022
    + surrogateDiagTailX0RatChunk000Sub001Block125Part023
    + surrogateDiagTailX0RatChunk000Sub001Block125Part024

theorem surrogateDiagTailX0RatChunk000Sub001Block125_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk000Sub001Block125Head + surrogateDiagTailX0RatChunk000Sub001Block125Mid + surrogateDiagTailX0RatChunk000Sub001Block125Tail =
      surrogateDiagTailX0RatChunk000Sub001Block125 := by
  unfold surrogateDiagTailX0RatChunk000Sub001Block125Head surrogateDiagTailX0RatChunk000Sub001Block125Mid surrogateDiagTailX0RatChunk000Sub001Block125Tail surrogateDiagTailX0RatChunk000Sub001Block125
  ring

def SurrogateDiagonalTailChunk000Sub001Block125HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block125HeadSum X0 = surrogateDiagTailX0RatChunk000Sub001Block125Head

def SurrogateDiagonalTailChunk000Sub001Block125MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block125MidSum X0 = surrogateDiagTailX0RatChunk000Sub001Block125Mid

def SurrogateDiagonalTailChunk000Sub001Block125TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block125TailSum X0 = surrogateDiagTailX0RatChunk000Sub001Block125Tail

theorem surrogateDiagonalTailChunk000Sub001Block125_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk000Sub001Block125HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk000Sub001Block125MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk000Sub001Block125TailCertificateAt X0) :
    surrogateDiagonalTailChunk000Sub001Block125Sum X0 = surrogateDiagTailX0RatChunk000Sub001Block125 := by
  unfold SurrogateDiagonalTailChunk000Sub001Block125HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk000Sub001Block125MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk000Sub001Block125TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk000Sub001Block125Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk000Sub001Block125_eq_head_add_mid_add_tail

/-- Block 126 covers tail-support indices [8150,8175) and q from 13463 to 13502. -/

def TailChunk000Sub001Block126Part000SupportExplicit : Finset ℕ :=
  ([13463] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block126Part000 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block126Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13463
    = surrogateDiagTailX0RatChunk000Sub001Block126Part000

theorem surrogateDiagonalTailChunk000Sub001Block126Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block126Part000CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block126Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block126Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block126Part000CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block126Part000SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block126Part000] using hcert

def TailChunk000Sub001Block126Part001SupportExplicit : Finset ℕ :=
  ([13465] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block126Part001 : ℚ :=
  (906927145525 : ℚ) / 33617626394920255488

def SurrogateDiagonalTailChunk000Sub001Block126Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13465
    = surrogateDiagTailX0RatChunk000Sub001Block126Part001

theorem surrogateDiagonalTailChunk000Sub001Block126Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block126Part001CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block126Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block126Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block126Part001CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block126Part001SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block126Part001] using hcert

def TailChunk000Sub001Block126Part002SupportExplicit : Finset ℕ :=
  ([13466] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block126Part002 : ℚ :=
  (708332640625 : ℚ) / 1283935765425283872

def SurrogateDiagonalTailChunk000Sub001Block126Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13466
    = surrogateDiagTailX0RatChunk000Sub001Block126Part002

theorem surrogateDiagonalTailChunk000Sub001Block126Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block126Part002CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block126Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block126Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block126Part002CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block126Part002SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block126Part002] using hcert

def TailChunk000Sub001Block126Part003SupportExplicit : Finset ℕ :=
  ([13469] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block126Part003 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block126Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13469
    = surrogateDiagTailX0RatChunk000Sub001Block126Part003

theorem surrogateDiagonalTailChunk000Sub001Block126Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block126Part003CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block126Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block126Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block126Part003CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block126Part003SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block126Part003] using hcert

def TailChunk000Sub001Block126Part004SupportExplicit : Finset ℕ :=
  ([13470] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block126Part004 : ℚ :=
  (104943759225 : ℚ) / 68761859473276928

def SurrogateDiagonalTailChunk000Sub001Block126Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13470
    = surrogateDiagTailX0RatChunk000Sub001Block126Part004

theorem surrogateDiagonalTailChunk000Sub001Block126Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block126Part004CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block126Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block126Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block126Part004CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block126Part004SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block126Part004] using hcert

def TailChunk000Sub001Block126Part005SupportExplicit : Finset ℕ :=
  ([13471] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block126Part005 : ℚ :=
  (24962447375 : ℚ) / 7328370209781123072

def SurrogateDiagonalTailChunk000Sub001Block126Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13471
    = surrogateDiagTailX0RatChunk000Sub001Block126Part005

theorem surrogateDiagonalTailChunk000Sub001Block126Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block126Part005CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block126Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block126Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block126Part005CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block126Part005SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block126Part005] using hcert

def TailChunk000Sub001Block126Part006SupportExplicit : Finset ℕ :=
  ([13474] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block126Part006 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block126Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13474
    = surrogateDiagTailX0RatChunk000Sub001Block126Part006

theorem surrogateDiagonalTailChunk000Sub001Block126Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block126Part006CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block126Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block126Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block126Part006CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block126Part006SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block126Part006] using hcert

def TailChunk000Sub001Block126Part007SupportExplicit : Finset ℕ :=
  ([13477] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block126Part007 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block126Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13477
    = surrogateDiagTailX0RatChunk000Sub001Block126Part007

theorem surrogateDiagonalTailChunk000Sub001Block126Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block126Part007CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block126Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block126Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block126Part007CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block126Part007SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block126Part007] using hcert

def TailChunk000Sub001Block126Part008SupportExplicit : Finset ℕ :=
  ([13478] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block126Part008 : ℚ :=
  (32388597675 : ℚ) / 1419474951544477696

def SurrogateDiagonalTailChunk000Sub001Block126Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13478
    = surrogateDiagTailX0RatChunk000Sub001Block126Part008

theorem surrogateDiagonalTailChunk000Sub001Block126Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block126Part008CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block126Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block126Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block126Part008CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block126Part008SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block126Part008] using hcert

def TailChunk000Sub001Block126Part009SupportExplicit : Finset ℕ :=
  ([13479] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block126Part009 : ℚ :=
  (19714907425 : ℚ) / 254522311025908512

def SurrogateDiagonalTailChunk000Sub001Block126Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13479
    = surrogateDiagTailX0RatChunk000Sub001Block126Part009

theorem surrogateDiagonalTailChunk000Sub001Block126Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block126Part009CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block126Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block126Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block126Part009CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block126Part009SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block126Part009] using hcert

def TailChunk000Sub001Block126Part010SupportExplicit : Finset ℕ :=
  ([13481] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block126Part010 : ℚ :=
  (5016369067 : ℚ) / 440389316955340800

def SurrogateDiagonalTailChunk000Sub001Block126Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13481
    = surrogateDiagTailX0RatChunk000Sub001Block126Part010

theorem surrogateDiagonalTailChunk000Sub001Block126Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block126Part010CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block126Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block126Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block126Part010CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block126Part010SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block126Part010] using hcert

def TailChunk000Sub001Block126Part011SupportExplicit : Finset ℕ :=
  ([13483] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block126Part011 : ℚ :=
  (18201070375 : ℚ) / 19256091694703050752

def SurrogateDiagonalTailChunk000Sub001Block126Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13483
    = surrogateDiagTailX0RatChunk000Sub001Block126Part011

theorem surrogateDiagonalTailChunk000Sub001Block126Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block126Part011CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block126Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block126Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block126Part011CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block126Part011SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block126Part011] using hcert

def TailChunk000Sub001Block126Part012SupportExplicit : Finset ℕ :=
  ([13485] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block126Part012 : ℚ :=
  (51440758333 : ℚ) / 203968894677811200

def SurrogateDiagonalTailChunk000Sub001Block126Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13485
    = surrogateDiagTailX0RatChunk000Sub001Block126Part012

theorem surrogateDiagonalTailChunk000Sub001Block126Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block126Part012CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block126Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block126Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block126Part012CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block126Part012SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block126Part012] using hcert

def TailChunk000Sub001Block126Part013SupportExplicit : Finset ℕ :=
  ([13486] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block126Part013 : ℚ :=
  (2535151321 : ℚ) / 46770421525862400

def SurrogateDiagonalTailChunk000Sub001Block126Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13486
    = surrogateDiagTailX0RatChunk000Sub001Block126Part013

theorem surrogateDiagonalTailChunk000Sub001Block126Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block126Part013CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block126Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block126Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block126Part013CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block126Part013SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block126Part013] using hcert

def TailChunk000Sub001Block126Part014SupportExplicit : Finset ℕ :=
  ([13487] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block126Part014 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block126Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13487
    = surrogateDiagTailX0RatChunk000Sub001Block126Part014

theorem surrogateDiagonalTailChunk000Sub001Block126Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block126Part014CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block126Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block126Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block126Part014CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block126Part014SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block126Part014] using hcert

def TailChunk000Sub001Block126Part015SupportExplicit : Finset ℕ :=
  ([13489] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block126Part015 : ℚ :=
  (31632304849 : ℚ) / 1485809544344371200

def SurrogateDiagonalTailChunk000Sub001Block126Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13489
    = surrogateDiagTailX0RatChunk000Sub001Block126Part015

theorem surrogateDiagonalTailChunk000Sub001Block126Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block126Part015CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block126Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block126Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block126Part015CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block126Part015SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block126Part015] using hcert

def TailChunk000Sub001Block126Part016SupportExplicit : Finset ℕ :=
  ([13490] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block126Part016 : ℚ :=
  (10067565227 : ℚ) / 32268516540825600

def SurrogateDiagonalTailChunk000Sub001Block126Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13490
    = surrogateDiagTailX0RatChunk000Sub001Block126Part016

theorem surrogateDiagonalTailChunk000Sub001Block126Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block126Part016CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block126Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block126Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block126Part016CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block126Part016SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block126Part016] using hcert

def TailChunk000Sub001Block126Part017SupportExplicit : Finset ℕ :=
  ([13493] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block126Part017 : ℚ :=
  (167925449 : ℚ) / 181891341122025600

def SurrogateDiagonalTailChunk000Sub001Block126Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13493
    = surrogateDiagTailX0RatChunk000Sub001Block126Part017

theorem surrogateDiagonalTailChunk000Sub001Block126Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block126Part017CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block126Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block126Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block126Part017CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block126Part017SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block126Part017] using hcert

def TailChunk000Sub001Block126Part018SupportExplicit : Finset ℕ :=
  ([13494] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block126Part018 : ℚ :=
  (322619682125 : ℚ) / 363040952256036864

def SurrogateDiagonalTailChunk000Sub001Block126Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13494
    = surrogateDiagTailX0RatChunk000Sub001Block126Part018

theorem surrogateDiagonalTailChunk000Sub001Block126Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block126Part018CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block126Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block126Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block126Part018CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block126Part018SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block126Part018] using hcert

def TailChunk000Sub001Block126Part019SupportExplicit : Finset ℕ :=
  ([13495] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block126Part019 : ℚ :=
  (12830546975 : ℚ) / 477723116491634688

def SurrogateDiagonalTailChunk000Sub001Block126Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13495
    = surrogateDiagTailX0RatChunk000Sub001Block126Part019

theorem surrogateDiagonalTailChunk000Sub001Block126Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block126Part019CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block126Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block126Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block126Part019CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block126Part019SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block126Part019] using hcert

def TailChunk000Sub001Block126Part020SupportExplicit : Finset ℕ :=
  ([13497] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block126Part020 : ℚ :=
  (321487297 : ℚ) / 2771580534865920

def SurrogateDiagonalTailChunk000Sub001Block126Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13497
    = surrogateDiagTailX0RatChunk000Sub001Block126Part020

theorem surrogateDiagonalTailChunk000Sub001Block126Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block126Part020CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block126Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block126Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block126Part020CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block126Part020SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block126Part020] using hcert

def TailChunk000Sub001Block126Part021SupportExplicit : Finset ℕ :=
  ([13498] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block126Part021 : ℚ :=
  (132104295025 : ℚ) / 4029837493464465408

def SurrogateDiagonalTailChunk000Sub001Block126Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13498
    = surrogateDiagTailX0RatChunk000Sub001Block126Part021

theorem surrogateDiagonalTailChunk000Sub001Block126Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block126Part021CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block126Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block126Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block126Part021CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block126Part021SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block126Part021] using hcert

def TailChunk000Sub001Block126Part022SupportExplicit : Finset ℕ :=
  ([13499] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block126Part022 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block126Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13499
    = surrogateDiagTailX0RatChunk000Sub001Block126Part022

theorem surrogateDiagonalTailChunk000Sub001Block126Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block126Part022CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block126Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block126Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block126Part022CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block126Part022SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block126Part022] using hcert

def TailChunk000Sub001Block126Part023SupportExplicit : Finset ℕ :=
  ([13501] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block126Part023 : ℚ :=
  (199715385475 : ℚ) / 69072956646525752448

def SurrogateDiagonalTailChunk000Sub001Block126Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13501
    = surrogateDiagTailX0RatChunk000Sub001Block126Part023

theorem surrogateDiagonalTailChunk000Sub001Block126Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block126Part023CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block126Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block126Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block126Part023CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block126Part023SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block126Part023] using hcert

def TailChunk000Sub001Block126Part024SupportExplicit : Finset ℕ :=
  ([13502] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block126Part024 : ℚ :=
  (30783794225 : ℚ) / 2304052752306299904

def SurrogateDiagonalTailChunk000Sub001Block126Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13502
    = surrogateDiagTailX0RatChunk000Sub001Block126Part024

theorem surrogateDiagonalTailChunk000Sub001Block126Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block126Part024CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block126Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block126Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block126Part024CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block126Part024SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block126Part024] using hcert

def surrogateDiagonalTailChunk000Sub001Block126HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block126Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block126Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block126Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block126Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block126Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block126Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block126Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block126Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block126Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block126Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block126Head : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block126Part000
    + surrogateDiagTailX0RatChunk000Sub001Block126Part001
    + surrogateDiagTailX0RatChunk000Sub001Block126Part002
    + surrogateDiagTailX0RatChunk000Sub001Block126Part003
    + surrogateDiagTailX0RatChunk000Sub001Block126Part004
    + surrogateDiagTailX0RatChunk000Sub001Block126Part005
    + surrogateDiagTailX0RatChunk000Sub001Block126Part006
    + surrogateDiagTailX0RatChunk000Sub001Block126Part007
    + surrogateDiagTailX0RatChunk000Sub001Block126Part008
    + surrogateDiagTailX0RatChunk000Sub001Block126Part009

def surrogateDiagonalTailChunk000Sub001Block126MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block126Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block126Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block126Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block126Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block126Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block126Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block126Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block126Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block126Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block126Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block126Mid : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block126Part010
    + surrogateDiagTailX0RatChunk000Sub001Block126Part011
    + surrogateDiagTailX0RatChunk000Sub001Block126Part012
    + surrogateDiagTailX0RatChunk000Sub001Block126Part013
    + surrogateDiagTailX0RatChunk000Sub001Block126Part014
    + surrogateDiagTailX0RatChunk000Sub001Block126Part015
    + surrogateDiagTailX0RatChunk000Sub001Block126Part016
    + surrogateDiagTailX0RatChunk000Sub001Block126Part017
    + surrogateDiagTailX0RatChunk000Sub001Block126Part018
    + surrogateDiagTailX0RatChunk000Sub001Block126Part019

def surrogateDiagonalTailChunk000Sub001Block126TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block126Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block126Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block126Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block126Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block126Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block126Tail : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block126Part020
    + surrogateDiagTailX0RatChunk000Sub001Block126Part021
    + surrogateDiagTailX0RatChunk000Sub001Block126Part022
    + surrogateDiagTailX0RatChunk000Sub001Block126Part023
    + surrogateDiagTailX0RatChunk000Sub001Block126Part024

def surrogateDiagonalTailChunk000Sub001Block126Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub001Block126HeadSum X0
    + surrogateDiagonalTailChunk000Sub001Block126MidSum X0
    + surrogateDiagonalTailChunk000Sub001Block126TailSum X0

def surrogateDiagTailX0RatChunk000Sub001Block126 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block126Part000
    + surrogateDiagTailX0RatChunk000Sub001Block126Part001
    + surrogateDiagTailX0RatChunk000Sub001Block126Part002
    + surrogateDiagTailX0RatChunk000Sub001Block126Part003
    + surrogateDiagTailX0RatChunk000Sub001Block126Part004
    + surrogateDiagTailX0RatChunk000Sub001Block126Part005
    + surrogateDiagTailX0RatChunk000Sub001Block126Part006
    + surrogateDiagTailX0RatChunk000Sub001Block126Part007
    + surrogateDiagTailX0RatChunk000Sub001Block126Part008
    + surrogateDiagTailX0RatChunk000Sub001Block126Part009
    + surrogateDiagTailX0RatChunk000Sub001Block126Part010
    + surrogateDiagTailX0RatChunk000Sub001Block126Part011
    + surrogateDiagTailX0RatChunk000Sub001Block126Part012
    + surrogateDiagTailX0RatChunk000Sub001Block126Part013
    + surrogateDiagTailX0RatChunk000Sub001Block126Part014
    + surrogateDiagTailX0RatChunk000Sub001Block126Part015
    + surrogateDiagTailX0RatChunk000Sub001Block126Part016
    + surrogateDiagTailX0RatChunk000Sub001Block126Part017
    + surrogateDiagTailX0RatChunk000Sub001Block126Part018
    + surrogateDiagTailX0RatChunk000Sub001Block126Part019
    + surrogateDiagTailX0RatChunk000Sub001Block126Part020
    + surrogateDiagTailX0RatChunk000Sub001Block126Part021
    + surrogateDiagTailX0RatChunk000Sub001Block126Part022
    + surrogateDiagTailX0RatChunk000Sub001Block126Part023
    + surrogateDiagTailX0RatChunk000Sub001Block126Part024

theorem surrogateDiagTailX0RatChunk000Sub001Block126_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk000Sub001Block126Head + surrogateDiagTailX0RatChunk000Sub001Block126Mid + surrogateDiagTailX0RatChunk000Sub001Block126Tail =
      surrogateDiagTailX0RatChunk000Sub001Block126 := by
  unfold surrogateDiagTailX0RatChunk000Sub001Block126Head surrogateDiagTailX0RatChunk000Sub001Block126Mid surrogateDiagTailX0RatChunk000Sub001Block126Tail surrogateDiagTailX0RatChunk000Sub001Block126
  ring

def SurrogateDiagonalTailChunk000Sub001Block126HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block126HeadSum X0 = surrogateDiagTailX0RatChunk000Sub001Block126Head

def SurrogateDiagonalTailChunk000Sub001Block126MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block126MidSum X0 = surrogateDiagTailX0RatChunk000Sub001Block126Mid

def SurrogateDiagonalTailChunk000Sub001Block126TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block126TailSum X0 = surrogateDiagTailX0RatChunk000Sub001Block126Tail

theorem surrogateDiagonalTailChunk000Sub001Block126_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk000Sub001Block126HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk000Sub001Block126MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk000Sub001Block126TailCertificateAt X0) :
    surrogateDiagonalTailChunk000Sub001Block126Sum X0 = surrogateDiagTailX0RatChunk000Sub001Block126 := by
  unfold SurrogateDiagonalTailChunk000Sub001Block126HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk000Sub001Block126MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk000Sub001Block126TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk000Sub001Block126Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk000Sub001Block126_eq_head_add_mid_add_tail

/-- Block 127 covers tail-support indices [8175,8200) and q from 13503 to 13541. -/

def TailChunk000Sub001Block127Part000SupportExplicit : Finset ℕ :=
  ([13503] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block127Part000 : ℚ :=
  (316530514825 : ℚ) / 2202074277922386432

def SurrogateDiagonalTailChunk000Sub001Block127Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13503
    = surrogateDiagTailX0RatChunk000Sub001Block127Part000

theorem surrogateDiagonalTailChunk000Sub001Block127Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block127Part000CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block127Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block127Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block127Part000CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block127Part000SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block127Part000] using hcert

def TailChunk000Sub001Block127Part001SupportExplicit : Finset ℕ :=
  ([13505] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block127Part001 : ℚ :=
  (554520806575 : ℚ) / 28893943085439909888

def SurrogateDiagonalTailChunk000Sub001Block127Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13505
    = surrogateDiagTailX0RatChunk000Sub001Block127Part001

theorem surrogateDiagonalTailChunk000Sub001Block127Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block127Part001CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block127Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block127Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block127Part001CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block127Part001SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block127Part001] using hcert

def TailChunk000Sub001Block127Part002SupportExplicit : Finset ℕ :=
  ([13506] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block127Part002 : ℚ :=
  (12666216749 : ℚ) / 20507225625000000

def SurrogateDiagonalTailChunk000Sub001Block127Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13506
    = surrogateDiagTailX0RatChunk000Sub001Block127Part002

theorem surrogateDiagonalTailChunk000Sub001Block127Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block127Part002CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block127Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block127Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block127Part002CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block127Part002SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block127Part002] using hcert

def TailChunk000Sub001Block127Part003SupportExplicit : Finset ℕ :=
  ([13507] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block127Part003 : ℚ :=
  (37798295375 : ℚ) / 6688038241443612672

def SurrogateDiagonalTailChunk000Sub001Block127Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13507
    = surrogateDiagTailX0RatChunk000Sub001Block127Part003

theorem surrogateDiagonalTailChunk000Sub001Block127Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block127Part003CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block127Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block127Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block127Part003CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block127Part003SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block127Part003] using hcert

def TailChunk000Sub001Block127Part004SupportExplicit : Finset ℕ :=
  ([13510] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block127Part004 : ℚ :=
  (482026076125 : ℚ) / 1127396651405672448

def SurrogateDiagonalTailChunk000Sub001Block127Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13510
    = surrogateDiagTailX0RatChunk000Sub001Block127Part004

theorem surrogateDiagonalTailChunk000Sub001Block127Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block127Part004CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block127Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block127Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block127Part004CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block127Part004SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block127Part004] using hcert

def TailChunk000Sub001Block127Part005SupportExplicit : Finset ℕ :=
  ([13511] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block127Part005 : ℚ :=
  (1567614425 : ℚ) / 1341539194173917184

def SurrogateDiagonalTailChunk000Sub001Block127Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13511
    = surrogateDiagTailX0RatChunk000Sub001Block127Part005

theorem surrogateDiagonalTailChunk000Sub001Block127Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block127Part005CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block127Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block127Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block127Part005CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block127Part005SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block127Part005] using hcert

def TailChunk000Sub001Block127Part006SupportExplicit : Finset ℕ :=
  ([13513] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block127Part006 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block127Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13513
    = surrogateDiagTailX0RatChunk000Sub001Block127Part006

theorem surrogateDiagonalTailChunk000Sub001Block127Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block127Part006CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block127Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block127Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block127Part006CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block127Part006SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block127Part006] using hcert

def TailChunk000Sub001Block127Part007SupportExplicit : Finset ℕ :=
  ([13514] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block127Part007 : ℚ :=
  (226434087975 : ℚ) / 371047643509817344

def SurrogateDiagonalTailChunk000Sub001Block127Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13514
    = surrogateDiagTailX0RatChunk000Sub001Block127Part007

theorem surrogateDiagonalTailChunk000Sub001Block127Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block127Part007CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block127Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block127Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block127Part007CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block127Part007SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block127Part007] using hcert

def TailChunk000Sub001Block127Part008SupportExplicit : Finset ℕ :=
  ([13515] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block127Part008 : ℚ :=
  (653736470325 : ℚ) / 817953964354961408

def SurrogateDiagonalTailChunk000Sub001Block127Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13515
    = surrogateDiagTailX0RatChunk000Sub001Block127Part008

theorem surrogateDiagonalTailChunk000Sub001Block127Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block127Part008CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block127Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block127Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block127Part008CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block127Part008SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block127Part008] using hcert

def TailChunk000Sub001Block127Part009SupportExplicit : Finset ℕ :=
  ([13517] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block127Part009 : ℚ :=
  (5530958083 : ℚ) / 28102251346654050

def SurrogateDiagonalTailChunk000Sub001Block127Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13517
    = surrogateDiagTailX0RatChunk000Sub001Block127Part009

theorem surrogateDiagonalTailChunk000Sub001Block127Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block127Part009CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block127Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block127Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block127Part009CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block127Part009SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block127Part009] using hcert

def TailChunk000Sub001Block127Part010SupportExplicit : Finset ℕ :=
  ([13519] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block127Part010 : ℚ :=
  (388471452247 : ℚ) / 2274470547404851200

def SurrogateDiagonalTailChunk000Sub001Block127Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13519
    = surrogateDiagTailX0RatChunk000Sub001Block127Part010

theorem surrogateDiagonalTailChunk000Sub001Block127Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block127Part010CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block127Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block127Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block127Part010CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block127Part010SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block127Part010] using hcert

def TailChunk000Sub001Block127Part011SupportExplicit : Finset ℕ :=
  ([13521] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block127Part011 : ℚ :=
  (793331409575 : ℚ) / 2061681643324369296

def SurrogateDiagonalTailChunk000Sub001Block127Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13521
    = surrogateDiagTailX0RatChunk000Sub001Block127Part011

theorem surrogateDiagonalTailChunk000Sub001Block127Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block127Part011CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block127Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block127Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block127Part011CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block127Part011SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block127Part011] using hcert

def TailChunk000Sub001Block127Part012SupportExplicit : Finset ℕ :=
  ([13522] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block127Part012 : ℚ :=
  (1142778025 : ℚ) / 2088688299889152

def SurrogateDiagonalTailChunk000Sub001Block127Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13522
    = surrogateDiagTailX0RatChunk000Sub001Block127Part012

theorem surrogateDiagonalTailChunk000Sub001Block127Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block127Part012CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block127Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block127Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block127Part012CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block127Part012SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block127Part012] using hcert

def TailChunk000Sub001Block127Part013SupportExplicit : Finset ℕ :=
  ([13523] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block127Part013 : ℚ :=
  (2857367640625 : ℚ) / 20899244843932563282

def SurrogateDiagonalTailChunk000Sub001Block127Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13523
    = surrogateDiagTailX0RatChunk000Sub001Block127Part013

theorem surrogateDiagonalTailChunk000Sub001Block127Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block127Part013CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block127Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block127Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block127Part013CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block127Part013SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block127Part013] using hcert

def TailChunk000Sub001Block127Part014SupportExplicit : Finset ℕ :=
  ([13526] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block127Part014 : ℚ :=
  (714658890625 : ℚ) / 1306975760962825842

def SurrogateDiagonalTailChunk000Sub001Block127Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13526
    = surrogateDiagTailX0RatChunk000Sub001Block127Part014

theorem surrogateDiagonalTailChunk000Sub001Block127Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block127Part014CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block127Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block127Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block127Part014CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block127Part014SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block127Part014] using hcert

def TailChunk000Sub001Block127Part015SupportExplicit : Finset ℕ :=
  ([13529] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block127Part015 : ℚ :=
  (11104668369925 : ℚ) / 77865006930404439168

def SurrogateDiagonalTailChunk000Sub001Block127Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13529
    = surrogateDiagTailX0RatChunk000Sub001Block127Part015

theorem surrogateDiagonalTailChunk000Sub001Block127Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block127Part015CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block127Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block127Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block127Part015CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block127Part015SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block127Part015] using hcert

def TailChunk000Sub001Block127Part016SupportExplicit : Finset ℕ :=
  ([13530] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block127Part016 : ℚ :=
  (21816962357 : ℚ) / 5243928576000000

def SurrogateDiagonalTailChunk000Sub001Block127Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13530
    = surrogateDiagTailX0RatChunk000Sub001Block127Part016

theorem surrogateDiagonalTailChunk000Sub001Block127Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block127Part016CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block127Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block127Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block127Part016CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block127Part016SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block127Part016] using hcert

def TailChunk000Sub001Block127Part017SupportExplicit : Finset ℕ :=
  ([13531] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block127Part017 : ℚ :=
  (316709984125 : ℚ) / 1612509631660924416

def SurrogateDiagonalTailChunk000Sub001Block127Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13531
    = surrogateDiagTailX0RatChunk000Sub001Block127Part017

theorem surrogateDiagonalTailChunk000Sub001Block127Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block127Part017CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block127Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block127Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block127Part017CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block127Part017SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block127Part017] using hcert

def TailChunk000Sub001Block127Part018SupportExplicit : Finset ℕ :=
  ([13533] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block127Part018 : ℚ :=
  (4511656902175 : ℚ) / 11889845762566422528

def SurrogateDiagonalTailChunk000Sub001Block127Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13533
    = surrogateDiagTailX0RatChunk000Sub001Block127Part018

theorem surrogateDiagonalTailChunk000Sub001Block127Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block127Part018CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block127Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block127Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block127Part018CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block127Part018SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block127Part018] using hcert

def TailChunk000Sub001Block127Part019SupportExplicit : Finset ℕ :=
  ([13534] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block127Part019 : ℚ :=
  (55481903993 : ℚ) / 94892654736000000

def SurrogateDiagonalTailChunk000Sub001Block127Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13534
    = surrogateDiagTailX0RatChunk000Sub001Block127Part019

theorem surrogateDiagonalTailChunk000Sub001Block127Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block127Part019CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block127Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block127Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block127Part019CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block127Part019SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block127Part019] using hcert

def TailChunk000Sub001Block127Part020SupportExplicit : Finset ℕ :=
  ([13535] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block127Part020 : ℚ :=
  (7782070884025 : ℚ) / 34322427256250124288

def SurrogateDiagonalTailChunk000Sub001Block127Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13535
    = surrogateDiagTailX0RatChunk000Sub001Block127Part020

theorem surrogateDiagonalTailChunk000Sub001Block127Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block127Part020CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block127Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block127Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block127Part020CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block127Part020SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block127Part020] using hcert

def TailChunk000Sub001Block127Part021SupportExplicit : Finset ℕ :=
  ([13537] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block127Part021 : ℚ :=
  (2863287015625 : ℚ) / 20985931470214397952

def SurrogateDiagonalTailChunk000Sub001Block127Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13537
    = surrogateDiagTailX0RatChunk000Sub001Block127Part021

theorem surrogateDiagonalTailChunk000Sub001Block127Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block127Part021CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block127Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block127Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block127Part021CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block127Part021SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block127Part021] using hcert

def TailChunk000Sub001Block127Part022SupportExplicit : Finset ℕ :=
  ([13538] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block127Part022 : ℚ :=
  (2335181990275 : ℚ) / 2821891855406617728

def SurrogateDiagonalTailChunk000Sub001Block127Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13538
    = surrogateDiagTailX0RatChunk000Sub001Block127Part022

theorem surrogateDiagonalTailChunk000Sub001Block127Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block127Part022CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block127Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block127Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block127Part022CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block127Part022SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block127Part022] using hcert

def TailChunk000Sub001Block127Part023SupportExplicit : Finset ℕ :=
  ([13539] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block127Part023 : ℚ :=
  (5090160548725 : ℚ) / 16581476717206437888

def SurrogateDiagonalTailChunk000Sub001Block127Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13539
    = surrogateDiagTailX0RatChunk000Sub001Block127Part023

theorem surrogateDiagonalTailChunk000Sub001Block127Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block127Part023CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block127Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block127Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block127Part023CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block127Part023SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block127Part023] using hcert

def TailChunk000Sub001Block127Part024SupportExplicit : Finset ℕ :=
  ([13541] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block127Part024 : ℚ :=
  (129912484979 : ℚ) / 763108061094000000

def SurrogateDiagonalTailChunk000Sub001Block127Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13541
    = surrogateDiagTailX0RatChunk000Sub001Block127Part024

theorem surrogateDiagonalTailChunk000Sub001Block127Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block127Part024CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block127Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block127Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block127Part024CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block127Part024SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block127Part024] using hcert

def surrogateDiagonalTailChunk000Sub001Block127HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block127Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block127Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block127Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block127Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block127Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block127Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block127Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block127Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block127Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block127Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block127Head : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block127Part000
    + surrogateDiagTailX0RatChunk000Sub001Block127Part001
    + surrogateDiagTailX0RatChunk000Sub001Block127Part002
    + surrogateDiagTailX0RatChunk000Sub001Block127Part003
    + surrogateDiagTailX0RatChunk000Sub001Block127Part004
    + surrogateDiagTailX0RatChunk000Sub001Block127Part005
    + surrogateDiagTailX0RatChunk000Sub001Block127Part006
    + surrogateDiagTailX0RatChunk000Sub001Block127Part007
    + surrogateDiagTailX0RatChunk000Sub001Block127Part008
    + surrogateDiagTailX0RatChunk000Sub001Block127Part009

def surrogateDiagonalTailChunk000Sub001Block127MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block127Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block127Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block127Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block127Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block127Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block127Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block127Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block127Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block127Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block127Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block127Mid : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block127Part010
    + surrogateDiagTailX0RatChunk000Sub001Block127Part011
    + surrogateDiagTailX0RatChunk000Sub001Block127Part012
    + surrogateDiagTailX0RatChunk000Sub001Block127Part013
    + surrogateDiagTailX0RatChunk000Sub001Block127Part014
    + surrogateDiagTailX0RatChunk000Sub001Block127Part015
    + surrogateDiagTailX0RatChunk000Sub001Block127Part016
    + surrogateDiagTailX0RatChunk000Sub001Block127Part017
    + surrogateDiagTailX0RatChunk000Sub001Block127Part018
    + surrogateDiagTailX0RatChunk000Sub001Block127Part019

def surrogateDiagonalTailChunk000Sub001Block127TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block127Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block127Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block127Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block127Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block127Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block127Tail : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block127Part020
    + surrogateDiagTailX0RatChunk000Sub001Block127Part021
    + surrogateDiagTailX0RatChunk000Sub001Block127Part022
    + surrogateDiagTailX0RatChunk000Sub001Block127Part023
    + surrogateDiagTailX0RatChunk000Sub001Block127Part024

def surrogateDiagonalTailChunk000Sub001Block127Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub001Block127HeadSum X0
    + surrogateDiagonalTailChunk000Sub001Block127MidSum X0
    + surrogateDiagonalTailChunk000Sub001Block127TailSum X0

def surrogateDiagTailX0RatChunk000Sub001Block127 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block127Part000
    + surrogateDiagTailX0RatChunk000Sub001Block127Part001
    + surrogateDiagTailX0RatChunk000Sub001Block127Part002
    + surrogateDiagTailX0RatChunk000Sub001Block127Part003
    + surrogateDiagTailX0RatChunk000Sub001Block127Part004
    + surrogateDiagTailX0RatChunk000Sub001Block127Part005
    + surrogateDiagTailX0RatChunk000Sub001Block127Part006
    + surrogateDiagTailX0RatChunk000Sub001Block127Part007
    + surrogateDiagTailX0RatChunk000Sub001Block127Part008
    + surrogateDiagTailX0RatChunk000Sub001Block127Part009
    + surrogateDiagTailX0RatChunk000Sub001Block127Part010
    + surrogateDiagTailX0RatChunk000Sub001Block127Part011
    + surrogateDiagTailX0RatChunk000Sub001Block127Part012
    + surrogateDiagTailX0RatChunk000Sub001Block127Part013
    + surrogateDiagTailX0RatChunk000Sub001Block127Part014
    + surrogateDiagTailX0RatChunk000Sub001Block127Part015
    + surrogateDiagTailX0RatChunk000Sub001Block127Part016
    + surrogateDiagTailX0RatChunk000Sub001Block127Part017
    + surrogateDiagTailX0RatChunk000Sub001Block127Part018
    + surrogateDiagTailX0RatChunk000Sub001Block127Part019
    + surrogateDiagTailX0RatChunk000Sub001Block127Part020
    + surrogateDiagTailX0RatChunk000Sub001Block127Part021
    + surrogateDiagTailX0RatChunk000Sub001Block127Part022
    + surrogateDiagTailX0RatChunk000Sub001Block127Part023
    + surrogateDiagTailX0RatChunk000Sub001Block127Part024

theorem surrogateDiagTailX0RatChunk000Sub001Block127_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk000Sub001Block127Head + surrogateDiagTailX0RatChunk000Sub001Block127Mid + surrogateDiagTailX0RatChunk000Sub001Block127Tail =
      surrogateDiagTailX0RatChunk000Sub001Block127 := by
  unfold surrogateDiagTailX0RatChunk000Sub001Block127Head surrogateDiagTailX0RatChunk000Sub001Block127Mid surrogateDiagTailX0RatChunk000Sub001Block127Tail surrogateDiagTailX0RatChunk000Sub001Block127
  ring

def SurrogateDiagonalTailChunk000Sub001Block127HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block127HeadSum X0 = surrogateDiagTailX0RatChunk000Sub001Block127Head

def SurrogateDiagonalTailChunk000Sub001Block127MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block127MidSum X0 = surrogateDiagTailX0RatChunk000Sub001Block127Mid

def SurrogateDiagonalTailChunk000Sub001Block127TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block127TailSum X0 = surrogateDiagTailX0RatChunk000Sub001Block127Tail

theorem surrogateDiagonalTailChunk000Sub001Block127_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk000Sub001Block127HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk000Sub001Block127MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk000Sub001Block127TailCertificateAt X0) :
    surrogateDiagonalTailChunk000Sub001Block127Sum X0 = surrogateDiagTailX0RatChunk000Sub001Block127 := by
  unfold SurrogateDiagonalTailChunk000Sub001Block127HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk000Sub001Block127MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk000Sub001Block127TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk000Sub001Block127Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk000Sub001Block127_eq_head_add_mid_add_tail

/-- Block 128 covers tail-support indices [8200,8225) and q from 13542 to 13585. -/

def TailChunk000Sub001Block128Part000SupportExplicit : Finset ℕ :=
  ([13542] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block128Part000 : ℚ :=
  (12126794669 : ℚ) / 6967096615895040

def SurrogateDiagonalTailChunk000Sub001Block128Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13542
    = surrogateDiagTailX0RatChunk000Sub001Block128Part000

theorem surrogateDiagonalTailChunk000Sub001Block128Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block128Part000CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block128Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block128Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block128Part000CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block128Part000SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block128Part000] using hcert

def TailChunk000Sub001Block128Part001SupportExplicit : Finset ℕ :=
  ([13543] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block128Part001 : ℚ :=
  (10786317702325 : ℚ) / 72477407613237086208

def SurrogateDiagonalTailChunk000Sub001Block128Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13543
    = surrogateDiagTailX0RatChunk000Sub001Block128Part001

theorem surrogateDiagonalTailChunk000Sub001Block128Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block128Part001CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block128Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block128Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block128Part001CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block128Part001SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block128Part001] using hcert

def TailChunk000Sub001Block128Part002SupportExplicit : Finset ℕ :=
  ([13546] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block128Part002 : ℚ :=
  (103597257811 : ℚ) / 151643992109875200

def SurrogateDiagonalTailChunk000Sub001Block128Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13546
    = surrogateDiagTailX0RatChunk000Sub001Block128Part002

theorem surrogateDiagonalTailChunk000Sub001Block128Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block128Part002CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block128Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block128Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block128Part002CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block128Part002SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block128Part002] using hcert

def TailChunk000Sub001Block128Part003SupportExplicit : Finset ℕ :=
  ([13547] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block128Part003 : ℚ :=
  (369939986563 : ℚ) / 1992290264713267200

def SurrogateDiagonalTailChunk000Sub001Block128Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13547
    = surrogateDiagTailX0RatChunk000Sub001Block128Part003

theorem surrogateDiagonalTailChunk000Sub001Block128Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block128Part003CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block128Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block128Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block128Part003CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block128Part003SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block128Part003] using hcert

def TailChunk000Sub001Block128Part004SupportExplicit : Finset ℕ :=
  ([13549] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block128Part004 : ℚ :=
  (10341949632325 : ℚ) / 65789874881018462208

def SurrogateDiagonalTailChunk000Sub001Block128Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13549
    = surrogateDiagTailX0RatChunk000Sub001Block128Part004

theorem surrogateDiagonalTailChunk000Sub001Block128Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block128Part004CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block128Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block128Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block128Part004CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block128Part004SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block128Part004] using hcert

def TailChunk000Sub001Block128Part005SupportExplicit : Finset ℕ :=
  ([13551] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block128Part005 : ℚ :=
  (5099188548325 : ℚ) / 16640354517163788288

def SurrogateDiagonalTailChunk000Sub001Block128Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13551
    = surrogateDiagTailX0RatChunk000Sub001Block128Part005

theorem surrogateDiagonalTailChunk000Sub001Block128Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block128Part005CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block128Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block128Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block128Part005CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block128Part005SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block128Part005] using hcert

def TailChunk000Sub001Block128Part006SupportExplicit : Finset ℕ :=
  ([13553] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block128Part006 : ℚ :=
  (2870059515625 : ℚ) / 21085331800705277952

def SurrogateDiagonalTailChunk000Sub001Block128Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13553
    = surrogateDiagTailX0RatChunk000Sub001Block128Part006

theorem surrogateDiagonalTailChunk000Sub001Block128Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block128Part006CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block128Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block128Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block128Part006CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block128Part006SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block128Part006] using hcert

def TailChunk000Sub001Block128Part007SupportExplicit : Finset ℕ :=
  ([13555] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block128Part007 : ℚ :=
  (312203642029 : ℚ) / 1381032754456627200

def SurrogateDiagonalTailChunk000Sub001Block128Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13555
    = surrogateDiagTailX0RatChunk000Sub001Block128Part007

theorem surrogateDiagonalTailChunk000Sub001Block128Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block128Part007CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block128Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block128Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block128Part007CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block128Part007SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block128Part007] using hcert

def TailChunk000Sub001Block128Part008SupportExplicit : Finset ℕ :=
  ([13557] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block128Part008 : ℚ :=
  (5103705548125 : ℚ) / 16669852147007687808

def SurrogateDiagonalTailChunk000Sub001Block128Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13557
    = surrogateDiagTailX0RatChunk000Sub001Block128Part008

theorem surrogateDiagonalTailChunk000Sub001Block128Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block128Part008CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block128Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block128Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block128Part008CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block128Part008SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block128Part008] using hcert

def TailChunk000Sub001Block128Part009SupportExplicit : Finset ℕ :=
  ([13558] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block128Part009 : ℚ :=
  (718044390625 : ℚ) / 1319389809927356082

def SurrogateDiagonalTailChunk000Sub001Block128Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13558
    = surrogateDiagTailX0RatChunk000Sub001Block128Part009

theorem surrogateDiagonalTailChunk000Sub001Block128Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block128Part009CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block128Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block128Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block128Part009CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block128Part009SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block128Part009] using hcert

def TailChunk000Sub001Block128Part010SupportExplicit : Finset ℕ :=
  ([13559] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block128Part010 : ℚ :=
  (3776025335825 : ℚ) / 16120321926842548224

def SurrogateDiagonalTailChunk000Sub001Block128Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13559
    = surrogateDiagTailX0RatChunk000Sub001Block128Part010

theorem surrogateDiagonalTailChunk000Sub001Block128Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block128Part010CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block128Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block128Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block128Part010CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block128Part010SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block128Part010] using hcert

def TailChunk000Sub001Block128Part011SupportExplicit : Finset ℕ :=
  ([13561] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block128Part011 : ℚ :=
  (89078125763 : ℚ) / 625926602288400000

def SurrogateDiagonalTailChunk000Sub001Block128Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13561
    = surrogateDiagTailX0RatChunk000Sub001Block128Part011

theorem surrogateDiagonalTailChunk000Sub001Block128Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block128Part011CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block128Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block128Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block128Part011CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block128Part011SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block128Part011] using hcert

def TailChunk000Sub001Block128Part012SupportExplicit : Finset ℕ :=
  ([13562] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block128Part012 : ℚ :=
  (1149549025 : ℚ) / 2113516417319712

def SurrogateDiagonalTailChunk000Sub001Block128Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13562
    = surrogateDiagTailX0RatChunk000Sub001Block128Part012

theorem surrogateDiagonalTailChunk000Sub001Block128Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block128Part012CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block128Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block128Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block128Part012CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block128Part012SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block128Part012] using hcert

def TailChunk000Sub001Block128Part013SupportExplicit : Finset ℕ :=
  ([13565] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block128Part013 : ℚ :=
  (7816613885275 : ℚ) / 34627852981366161408

def SurrogateDiagonalTailChunk000Sub001Block128Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13565
    = surrogateDiagTailX0RatChunk000Sub001Block128Part013

theorem surrogateDiagonalTailChunk000Sub001Block128Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block128Part013CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block128Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block128Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block128Part013CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block128Part013SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block128Part013] using hcert

def TailChunk000Sub001Block128Part014SupportExplicit : Finset ℕ :=
  ([13566] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block128Part014 : ℚ :=
  (99857304275 : ℚ) / 29726278894485504

def SurrogateDiagonalTailChunk000Sub001Block128Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13566
    = surrogateDiagTailX0RatChunk000Sub001Block128Part014

theorem surrogateDiagonalTailChunk000Sub001Block128Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block128Part014CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block128Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block128Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block128Part014CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block128Part014SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block128Part014] using hcert

def TailChunk000Sub001Block128Part015SupportExplicit : Finset ℕ :=
  ([13567] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block128Part015 : ℚ :=
  (2875992015625 : ℚ) / 21172596378640429842

def SurrogateDiagonalTailChunk000Sub001Block128Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13567
    = surrogateDiagTailX0RatChunk000Sub001Block128Part015

theorem surrogateDiagonalTailChunk000Sub001Block128Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block128Part015CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block128Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block128Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block128Part015CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block128Part015SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block128Part015] using hcert

def TailChunk000Sub001Block128Part016SupportExplicit : Finset ℕ :=
  ([13569] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block128Part016 : ℚ :=
  (5112745547725 : ℚ) / 16728965039913426048

def SurrogateDiagonalTailChunk000Sub001Block128Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13569
    = surrogateDiagTailX0RatChunk000Sub001Block128Part016

theorem surrogateDiagonalTailChunk000Sub001Block128Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block128Part016CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block128Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block128Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block128Part016CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block128Part016SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block128Part016] using hcert

def TailChunk000Sub001Block128Part017SupportExplicit : Finset ℕ :=
  ([13570] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block128Part017 : ℚ :=
  (2028464625175 : ℚ) / 1696951858171772928

def SurrogateDiagonalTailChunk000Sub001Block128Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13570
    = surrogateDiagTailX0RatChunk000Sub001Block128Part017

theorem surrogateDiagonalTailChunk000Sub001Block128Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block128Part017CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block128Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block128Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block128Part017CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block128Part017SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block128Part017] using hcert

def TailChunk000Sub001Block128Part018SupportExplicit : Finset ℕ :=
  ([13571] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block128Part018 : ℚ :=
  (21997931051 : ℚ) / 151828247577600000

def SurrogateDiagonalTailChunk000Sub001Block128Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13571
    = surrogateDiagTailX0RatChunk000Sub001Block128Part018

theorem surrogateDiagonalTailChunk000Sub001Block128Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block128Part018CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block128Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block128Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block128Part018CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block128Part018SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block128Part018] using hcert

def TailChunk000Sub001Block128Part019SupportExplicit : Finset ℕ :=
  ([13574] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block128Part019 : ℚ :=
  (101647947661 : ℚ) / 144015653307187200

def SurrogateDiagonalTailChunk000Sub001Block128Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13574
    = surrogateDiagTailX0RatChunk000Sub001Block128Part019

theorem surrogateDiagonalTailChunk000Sub001Block128Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block128Part019CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block128Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block128Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block128Part019CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block128Part019SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block128Part019] using hcert

def TailChunk000Sub001Block128Part020SupportExplicit : Finset ℕ :=
  ([13577] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block128Part020 : ℚ :=
  (2880233265625 : ℚ) / 21235093853328118272

def SurrogateDiagonalTailChunk000Sub001Block128Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13577
    = surrogateDiagTailX0RatChunk000Sub001Block128Part020

theorem surrogateDiagonalTailChunk000Sub001Block128Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block128Part020CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block128Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block128Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block128Part020CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block128Part020SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block128Part020] using hcert

def TailChunk000Sub001Block128Part021SupportExplicit : Finset ℕ :=
  ([13578] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block128Part021 : ℚ :=
  (72394476889 : ℚ) / 34835483079475200

def SurrogateDiagonalTailChunk000Sub001Block128Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13578
    = surrogateDiagTailX0RatChunk000Sub001Block128Part021

theorem surrogateDiagonalTailChunk000Sub001Block128Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block128Part021CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block128Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block128Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block128Part021CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block128Part021SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block128Part021] using hcert

def TailChunk000Sub001Block128Part022SupportExplicit : Finset ℕ :=
  ([13579] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block128Part022 : ℚ :=
  (1371466843925 : ℚ) / 9420440622589921536

def SurrogateDiagonalTailChunk000Sub001Block128Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13579
    = surrogateDiagTailX0RatChunk000Sub001Block128Part022

theorem surrogateDiagonalTailChunk000Sub001Block128Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block128Part022CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block128Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block128Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block128Part022CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block128Part022SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block128Part022] using hcert

def TailChunk000Sub001Block128Part023SupportExplicit : Finset ℕ :=
  ([13582] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block128Part023 : ℚ :=
  (1152942025 : ℚ) / 2126013154417362

def SurrogateDiagonalTailChunk000Sub001Block128Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13582
    = surrogateDiagTailX0RatChunk000Sub001Block128Part023

theorem surrogateDiagonalTailChunk000Sub001Block128Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block128Part023CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block128Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block128Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block128Part023CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block128Part023SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block128Part023] using hcert

def TailChunk000Sub001Block128Part024SupportExplicit : Finset ℕ :=
  ([13585] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block128Part024 : ℚ :=
  (4137879659 : ℚ) / 11147354585432064

def SurrogateDiagonalTailChunk000Sub001Block128Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13585
    = surrogateDiagTailX0RatChunk000Sub001Block128Part024

theorem surrogateDiagonalTailChunk000Sub001Block128Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block128Part024CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block128Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block128Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block128Part024CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block128Part024SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block128Part024] using hcert

def surrogateDiagonalTailChunk000Sub001Block128HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block128Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block128Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block128Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block128Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block128Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block128Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block128Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block128Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block128Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block128Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block128Head : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block128Part000
    + surrogateDiagTailX0RatChunk000Sub001Block128Part001
    + surrogateDiagTailX0RatChunk000Sub001Block128Part002
    + surrogateDiagTailX0RatChunk000Sub001Block128Part003
    + surrogateDiagTailX0RatChunk000Sub001Block128Part004
    + surrogateDiagTailX0RatChunk000Sub001Block128Part005
    + surrogateDiagTailX0RatChunk000Sub001Block128Part006
    + surrogateDiagTailX0RatChunk000Sub001Block128Part007
    + surrogateDiagTailX0RatChunk000Sub001Block128Part008
    + surrogateDiagTailX0RatChunk000Sub001Block128Part009

def surrogateDiagonalTailChunk000Sub001Block128MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block128Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block128Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block128Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block128Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block128Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block128Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block128Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block128Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block128Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block128Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block128Mid : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block128Part010
    + surrogateDiagTailX0RatChunk000Sub001Block128Part011
    + surrogateDiagTailX0RatChunk000Sub001Block128Part012
    + surrogateDiagTailX0RatChunk000Sub001Block128Part013
    + surrogateDiagTailX0RatChunk000Sub001Block128Part014
    + surrogateDiagTailX0RatChunk000Sub001Block128Part015
    + surrogateDiagTailX0RatChunk000Sub001Block128Part016
    + surrogateDiagTailX0RatChunk000Sub001Block128Part017
    + surrogateDiagTailX0RatChunk000Sub001Block128Part018
    + surrogateDiagTailX0RatChunk000Sub001Block128Part019

def surrogateDiagonalTailChunk000Sub001Block128TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block128Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block128Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block128Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block128Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block128Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block128Tail : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block128Part020
    + surrogateDiagTailX0RatChunk000Sub001Block128Part021
    + surrogateDiagTailX0RatChunk000Sub001Block128Part022
    + surrogateDiagTailX0RatChunk000Sub001Block128Part023
    + surrogateDiagTailX0RatChunk000Sub001Block128Part024

def surrogateDiagonalTailChunk000Sub001Block128Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub001Block128HeadSum X0
    + surrogateDiagonalTailChunk000Sub001Block128MidSum X0
    + surrogateDiagonalTailChunk000Sub001Block128TailSum X0

def surrogateDiagTailX0RatChunk000Sub001Block128 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block128Part000
    + surrogateDiagTailX0RatChunk000Sub001Block128Part001
    + surrogateDiagTailX0RatChunk000Sub001Block128Part002
    + surrogateDiagTailX0RatChunk000Sub001Block128Part003
    + surrogateDiagTailX0RatChunk000Sub001Block128Part004
    + surrogateDiagTailX0RatChunk000Sub001Block128Part005
    + surrogateDiagTailX0RatChunk000Sub001Block128Part006
    + surrogateDiagTailX0RatChunk000Sub001Block128Part007
    + surrogateDiagTailX0RatChunk000Sub001Block128Part008
    + surrogateDiagTailX0RatChunk000Sub001Block128Part009
    + surrogateDiagTailX0RatChunk000Sub001Block128Part010
    + surrogateDiagTailX0RatChunk000Sub001Block128Part011
    + surrogateDiagTailX0RatChunk000Sub001Block128Part012
    + surrogateDiagTailX0RatChunk000Sub001Block128Part013
    + surrogateDiagTailX0RatChunk000Sub001Block128Part014
    + surrogateDiagTailX0RatChunk000Sub001Block128Part015
    + surrogateDiagTailX0RatChunk000Sub001Block128Part016
    + surrogateDiagTailX0RatChunk000Sub001Block128Part017
    + surrogateDiagTailX0RatChunk000Sub001Block128Part018
    + surrogateDiagTailX0RatChunk000Sub001Block128Part019
    + surrogateDiagTailX0RatChunk000Sub001Block128Part020
    + surrogateDiagTailX0RatChunk000Sub001Block128Part021
    + surrogateDiagTailX0RatChunk000Sub001Block128Part022
    + surrogateDiagTailX0RatChunk000Sub001Block128Part023
    + surrogateDiagTailX0RatChunk000Sub001Block128Part024

theorem surrogateDiagTailX0RatChunk000Sub001Block128_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk000Sub001Block128Head + surrogateDiagTailX0RatChunk000Sub001Block128Mid + surrogateDiagTailX0RatChunk000Sub001Block128Tail =
      surrogateDiagTailX0RatChunk000Sub001Block128 := by
  unfold surrogateDiagTailX0RatChunk000Sub001Block128Head surrogateDiagTailX0RatChunk000Sub001Block128Mid surrogateDiagTailX0RatChunk000Sub001Block128Tail surrogateDiagTailX0RatChunk000Sub001Block128
  ring

def SurrogateDiagonalTailChunk000Sub001Block128HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block128HeadSum X0 = surrogateDiagTailX0RatChunk000Sub001Block128Head

def SurrogateDiagonalTailChunk000Sub001Block128MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block128MidSum X0 = surrogateDiagTailX0RatChunk000Sub001Block128Mid

def SurrogateDiagonalTailChunk000Sub001Block128TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block128TailSum X0 = surrogateDiagTailX0RatChunk000Sub001Block128Tail

theorem surrogateDiagonalTailChunk000Sub001Block128_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk000Sub001Block128HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk000Sub001Block128MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk000Sub001Block128TailCertificateAt X0) :
    surrogateDiagonalTailChunk000Sub001Block128Sum X0 = surrogateDiagTailX0RatChunk000Sub001Block128 := by
  unfold SurrogateDiagonalTailChunk000Sub001Block128HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk000Sub001Block128MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk000Sub001Block128TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk000Sub001Block128Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk000Sub001Block128_eq_head_add_mid_add_tail

/-- Block 129 covers tail-support indices [8225,8250) and q from 13586 to 13623. -/

def TailChunk000Sub001Block129Part000SupportExplicit : Finset ℕ :=
  ([13586] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block129Part000 : ℚ :=
  (721013265625 : ℚ) / 1330324460588339712

def SurrogateDiagonalTailChunk000Sub001Block129Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13586
    = surrogateDiagTailX0RatChunk000Sub001Block129Part000

theorem surrogateDiagonalTailChunk000Sub001Block129Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block129Part000CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block129Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block129Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block129Part000CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block129Part000SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block129Part000] using hcert

def TailChunk000Sub001Block129Part001SupportExplicit : Finset ℕ :=
  ([13587] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block129Part001 : ℚ :=
  (2049293865725 : ℚ) / 4514939336053269504

def SurrogateDiagonalTailChunk000Sub001Block129Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13587
    = surrogateDiagTailX0RatChunk000Sub001Block129Part001

theorem surrogateDiagonalTailChunk000Sub001Block129Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block129Part001CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block129Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block129Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block129Part001CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block129Part001SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block129Part001] using hcert

def TailChunk000Sub001Block129Part002SupportExplicit : Finset ℕ :=
  ([13589] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block129Part002 : ℚ :=
  (114495457925 : ℚ) / 811907259769037376

def SurrogateDiagonalTailChunk000Sub001Block129Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13589
    = surrogateDiagTailX0RatChunk000Sub001Block129Part002

theorem surrogateDiagonalTailChunk000Sub001Block129Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block129Part002CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block129Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block129Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block129Part002CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block129Part002SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block129Part002] using hcert

def TailChunk000Sub001Block129Part003SupportExplicit : Finset ℕ :=
  ([13591] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block129Part003 : ℚ :=
  (4617882025 : ℚ) / 34116516220466322

def SurrogateDiagonalTailChunk000Sub001Block129Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13591
    = surrogateDiagTailX0RatChunk000Sub001Block129Part003

theorem surrogateDiagonalTailChunk000Sub001Block129Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block129Part003CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block129Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block129Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block129Part003CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block129Part003SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block129Part003] using hcert

def TailChunk000Sub001Block129Part004SupportExplicit : Finset ℕ :=
  ([13593] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block129Part004 : ℚ :=
  (794971757775 : ℚ) / 2305210557270376448

def SurrogateDiagonalTailChunk000Sub001Block129Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13593
    = surrogateDiagTailX0RatChunk000Sub001Block129Part004

theorem surrogateDiagonalTailChunk000Sub001Block129Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block129Part004CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block129Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block129Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block129Part004CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block129Part004SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block129Part004] using hcert

def TailChunk000Sub001Block129Part005SupportExplicit : Finset ℕ :=
  ([13594] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block129Part005 : ℚ :=
  (96535954087 : ℚ) / 114756894965635200

def SurrogateDiagonalTailChunk000Sub001Block129Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13594
    = surrogateDiagTailX0RatChunk000Sub001Block129Part005

theorem surrogateDiagonalTailChunk000Sub001Block129Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block129Part005CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block129Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block129Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block129Part005CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block129Part005SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block129Part005] using hcert

def TailChunk000Sub001Block129Part006SupportExplicit : Finset ℕ :=
  ([13595] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block129Part006 : ℚ :=
  (7851233393725 : ℚ) / 34935312609757513728

def SurrogateDiagonalTailChunk000Sub001Block129Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13595
    = surrogateDiagTailX0RatChunk000Sub001Block129Part006

theorem surrogateDiagonalTailChunk000Sub001Block129Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block129Part006CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block129Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block129Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block129Part006CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block129Part006SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block129Part006] using hcert

def TailChunk000Sub001Block129Part007SupportExplicit : Finset ℕ :=
  ([13597] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block129Part007 : ℚ :=
  (2888725140625 : ℚ) / 21360503781931244832

def SurrogateDiagonalTailChunk000Sub001Block129Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13597
    = surrogateDiagTailX0RatChunk000Sub001Block129Part007

theorem surrogateDiagonalTailChunk000Sub001Block129Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block129Part007CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block129Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block129Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block129Part007CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block129Part007SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block129Part007] using hcert

def TailChunk000Sub001Block129Part008SupportExplicit : Finset ℕ :=
  ([13598] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block129Part008 : ℚ :=
  (6001865675 : ℚ) / 8911485571446144

def SurrogateDiagonalTailChunk000Sub001Block129Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13598
    = surrogateDiagTailX0RatChunk000Sub001Block129Part008

theorem surrogateDiagonalTailChunk000Sub001Block129Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block129Part008CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block129Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block129Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block129Part008CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block129Part008SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block129Part008] using hcert

def TailChunk000Sub001Block129Part009SupportExplicit : Finset ℕ :=
  ([13601] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block129Part009 : ℚ :=
  (8052942379975 : ℚ) / 37795468053938208768

def SurrogateDiagonalTailChunk000Sub001Block129Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13601
    = surrogateDiagTailX0RatChunk000Sub001Block129Part009

theorem surrogateDiagonalTailChunk000Sub001Block129Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block129Part009CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block129Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block129Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block129Part009CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block129Part009SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block129Part009] using hcert

def TailChunk000Sub001Block129Part010SupportExplicit : Finset ℕ :=
  ([13602] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block129Part010 : ℚ :=
  (200686608575 : ℚ) / 131854961616859536

def SurrogateDiagonalTailChunk000Sub001Block129Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13602
    = surrogateDiagTailX0RatChunk000Sub001Block129Part010

theorem surrogateDiagonalTailChunk000Sub001Block129Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block129Part010CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block129Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block129Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block129Part010CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block129Part010SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block129Part010] using hcert

def TailChunk000Sub001Block129Part011SupportExplicit : Finset ℕ :=
  ([13603] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block129Part011 : ℚ :=
  (446936221723 : ℚ) / 3148500376336435200

def SurrogateDiagonalTailChunk000Sub001Block129Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13603
    = surrogateDiagTailX0RatChunk000Sub001Block129Part011

theorem surrogateDiagonalTailChunk000Sub001Block129Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block129Part011CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block129Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block129Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block129Part011CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block129Part011SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block129Part011] using hcert

def TailChunk000Sub001Block129Part012SupportExplicit : Finset ℕ :=
  ([13605] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block129Part012 : ℚ :=
  (3644849454475 : ℚ) / 6900802490816299008

def SurrogateDiagonalTailChunk000Sub001Block129Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13605
    = surrogateDiagTailX0RatChunk000Sub001Block129Part012

theorem surrogateDiagonalTailChunk000Sub001Block129Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block129Part012CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block129Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block129Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block129Part012CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block129Part012SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block129Part012] using hcert

def TailChunk000Sub001Block129Part013SupportExplicit : Finset ℕ :=
  ([13606] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block129Part013 : ℚ :=
  (723137640625 : ℚ) / 1338176435506757202

def SurrogateDiagonalTailChunk000Sub001Block129Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13606
    = surrogateDiagTailX0RatChunk000Sub001Block129Part013

theorem surrogateDiagonalTailChunk000Sub001Block129Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block129Part013CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block129Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block129Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block129Part013CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block129Part013SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block129Part013] using hcert

def TailChunk000Sub001Block129Part014SupportExplicit : Finset ℕ :=
  ([13607] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block129Part014 : ℚ :=
  (131182608101 : ℚ) / 778107279809894400

def SurrogateDiagonalTailChunk000Sub001Block129Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13607
    = surrogateDiagTailX0RatChunk000Sub001Block129Part014

theorem surrogateDiagonalTailChunk000Sub001Block129Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block129Part014CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block129Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block129Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block129Part014CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block129Part014SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block129Part014] using hcert

def TailChunk000Sub001Block129Part015SupportExplicit : Finset ℕ :=
  ([13609] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block129Part015 : ℚ :=
  (13667167883 : ℚ) / 93179061686420100

def SurrogateDiagonalTailChunk000Sub001Block129Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13609
    = surrogateDiagTailX0RatChunk000Sub001Block129Part015

theorem surrogateDiagonalTailChunk000Sub001Block129Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block129Part015CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block129Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block129Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block129Part015CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block129Part015SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block129Part015] using hcert

def TailChunk000Sub001Block129Part016SupportExplicit : Finset ℕ :=
  ([13610] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block129Part016 : ℚ :=
  (43961326487 : ℚ) / 43797815859609600

def SurrogateDiagonalTailChunk000Sub001Block129Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13610
    = surrogateDiagTailX0RatChunk000Sub001Block129Part016

theorem surrogateDiagonalTailChunk000Sub001Block129Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block129Part016CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block129Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block129Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block129Part016CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block129Part016SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block129Part016] using hcert

def TailChunk000Sub001Block129Part017SupportExplicit : Finset ℕ :=
  ([13611] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block129Part017 : ℚ :=
  (78558385825 : ℚ) / 209778418969214976

def SurrogateDiagonalTailChunk000Sub001Block129Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13611
    = surrogateDiagTailX0RatChunk000Sub001Block129Part017

theorem surrogateDiagonalTailChunk000Sub001Block129Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block129Part017CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block129Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block129Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block129Part017CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block129Part017SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block129Part017] using hcert

def TailChunk000Sub001Block129Part018SupportExplicit : Finset ℕ :=
  ([13613] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block129Part018 : ℚ :=
  (2895527640625 : ℚ) / 21461231005088392992

def SurrogateDiagonalTailChunk000Sub001Block129Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13613
    = surrogateDiagTailX0RatChunk000Sub001Block129Part018

theorem surrogateDiagonalTailChunk000Sub001Block129Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block129Part018CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block129Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block129Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block129Part018CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block129Part018SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block129Part018] using hcert

def TailChunk000Sub001Block129Part019SupportExplicit : Finset ℕ :=
  ([13614] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block129Part019 : ℚ :=
  (804163535975 : ℚ) / 529284342560891904

def SurrogateDiagonalTailChunk000Sub001Block129Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13614
    = surrogateDiagTailX0RatChunk000Sub001Block129Part019

theorem surrogateDiagonalTailChunk000Sub001Block129Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block129Part019CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block129Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block129Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block129Part019CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block129Part019SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block129Part019] using hcert

def TailChunk000Sub001Block129Part020SupportExplicit : Finset ℕ :=
  ([13615] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block129Part020 : ℚ :=
  (667835606425 : ℚ) / 2089085519018852352

def SurrogateDiagonalTailChunk000Sub001Block129Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13615
    = surrogateDiagTailX0RatChunk000Sub001Block129Part020

theorem surrogateDiagonalTailChunk000Sub001Block129Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block129Part020CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block129Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block129Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block129Part020CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block129Part020SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block129Part020] using hcert

def TailChunk000Sub001Block129Part021SupportExplicit : Finset ℕ :=
  ([13618] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block129Part021 : ℚ :=
  (102308258599 : ℚ) / 145895114964355200

def SurrogateDiagonalTailChunk000Sub001Block129Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13618
    = surrogateDiagTailX0RatChunk000Sub001Block129Part021

theorem surrogateDiagonalTailChunk000Sub001Block129Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block129Part021CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block129Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block129Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block129Part021CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block129Part021SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block129Part021] using hcert

def TailChunk000Sub001Block129Part022SupportExplicit : Finset ℕ :=
  ([13619] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block129Part022 : ℚ :=
  (2898080640625 : ℚ) / 21499095404042560722

def SurrogateDiagonalTailChunk000Sub001Block129Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13619
    = surrogateDiagTailX0RatChunk000Sub001Block129Part022

theorem surrogateDiagonalTailChunk000Sub001Block129Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block129Part022CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block129Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block129Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block129Part022CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block129Part022SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block129Part022] using hcert

def TailChunk000Sub001Block129Part023SupportExplicit : Finset ℕ :=
  ([13621] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block129Part023 : ℚ :=
  (2791697401375 : ℚ) / 19630895144519073792

def SurrogateDiagonalTailChunk000Sub001Block129Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13621
    = surrogateDiagTailX0RatChunk000Sub001Block129Part023

theorem surrogateDiagonalTailChunk000Sub001Block129Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block129Part023CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block129Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block129Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block129Part023CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block129Part023SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block129Part023] using hcert

def TailChunk000Sub001Block129Part024SupportExplicit : Finset ℕ :=
  ([13623] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block129Part024 : ℚ :=
  (4730306654575 : ℚ) / 13475493850031474688

def SurrogateDiagonalTailChunk000Sub001Block129Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13623
    = surrogateDiagTailX0RatChunk000Sub001Block129Part024

theorem surrogateDiagonalTailChunk000Sub001Block129Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block129Part024CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block129Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block129Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block129Part024CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block129Part024SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block129Part024] using hcert

def surrogateDiagonalTailChunk000Sub001Block129HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block129Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block129Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block129Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block129Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block129Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block129Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block129Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block129Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block129Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block129Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block129Head : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block129Part000
    + surrogateDiagTailX0RatChunk000Sub001Block129Part001
    + surrogateDiagTailX0RatChunk000Sub001Block129Part002
    + surrogateDiagTailX0RatChunk000Sub001Block129Part003
    + surrogateDiagTailX0RatChunk000Sub001Block129Part004
    + surrogateDiagTailX0RatChunk000Sub001Block129Part005
    + surrogateDiagTailX0RatChunk000Sub001Block129Part006
    + surrogateDiagTailX0RatChunk000Sub001Block129Part007
    + surrogateDiagTailX0RatChunk000Sub001Block129Part008
    + surrogateDiagTailX0RatChunk000Sub001Block129Part009

def surrogateDiagonalTailChunk000Sub001Block129MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block129Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block129Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block129Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block129Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block129Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block129Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block129Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block129Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block129Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block129Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block129Mid : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block129Part010
    + surrogateDiagTailX0RatChunk000Sub001Block129Part011
    + surrogateDiagTailX0RatChunk000Sub001Block129Part012
    + surrogateDiagTailX0RatChunk000Sub001Block129Part013
    + surrogateDiagTailX0RatChunk000Sub001Block129Part014
    + surrogateDiagTailX0RatChunk000Sub001Block129Part015
    + surrogateDiagTailX0RatChunk000Sub001Block129Part016
    + surrogateDiagTailX0RatChunk000Sub001Block129Part017
    + surrogateDiagTailX0RatChunk000Sub001Block129Part018
    + surrogateDiagTailX0RatChunk000Sub001Block129Part019

def surrogateDiagonalTailChunk000Sub001Block129TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block129Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block129Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block129Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block129Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block129Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block129Tail : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block129Part020
    + surrogateDiagTailX0RatChunk000Sub001Block129Part021
    + surrogateDiagTailX0RatChunk000Sub001Block129Part022
    + surrogateDiagTailX0RatChunk000Sub001Block129Part023
    + surrogateDiagTailX0RatChunk000Sub001Block129Part024

def surrogateDiagonalTailChunk000Sub001Block129Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub001Block129HeadSum X0
    + surrogateDiagonalTailChunk000Sub001Block129MidSum X0
    + surrogateDiagonalTailChunk000Sub001Block129TailSum X0

def surrogateDiagTailX0RatChunk000Sub001Block129 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block129Part000
    + surrogateDiagTailX0RatChunk000Sub001Block129Part001
    + surrogateDiagTailX0RatChunk000Sub001Block129Part002
    + surrogateDiagTailX0RatChunk000Sub001Block129Part003
    + surrogateDiagTailX0RatChunk000Sub001Block129Part004
    + surrogateDiagTailX0RatChunk000Sub001Block129Part005
    + surrogateDiagTailX0RatChunk000Sub001Block129Part006
    + surrogateDiagTailX0RatChunk000Sub001Block129Part007
    + surrogateDiagTailX0RatChunk000Sub001Block129Part008
    + surrogateDiagTailX0RatChunk000Sub001Block129Part009
    + surrogateDiagTailX0RatChunk000Sub001Block129Part010
    + surrogateDiagTailX0RatChunk000Sub001Block129Part011
    + surrogateDiagTailX0RatChunk000Sub001Block129Part012
    + surrogateDiagTailX0RatChunk000Sub001Block129Part013
    + surrogateDiagTailX0RatChunk000Sub001Block129Part014
    + surrogateDiagTailX0RatChunk000Sub001Block129Part015
    + surrogateDiagTailX0RatChunk000Sub001Block129Part016
    + surrogateDiagTailX0RatChunk000Sub001Block129Part017
    + surrogateDiagTailX0RatChunk000Sub001Block129Part018
    + surrogateDiagTailX0RatChunk000Sub001Block129Part019
    + surrogateDiagTailX0RatChunk000Sub001Block129Part020
    + surrogateDiagTailX0RatChunk000Sub001Block129Part021
    + surrogateDiagTailX0RatChunk000Sub001Block129Part022
    + surrogateDiagTailX0RatChunk000Sub001Block129Part023
    + surrogateDiagTailX0RatChunk000Sub001Block129Part024

theorem surrogateDiagTailX0RatChunk000Sub001Block129_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk000Sub001Block129Head + surrogateDiagTailX0RatChunk000Sub001Block129Mid + surrogateDiagTailX0RatChunk000Sub001Block129Tail =
      surrogateDiagTailX0RatChunk000Sub001Block129 := by
  unfold surrogateDiagTailX0RatChunk000Sub001Block129Head surrogateDiagTailX0RatChunk000Sub001Block129Mid surrogateDiagTailX0RatChunk000Sub001Block129Tail surrogateDiagTailX0RatChunk000Sub001Block129
  ring

def SurrogateDiagonalTailChunk000Sub001Block129HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block129HeadSum X0 = surrogateDiagTailX0RatChunk000Sub001Block129Head

def SurrogateDiagonalTailChunk000Sub001Block129MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block129MidSum X0 = surrogateDiagTailX0RatChunk000Sub001Block129Mid

def SurrogateDiagonalTailChunk000Sub001Block129TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block129TailSum X0 = surrogateDiagTailX0RatChunk000Sub001Block129Tail

theorem surrogateDiagonalTailChunk000Sub001Block129_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk000Sub001Block129HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk000Sub001Block129MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk000Sub001Block129TailCertificateAt X0) :
    surrogateDiagonalTailChunk000Sub001Block129Sum X0 = surrogateDiagTailX0RatChunk000Sub001Block129 := by
  unfold SurrogateDiagonalTailChunk000Sub001Block129HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk000Sub001Block129MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk000Sub001Block129TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk000Sub001Block129Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk000Sub001Block129_eq_head_add_mid_add_tail

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

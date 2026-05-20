import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0TailPilot25

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

open scoped BigOperators

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

/- Generated direct-term certificate blocks for tail chunk 000, subchunk 000, blocks [28,29). -/

/- Block 028 covers tail-support indices [700,725) and q from 1202 to 1241. -/

def TailChunk000Sub000Block028Part000SupportExplicit : Finset ℕ :=
  ([1202] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block028Part000 : ℚ :=
  (4695613 : ℚ) / 7501500000

def SurrogateDiagonalTailChunk000Sub000Block028Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1202
    = surrogateDiagTailX0RatChunk000Sub000Block028Part000

theorem surrogateDiagonalTailChunk000Sub000Block028Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block028Part000CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block028Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block028Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block028Part000CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block028Part000SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block028Part000] using hcert

def TailChunk000Sub000Block028Part001SupportExplicit : Finset ℕ :=
  ([1203] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block028Part001 : ℚ :=
  (626679193 : ℚ) / 2560512000000

def SurrogateDiagonalTailChunk000Sub000Block028Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1203
    = surrogateDiagTailX0RatChunk000Sub000Block028Part001

theorem surrogateDiagonalTailChunk000Sub000Block028Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block028Part001CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block028Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block028Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block028Part001CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block028Part001SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block028Part001] using hcert

def TailChunk000Sub000Block028Part002SupportExplicit : Finset ℕ :=
  ([1205] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block028Part002 : ℚ :=
  (38544761 : ℚ) / 235976785920

def SurrogateDiagonalTailChunk000Sub000Block028Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1205
    = surrogateDiagTailX0RatChunk000Sub000Block028Part002

theorem surrogateDiagonalTailChunk000Sub000Block028Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block028Part002CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block028Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block028Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block028Part002CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block028Part002SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block028Part002] using hcert

def TailChunk000Sub000Block028Part003SupportExplicit : Finset ℕ :=
  ([1207] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block028Part003 : ℚ :=
  (96802877 : ℚ) / 1124167188480

def SurrogateDiagonalTailChunk000Sub000Block028Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1207
    = surrogateDiagTailX0RatChunk000Sub000Block028Part003

theorem surrogateDiagonalTailChunk000Sub000Block028Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block028Part003CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block028Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block028Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block028Part003CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block028Part003SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block028Part003] using hcert

def TailChunk000Sub000Block028Part004SupportExplicit : Finset ℕ :=
  ([1209] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block028Part004 : ℚ :=
  (1812480203 : ℚ) / 5375846154240

def SurrogateDiagonalTailChunk000Sub000Block028Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1209
    = surrogateDiagTailX0RatChunk000Sub000Block028Part004

theorem surrogateDiagonalTailChunk000Sub000Block028Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block028Part004CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block028Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block028Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block028Part004CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block028Part004SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block028Part004] using hcert

def TailChunk000Sub000Block028Part005SupportExplicit : Finset ℕ :=
  ([1211] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block028Part005 : ℚ :=
  (42124439225 : ℚ) / 315139715500032

def SurrogateDiagonalTailChunk000Sub000Block028Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1211
    = surrogateDiagTailX0RatChunk000Sub000Block028Part005

theorem surrogateDiagonalTailChunk000Sub000Block028Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block028Part005CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block028Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block028Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block028Part005CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block028Part005SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block028Part005] using hcert

def TailChunk000Sub000Block028Part006SupportExplicit : Finset ℕ :=
  ([1213] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block028Part006 : ℚ :=
  (183810772325 : ℚ) / 2697785043038784

def SurrogateDiagonalTailChunk000Sub000Block028Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1213
    = surrogateDiagTailX0RatChunk000Sub000Block028Part006

theorem surrogateDiagonalTailChunk000Sub000Block028Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block028Part006CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block028Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block028Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block028Part006CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block028Part006SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block028Part006] using hcert

def TailChunk000Sub000Block028Part007SupportExplicit : Finset ℕ :=
  ([1214] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block028Part007 : ℚ :=
  (45991646425 : ℚ) / 84305782594962

def SurrogateDiagonalTailChunk000Sub000Block028Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1214
    = surrogateDiagTailX0RatChunk000Sub000Block028Part007

theorem surrogateDiagonalTailChunk000Sub000Block028Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block028Part007CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block028Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block028Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block028Part007CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block028Part007SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block028Part007] using hcert

def TailChunk000Sub000Block028Part008SupportExplicit : Finset ℕ :=
  ([1217] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block028Part008 : ℚ :=
  (9738160175 : ℚ) / 143872424411136

def SurrogateDiagonalTailChunk000Sub000Block028Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1217
    = surrogateDiagTailX0RatChunk000Sub000Block028Part008

theorem surrogateDiagonalTailChunk000Sub000Block028Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block028Part008CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block028Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block028Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block028Part008CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block028Part008SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block028Part008] using hcert

def TailChunk000Sub000Block028Part009SupportExplicit : Finset ℕ :=
  ([1218] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block028Part009 : ℚ :=
  (102769976875 : ℚ) / 31870139793408

def SurrogateDiagonalTailChunk000Sub000Block028Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1218
    = surrogateDiagTailX0RatChunk000Sub000Block028Part009

theorem surrogateDiagonalTailChunk000Sub000Block028Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block028Part009CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block028Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block028Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block028Part009CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block028Part009SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block028Part009] using hcert

def TailChunk000Sub000Block028Part010SupportExplicit : Finset ℕ :=
  ([1219] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block028Part010 : ℚ :=
  (87342286225 : ℚ) / 1070707797299712

def SurrogateDiagonalTailChunk000Sub000Block028Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1219
    = surrogateDiagTailX0RatChunk000Sub000Block028Part010

theorem surrogateDiagonalTailChunk000Sub000Block028Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block028Part010CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block028Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block028Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block028Part010CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block028Part010SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block028Part010] using hcert

def TailChunk000Sub000Block028Part011SupportExplicit : Finset ℕ :=
  ([1221] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block028Part011 : ℚ :=
  (440933291 : ℚ) / 1343961538560

def SurrogateDiagonalTailChunk000Sub000Block028Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1221
    = surrogateDiagTailX0RatChunk000Sub000Block028Part011

theorem surrogateDiagonalTailChunk000Sub000Block028Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block028Part011CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block028Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block028Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block028Part011CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block028Part011SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block028Part011] using hcert

def TailChunk000Sub000Block028Part012SupportExplicit : Finset ℕ :=
  ([1222] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block028Part012 : ℚ :=
  (169021552525 : ℚ) / 232157741303808

def SurrogateDiagonalTailChunk000Sub000Block028Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1222
    = surrogateDiagTailX0RatChunk000Sub000Block028Part012

theorem surrogateDiagonalTailChunk000Sub000Block028Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block028Part012CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block028Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block028Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block028Part012CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block028Part012SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block028Part012] using hcert

def TailChunk000Sub000Block028Part013SupportExplicit : Finset ℕ :=
  ([1223] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block028Part013 : ℚ :=
  (186853945325 : ℚ) / 2787928855096164

def SurrogateDiagonalTailChunk000Sub000Block028Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1223
    = surrogateDiagTailX0RatChunk000Sub000Block028Part013

theorem surrogateDiagonalTailChunk000Sub000Block028Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block028Part013CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block028Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block028Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block028Part013CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block028Part013SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block028Part013] using hcert

def TailChunk000Sub000Block028Part014SupportExplicit : Finset ℕ :=
  ([1226] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block028Part014 : ℚ :=
  (46905365425 : ℚ) / 87694540360992

def SurrogateDiagonalTailChunk000Sub000Block028Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1226
    = surrogateDiagTailX0RatChunk000Sub000Block028Part014

theorem surrogateDiagonalTailChunk000Sub000Block028Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block028Part014CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block028Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block028Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block028Part014CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block028Part014SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block028Part014] using hcert

def TailChunk000Sub000Block028Part015SupportExplicit : Finset ℕ :=
  ([1227] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block028Part015 : ℚ :=
  (16687975 : ℚ) / 73894035456

def SurrogateDiagonalTailChunk000Sub000Block028Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1227
    = surrogateDiagTailX0RatChunk000Sub000Block028Part015

theorem surrogateDiagonalTailChunk000Sub000Block028Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block028Part015CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block028Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block028Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block028Part015CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block028Part015SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block028Part015] using hcert

def TailChunk000Sub000Block028Part016SupportExplicit : Finset ℕ :=
  ([1229] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block028Part016 : ℚ :=
  (188691841925 : ℚ) / 2843088184256064

def SurrogateDiagonalTailChunk000Sub000Block028Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1229
    = surrogateDiagTailX0RatChunk000Sub000Block028Part016

theorem surrogateDiagonalTailChunk000Sub000Block028Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block028Part016CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block028Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block028Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block028Part016CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block028Part016SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block028Part016] using hcert

def TailChunk000Sub000Block028Part017SupportExplicit : Finset ℕ :=
  ([1230] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block028Part017 : ℚ :=
  (493298111 : ℚ) / 131098214400

def SurrogateDiagonalTailChunk000Sub000Block028Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1230
    = surrogateDiagTailX0RatChunk000Sub000Block028Part017

theorem surrogateDiagonalTailChunk000Sub000Block028Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block028Part017CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block028Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block028Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block028Part017CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block028Part017SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block028Part017] using hcert

def TailChunk000Sub000Block028Part018SupportExplicit : Finset ℕ :=
  ([1231] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block028Part018 : ℚ :=
  (7572258917 : ℚ) / 114466209164100

def SurrogateDiagonalTailChunk000Sub000Block028Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1231
    = surrogateDiagTailX0RatChunk000Sub000Block028Part018

theorem surrogateDiagonalTailChunk000Sub000Block028Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block028Part018CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block028Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block028Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block028Part018CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block028Part018SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block028Part018] using hcert

def TailChunk000Sub000Block028Part019SupportExplicit : Finset ℕ :=
  ([1234] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block028Part019 : ℚ :=
  (47519504425 : ℚ) / 90009783316992

def SurrogateDiagonalTailChunk000Sub000Block028Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1234
    = surrogateDiagTailX0RatChunk000Sub000Block028Part019

theorem surrogateDiagonalTailChunk000Sub000Block028Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block028Part019CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block028Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block028Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block028Part019CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block028Part019SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block028Part019] using hcert

def TailChunk000Sub000Block028Part020SupportExplicit : Finset ℕ :=
  ([1235] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block028Part020 : ℚ :=
  (133534334525 : ℚ) / 696709661589504

def SurrogateDiagonalTailChunk000Sub000Block028Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1235
    = surrogateDiagTailX0RatChunk000Sub000Block028Part020

theorem surrogateDiagonalTailChunk000Sub000Block028Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block028Part020CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block028Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block028Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block028Part020CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block028Part020SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block028Part020] using hcert

def TailChunk000Sub000Block028Part021SupportExplicit : Finset ℕ :=
  ([1237] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block028Part021 : ℚ :=
  (191156362325 : ℚ) / 2917902299287104

def SurrogateDiagonalTailChunk000Sub000Block028Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1237
    = surrogateDiagTailX0RatChunk000Sub000Block028Part021

theorem surrogateDiagonalTailChunk000Sub000Block028Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block028Part021CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block028Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block028Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block028Part021CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block028Part021SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block028Part021] using hcert

def TailChunk000Sub000Block028Part022SupportExplicit : Finset ℕ :=
  ([1238] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block028Part022 : ℚ :=
  (47828071825 : ℚ) / 91184446852722

def SurrogateDiagonalTailChunk000Sub000Block028Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1238
    = surrogateDiagTailX0RatChunk000Sub000Block028Part022

theorem surrogateDiagonalTailChunk000Sub000Block028Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block028Part022CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block028Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block028Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block028Part022CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block028Part022SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block028Part022] using hcert

def TailChunk000Sub000Block028Part023SupportExplicit : Finset ℕ :=
  ([1239] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block028Part023 : ℚ :=
  (216501742675 : ℚ) / 586764482070528

def SurrogateDiagonalTailChunk000Sub000Block028Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1239
    = surrogateDiagTailX0RatChunk000Sub000Block028Part023

theorem surrogateDiagonalTailChunk000Sub000Block028Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block028Part023CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block028Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block028Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block028Part023CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block028Part023SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block028Part023] using hcert

def TailChunk000Sub000Block028Part024SupportExplicit : Finset ℕ :=
  ([1241] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block028Part024 : ℚ :=
  (119171225275 : ℚ) / 1467964389851136

def SurrogateDiagonalTailChunk000Sub000Block028Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1241
    = surrogateDiagTailX0RatChunk000Sub000Block028Part024

theorem surrogateDiagonalTailChunk000Sub000Block028Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block028Part024CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block028Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block028Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block028Part024CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block028Part024SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block028Part024] using hcert

def surrogateDiagonalTailChunk000Sub000Block028HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block028Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block028Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block028Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block028Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block028Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block028Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block028Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block028Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block028Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block028Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block028Head : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block028Part000
    + surrogateDiagTailX0RatChunk000Sub000Block028Part001
    + surrogateDiagTailX0RatChunk000Sub000Block028Part002
    + surrogateDiagTailX0RatChunk000Sub000Block028Part003
    + surrogateDiagTailX0RatChunk000Sub000Block028Part004
    + surrogateDiagTailX0RatChunk000Sub000Block028Part005
    + surrogateDiagTailX0RatChunk000Sub000Block028Part006
    + surrogateDiagTailX0RatChunk000Sub000Block028Part007
    + surrogateDiagTailX0RatChunk000Sub000Block028Part008
    + surrogateDiagTailX0RatChunk000Sub000Block028Part009

def surrogateDiagonalTailChunk000Sub000Block028MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block028Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block028Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block028Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block028Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block028Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block028Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block028Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block028Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block028Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block028Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block028Mid : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block028Part010
    + surrogateDiagTailX0RatChunk000Sub000Block028Part011
    + surrogateDiagTailX0RatChunk000Sub000Block028Part012
    + surrogateDiagTailX0RatChunk000Sub000Block028Part013
    + surrogateDiagTailX0RatChunk000Sub000Block028Part014
    + surrogateDiagTailX0RatChunk000Sub000Block028Part015
    + surrogateDiagTailX0RatChunk000Sub000Block028Part016
    + surrogateDiagTailX0RatChunk000Sub000Block028Part017
    + surrogateDiagTailX0RatChunk000Sub000Block028Part018
    + surrogateDiagTailX0RatChunk000Sub000Block028Part019

def surrogateDiagonalTailChunk000Sub000Block028TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block028Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block028Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block028Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block028Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block028Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block028Tail : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block028Part020
    + surrogateDiagTailX0RatChunk000Sub000Block028Part021
    + surrogateDiagTailX0RatChunk000Sub000Block028Part022
    + surrogateDiagTailX0RatChunk000Sub000Block028Part023
    + surrogateDiagTailX0RatChunk000Sub000Block028Part024

def surrogateDiagonalTailChunk000Sub000Block028Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub000Block028HeadSum X0
    + surrogateDiagonalTailChunk000Sub000Block028MidSum X0
    + surrogateDiagonalTailChunk000Sub000Block028TailSum X0

def surrogateDiagTailX0RatChunk000Sub000Block028 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block028Part000
    + surrogateDiagTailX0RatChunk000Sub000Block028Part001
    + surrogateDiagTailX0RatChunk000Sub000Block028Part002
    + surrogateDiagTailX0RatChunk000Sub000Block028Part003
    + surrogateDiagTailX0RatChunk000Sub000Block028Part004
    + surrogateDiagTailX0RatChunk000Sub000Block028Part005
    + surrogateDiagTailX0RatChunk000Sub000Block028Part006
    + surrogateDiagTailX0RatChunk000Sub000Block028Part007
    + surrogateDiagTailX0RatChunk000Sub000Block028Part008
    + surrogateDiagTailX0RatChunk000Sub000Block028Part009
    + surrogateDiagTailX0RatChunk000Sub000Block028Part010
    + surrogateDiagTailX0RatChunk000Sub000Block028Part011
    + surrogateDiagTailX0RatChunk000Sub000Block028Part012
    + surrogateDiagTailX0RatChunk000Sub000Block028Part013
    + surrogateDiagTailX0RatChunk000Sub000Block028Part014
    + surrogateDiagTailX0RatChunk000Sub000Block028Part015
    + surrogateDiagTailX0RatChunk000Sub000Block028Part016
    + surrogateDiagTailX0RatChunk000Sub000Block028Part017
    + surrogateDiagTailX0RatChunk000Sub000Block028Part018
    + surrogateDiagTailX0RatChunk000Sub000Block028Part019
    + surrogateDiagTailX0RatChunk000Sub000Block028Part020
    + surrogateDiagTailX0RatChunk000Sub000Block028Part021
    + surrogateDiagTailX0RatChunk000Sub000Block028Part022
    + surrogateDiagTailX0RatChunk000Sub000Block028Part023
    + surrogateDiagTailX0RatChunk000Sub000Block028Part024

theorem surrogateDiagTailX0RatChunk000Sub000Block028_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk000Sub000Block028Head + surrogateDiagTailX0RatChunk000Sub000Block028Mid + surrogateDiagTailX0RatChunk000Sub000Block028Tail =
      surrogateDiagTailX0RatChunk000Sub000Block028 := by
  unfold surrogateDiagTailX0RatChunk000Sub000Block028Head surrogateDiagTailX0RatChunk000Sub000Block028Mid surrogateDiagTailX0RatChunk000Sub000Block028Tail surrogateDiagTailX0RatChunk000Sub000Block028
  ring

def SurrogateDiagonalTailChunk000Sub000Block028HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block028HeadSum X0 = surrogateDiagTailX0RatChunk000Sub000Block028Head

def SurrogateDiagonalTailChunk000Sub000Block028MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block028MidSum X0 = surrogateDiagTailX0RatChunk000Sub000Block028Mid

def SurrogateDiagonalTailChunk000Sub000Block028TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block028TailSum X0 = surrogateDiagTailX0RatChunk000Sub000Block028Tail

theorem surrogateDiagonalTailChunk000Sub000Block028_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk000Sub000Block028HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk000Sub000Block028MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk000Sub000Block028TailCertificateAt X0) :
    surrogateDiagonalTailChunk000Sub000Block028Sum X0 = surrogateDiagTailX0RatChunk000Sub000Block028 := by
  unfold SurrogateDiagonalTailChunk000Sub000Block028HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk000Sub000Block028MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk000Sub000Block028TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk000Sub000Block028Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk000Sub000Block028_eq_head_add_mid_add_tail

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

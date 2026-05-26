import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0TailPilot25

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

open scoped BigOperators

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

/- Generated direct-term certificate blocks for tail chunk 001, subchunk 001, blocks [10,20). -/

/-- Block 010 covers tail-support indices [15250,15275) and q from 25134 to 25174. -/

def TailChunk001Sub001Block010Part000SupportExplicit : Finset ℕ :=
  ([25134] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block010Part000 : ℚ :=
  (55975250031 : ℚ) / 144940485746022400

def SurrogateDiagonalTailChunk001Sub001Block010Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25134
    = surrogateDiagTailX0RatChunk001Sub001Block010Part000

theorem surrogateDiagonalTailChunk001Sub001Block010Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block010Part000CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block010Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block010Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block010Part000CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block010Part000SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block010Part000] using hcert

def TailChunk001Sub001Block010Part001SupportExplicit : Finset ℕ :=
  ([25135] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block010Part001 : ℚ :=
  (85303744447 : ℚ) / 1107098305843691520

def SurrogateDiagonalTailChunk001Sub001Block010Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25135
    = surrogateDiagTailX0RatChunk001Sub001Block010Part001

theorem surrogateDiagonalTailChunk001Sub001Block010Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block010Part001CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block010Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block010Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block010Part001CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block010Part001SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block010Part001] using hcert

def TailChunk001Sub001Block010Part002SupportExplicit : Finset ℕ :=
  ([25138] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block010Part002 : ℚ :=
  (2468433765625 : ℚ) / 15596658234768732672

def SurrogateDiagonalTailChunk001Sub001Block010Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25138
    = surrogateDiagTailX0RatChunk001Sub001Block010Part002

theorem surrogateDiagonalTailChunk001Sub001Block010Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block010Part002CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block010Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block010Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block010Part002CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block010Part002SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block010Part002] using hcert

def TailChunk001Sub001Block010Part003SupportExplicit : Finset ℕ :=
  ([25139] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block010Part003 : ℚ :=
  (18189708449375 : ℚ) / 416464646253290578944

def SurrogateDiagonalTailChunk001Sub001Block010Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25139
    = surrogateDiagTailX0RatChunk001Sub001Block010Part003

theorem surrogateDiagonalTailChunk001Sub001Block010Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block010Part003CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block010Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block010Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block010Part003CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block010Part003SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block010Part003] using hcert

def TailChunk001Sub001Block010Part004SupportExplicit : Finset ℕ :=
  ([25141] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block010Part004 : ℚ :=
  (296977911311 : ℚ) / 6974963515760400000

def SurrogateDiagonalTailChunk001Sub001Block010Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25141
    = surrogateDiagTailX0RatChunk001Sub001Block010Part004

theorem surrogateDiagonalTailChunk001Sub001Block010Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block010Part004CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block010Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block010Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block010Part004CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block010Part004SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block010Part004] using hcert

def TailChunk001Sub001Block010Part005SupportExplicit : Finset ℕ :=
  ([25142] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block010Part005 : ℚ :=
  (4318208519825 : ℚ) / 22575134843252941824

def SurrogateDiagonalTailChunk001Sub001Block010Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25142
    = surrogateDiagTailX0RatChunk001Sub001Block010Part005

theorem surrogateDiagonalTailChunk001Sub001Block010Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block010Part005CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block010Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block010Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block010Part005CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block010Part005SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block010Part005] using hcert

def TailChunk001Sub001Block010Part006SupportExplicit : Finset ℕ :=
  ([25145] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block010Part006 : ℚ :=
  (2993290261625 : ℚ) / 45230524611373142016

def SurrogateDiagonalTailChunk001Sub001Block010Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25145
    = surrogateDiagTailX0RatChunk001Sub001Block010Part006

theorem surrogateDiagonalTailChunk001Sub001Block010Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block010Part006CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block010Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block010Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block010Part006CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block010Part006SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block010Part006] using hcert

def TailChunk001Sub001Block010Part007SupportExplicit : Finset ℕ :=
  ([25147] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block010Part007 : ℚ :=
  (9880806390625 : ℚ) / 249943882948315906482

def SurrogateDiagonalTailChunk001Sub001Block010Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25147
    = surrogateDiagTailX0RatChunk001Sub001Block010Part007

theorem surrogateDiagonalTailChunk001Sub001Block010Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block010Part007CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block010Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block010Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block010Part007CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block010Part007SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block010Part007] using hcert

def TailChunk001Sub001Block010Part008SupportExplicit : Finset ℕ :=
  ([25149] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block010Part008 : ℚ :=
  (112785969729 : ℚ) / 1205899158272000000

def SurrogateDiagonalTailChunk001Sub001Block010Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25149
    = surrogateDiagTailX0RatChunk001Sub001Block010Part008

theorem surrogateDiagonalTailChunk001Sub001Block010Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block010Part008CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block010Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block010Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block010Part008CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block010Part008SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block010Part008] using hcert

def TailChunk001Sub001Block010Part009SupportExplicit : Finset ℕ :=
  ([25151] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block010Part009 : ℚ :=
  (3225823523525 : ℚ) / 59942473915230093312

def SurrogateDiagonalTailChunk001Sub001Block010Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25151
    = surrogateDiagTailX0RatChunk001Sub001Block010Part009

theorem surrogateDiagonalTailChunk001Sub001Block010Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block010Part009CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block010Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block010Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block010Part009CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block010Part009SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block010Part009] using hcert

def TailChunk001Sub001Block010Part010SupportExplicit : Finset ℕ :=
  ([25153] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block010Part010 : ℚ :=
  (9885522015625 : ℚ) / 250182521320586084352

def SurrogateDiagonalTailChunk001Sub001Block010Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25153
    = surrogateDiagTailX0RatChunk001Sub001Block010Part010

theorem surrogateDiagonalTailChunk001Sub001Block010Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block010Part010CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block010Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block010Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block010Part010CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block010Part010SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block010Part010] using hcert

def TailChunk001Sub001Block010Part011SupportExplicit : Finset ℕ :=
  ([25154] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block010Part011 : ℚ :=
  (2471577015625 : ℚ) / 15636407582536630272

def SurrogateDiagonalTailChunk001Sub001Block010Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25154
    = surrogateDiagTailX0RatChunk001Sub001Block010Part011

theorem surrogateDiagonalTailChunk001Sub001Block010Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block010Part011CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block010Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block010Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block010Part011CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block010Part011SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block010Part011] using hcert

def TailChunk001Sub001Block010Part012SupportExplicit : Finset ℕ :=
  ([25157] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block010Part012 : ℚ :=
  (26393810651 : ℚ) / 546288112447654464

def SurrogateDiagonalTailChunk001Sub001Block010Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25157
    = surrogateDiagTailX0RatChunk001Sub001Block010Part012

theorem surrogateDiagonalTailChunk001Sub001Block010Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block010Part012CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block010Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block010Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block010Part012CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block010Part012SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block010Part012] using hcert

def TailChunk001Sub001Block010Part013SupportExplicit : Finset ℕ :=
  ([25158] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block010Part013 : ℚ :=
  (1767453226625 : ℚ) / 3315328624689030144

def SurrogateDiagonalTailChunk001Sub001Block010Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25158
    = surrogateDiagTailX0RatChunk001Sub001Block010Part013

theorem surrogateDiagonalTailChunk001Sub001Block010Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block010Part013CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block010Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block010Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block010Part013CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block010Part013SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block010Part013] using hcert

def TailChunk001Sub001Block010Part014SupportExplicit : Finset ℕ :=
  ([25159] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block010Part014 : ℚ :=
  (171837468563 : ℚ) / 4231074835261900800

def SurrogateDiagonalTailChunk001Sub001Block010Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25159
    = surrogateDiagTailX0RatChunk001Sub001Block010Part014

theorem surrogateDiagonalTailChunk001Sub001Block010Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block010Part014CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block010Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block010Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block010Part014CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block010Part014SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block010Part014] using hcert

def TailChunk001Sub001Block010Part015SupportExplicit : Finset ℕ :=
  ([25161] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block010Part015 : ℚ :=
  (17581873161325 : ℚ) / 197863767336499840128

def SurrogateDiagonalTailChunk001Sub001Block010Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25161
    = surrogateDiagTailX0RatChunk001Sub001Block010Part015

theorem surrogateDiagonalTailChunk001Sub001Block010Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block010Part015CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block010Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block010Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block010Part015CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block010Part015SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block010Part015] using hcert

def TailChunk001Sub001Block010Part016SupportExplicit : Finset ℕ :=
  ([25162] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block010Part016 : ℚ :=
  (254861091725 : ℚ) / 1446057799490592288

def SurrogateDiagonalTailChunk001Sub001Block010Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25162
    = surrogateDiagTailX0RatChunk001Sub001Block010Part016

theorem surrogateDiagonalTailChunk001Sub001Block010Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block010Part016CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block010Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block010Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block010Part016CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block010Part016SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block010Part016] using hcert

def TailChunk001Sub001Block010Part017SupportExplicit : Finset ℕ :=
  ([25163] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block010Part017 : ℚ :=
  (9893383890625 : ℚ) / 250580631631072403442

def SurrogateDiagonalTailChunk001Sub001Block010Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25163
    = surrogateDiagTailX0RatChunk001Sub001Block010Part017

theorem surrogateDiagonalTailChunk001Sub001Block010Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block010Part017CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block010Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block010Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block010Part017CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block010Part017SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block010Part017] using hcert

def TailChunk001Sub001Block010Part018SupportExplicit : Finset ℕ :=
  ([25165] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block010Part018 : ℚ :=
  (2084176880525 : ℚ) / 24497800480504184832

def SurrogateDiagonalTailChunk001Sub001Block010Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25165
    = surrogateDiagTailX0RatChunk001Sub001Block010Part018

theorem surrogateDiagonalTailChunk001Sub001Block010Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block010Part018CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block010Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block010Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block010Part018CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block010Part018SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block010Part018] using hcert

def TailChunk001Sub001Block010Part019SupportExplicit : Finset ℕ :=
  ([25166] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block010Part019 : ℚ :=
  (2473935765625 : ℚ) / 15666269417115561522

def SurrogateDiagonalTailChunk001Sub001Block010Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25166
    = surrogateDiagTailX0RatChunk001Sub001Block010Part019

theorem surrogateDiagonalTailChunk001Sub001Block010Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block010Part019CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block010Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block010Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block010Part019CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block010Part019SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block010Part019] using hcert

def TailChunk001Sub001Block010Part020SupportExplicit : Finset ℕ :=
  ([25167] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block010Part020 : ℚ :=
  (17590260161125 : ℚ) / 198052591149707839488

def SurrogateDiagonalTailChunk001Sub001Block010Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25167
    = surrogateDiagTailX0RatChunk001Sub001Block010Part020

theorem surrogateDiagonalTailChunk001Sub001Block010Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block010Part020CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block010Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block010Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block010Part020CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block010Part020SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block010Part020] using hcert

def TailChunk001Sub001Block010Part021SupportExplicit : Finset ℕ :=
  ([25169] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block010Part021 : ℚ :=
  (9898102515625 : ℚ) / 250819725764241334272

def SurrogateDiagonalTailChunk001Sub001Block010Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25169
    = surrogateDiagTailX0RatChunk001Sub001Block010Part021

theorem surrogateDiagonalTailChunk001Sub001Block010Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block010Part021CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block010Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block010Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block010Part021CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block010Part021SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block010Part021] using hcert

def TailChunk001Sub001Block010Part022SupportExplicit : Finset ℕ :=
  ([25170] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block010Part022 : ℚ :=
  (1054114714575 : ℚ) / 1683610504066072576

def SurrogateDiagonalTailChunk001Sub001Block010Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25170
    = surrogateDiagTailX0RatChunk001Sub001Block010Part022

theorem surrogateDiagonalTailChunk001Sub001Block010Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block010Part022CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block010Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block010Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block010Part022CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block010Part022SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block010Part022] using hcert

def TailChunk001Sub001Block010Part023SupportExplicit : Finset ℕ :=
  ([25171] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block010Part023 : ℚ :=
  (15839481025 : ℚ) / 401439138908637042

def SurrogateDiagonalTailChunk001Sub001Block010Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25171
    = surrogateDiagTailX0RatChunk001Sub001Block010Part023

theorem surrogateDiagonalTailChunk001Sub001Block010Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block010Part023CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block010Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block010Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block010Part023CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block010Part023SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block010Part023] using hcert

def TailChunk001Sub001Block010Part024SupportExplicit : Finset ℕ :=
  ([25174] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block010Part024 : ℚ :=
  (31549814597 : ℚ) / 187081686103449600

def SurrogateDiagonalTailChunk001Sub001Block010Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25174
    = surrogateDiagTailX0RatChunk001Sub001Block010Part024

theorem surrogateDiagonalTailChunk001Sub001Block010Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block010Part024CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block010Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block010Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block010Part024CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block010Part024SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block010Part024] using hcert

def surrogateDiagonalTailChunk001Sub001Block010HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub001Block010Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block010Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block010Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block010Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block010Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block010Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block010Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block010Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block010Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block010Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub001Block010Head : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block010Part000
    + surrogateDiagTailX0RatChunk001Sub001Block010Part001
    + surrogateDiagTailX0RatChunk001Sub001Block010Part002
    + surrogateDiagTailX0RatChunk001Sub001Block010Part003
    + surrogateDiagTailX0RatChunk001Sub001Block010Part004
    + surrogateDiagTailX0RatChunk001Sub001Block010Part005
    + surrogateDiagTailX0RatChunk001Sub001Block010Part006
    + surrogateDiagTailX0RatChunk001Sub001Block010Part007
    + surrogateDiagTailX0RatChunk001Sub001Block010Part008
    + surrogateDiagTailX0RatChunk001Sub001Block010Part009

def surrogateDiagonalTailChunk001Sub001Block010MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub001Block010Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block010Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block010Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block010Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block010Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block010Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block010Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block010Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block010Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block010Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub001Block010Mid : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block010Part010
    + surrogateDiagTailX0RatChunk001Sub001Block010Part011
    + surrogateDiagTailX0RatChunk001Sub001Block010Part012
    + surrogateDiagTailX0RatChunk001Sub001Block010Part013
    + surrogateDiagTailX0RatChunk001Sub001Block010Part014
    + surrogateDiagTailX0RatChunk001Sub001Block010Part015
    + surrogateDiagTailX0RatChunk001Sub001Block010Part016
    + surrogateDiagTailX0RatChunk001Sub001Block010Part017
    + surrogateDiagTailX0RatChunk001Sub001Block010Part018
    + surrogateDiagTailX0RatChunk001Sub001Block010Part019

def surrogateDiagonalTailChunk001Sub001Block010TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub001Block010Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block010Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block010Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block010Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block010Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub001Block010Tail : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block010Part020
    + surrogateDiagTailX0RatChunk001Sub001Block010Part021
    + surrogateDiagTailX0RatChunk001Sub001Block010Part022
    + surrogateDiagTailX0RatChunk001Sub001Block010Part023
    + surrogateDiagTailX0RatChunk001Sub001Block010Part024

def surrogateDiagonalTailChunk001Sub001Block010Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk001Sub001Block010HeadSum X0
    + surrogateDiagonalTailChunk001Sub001Block010MidSum X0
    + surrogateDiagonalTailChunk001Sub001Block010TailSum X0

def surrogateDiagTailX0RatChunk001Sub001Block010 : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block010Part000
    + surrogateDiagTailX0RatChunk001Sub001Block010Part001
    + surrogateDiagTailX0RatChunk001Sub001Block010Part002
    + surrogateDiagTailX0RatChunk001Sub001Block010Part003
    + surrogateDiagTailX0RatChunk001Sub001Block010Part004
    + surrogateDiagTailX0RatChunk001Sub001Block010Part005
    + surrogateDiagTailX0RatChunk001Sub001Block010Part006
    + surrogateDiagTailX0RatChunk001Sub001Block010Part007
    + surrogateDiagTailX0RatChunk001Sub001Block010Part008
    + surrogateDiagTailX0RatChunk001Sub001Block010Part009
    + surrogateDiagTailX0RatChunk001Sub001Block010Part010
    + surrogateDiagTailX0RatChunk001Sub001Block010Part011
    + surrogateDiagTailX0RatChunk001Sub001Block010Part012
    + surrogateDiagTailX0RatChunk001Sub001Block010Part013
    + surrogateDiagTailX0RatChunk001Sub001Block010Part014
    + surrogateDiagTailX0RatChunk001Sub001Block010Part015
    + surrogateDiagTailX0RatChunk001Sub001Block010Part016
    + surrogateDiagTailX0RatChunk001Sub001Block010Part017
    + surrogateDiagTailX0RatChunk001Sub001Block010Part018
    + surrogateDiagTailX0RatChunk001Sub001Block010Part019
    + surrogateDiagTailX0RatChunk001Sub001Block010Part020
    + surrogateDiagTailX0RatChunk001Sub001Block010Part021
    + surrogateDiagTailX0RatChunk001Sub001Block010Part022
    + surrogateDiagTailX0RatChunk001Sub001Block010Part023
    + surrogateDiagTailX0RatChunk001Sub001Block010Part024

theorem surrogateDiagTailX0RatChunk001Sub001Block010_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk001Sub001Block010Head + surrogateDiagTailX0RatChunk001Sub001Block010Mid + surrogateDiagTailX0RatChunk001Sub001Block010Tail =
      surrogateDiagTailX0RatChunk001Sub001Block010 := by
  unfold surrogateDiagTailX0RatChunk001Sub001Block010Head surrogateDiagTailX0RatChunk001Sub001Block010Mid surrogateDiagTailX0RatChunk001Sub001Block010Tail surrogateDiagTailX0RatChunk001Sub001Block010
  ring

def SurrogateDiagonalTailChunk001Sub001Block010HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub001Block010HeadSum X0 = surrogateDiagTailX0RatChunk001Sub001Block010Head

def SurrogateDiagonalTailChunk001Sub001Block010MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub001Block010MidSum X0 = surrogateDiagTailX0RatChunk001Sub001Block010Mid

def SurrogateDiagonalTailChunk001Sub001Block010TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub001Block010TailSum X0 = surrogateDiagTailX0RatChunk001Sub001Block010Tail

theorem surrogateDiagonalTailChunk001Sub001Block010_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk001Sub001Block010HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk001Sub001Block010MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk001Sub001Block010TailCertificateAt X0) :
    surrogateDiagonalTailChunk001Sub001Block010Sum X0 = surrogateDiagTailX0RatChunk001Sub001Block010 := by
  unfold SurrogateDiagonalTailChunk001Sub001Block010HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk001Sub001Block010MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk001Sub001Block010TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk001Sub001Block010Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk001Sub001Block010_eq_head_add_mid_add_tail

/-- Block 011 covers tail-support indices [15275,15300) and q from 25177 to 25219. -/

def TailChunk001Sub001Block011Part000SupportExplicit : Finset ℕ :=
  ([25177] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block011Part000 : ℚ :=
  (353268718093 : ℚ) / 7862373139139788800

def SurrogateDiagonalTailChunk001Sub001Block011Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25177
    = surrogateDiagTailX0RatChunk001Sub001Block011Part000

theorem surrogateDiagonalTailChunk001Sub001Block011Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block011Part000CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block011Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block011Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block011Part000CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block011Part000SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block011Part000] using hcert

def TailChunk001Sub001Block011Part001SupportExplicit : Finset ℕ :=
  ([25178] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block011Part001 : ℚ :=
  (2476295640625 : ℚ) / 15696174003060156192

def SurrogateDiagonalTailChunk001Sub001Block011Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25178
    = surrogateDiagTailX0RatChunk001Sub001Block011Part001

theorem surrogateDiagonalTailChunk001Sub001Block011Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block011Part001CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block011Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block011Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block011Part001CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block011Part001SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block011Part001] using hcert

def TailChunk001Sub001Block011Part002SupportExplicit : Finset ℕ :=
  ([25179] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block011Part002 : ℚ :=
  (440668344709 : ℚ) / 2821674129437491200

def SurrogateDiagonalTailChunk001Sub001Block011Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25179
    = surrogateDiagTailX0RatChunk001Sub001Block011Part002

theorem surrogateDiagonalTailChunk001Sub001Block011Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block011Part002CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block011Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block011Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block011Part002CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block011Part002SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block011Part002] using hcert

def TailChunk001Sub001Block011Part003SupportExplicit : Finset ℕ :=
  ([25183] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block011Part003 : ℚ :=
  (9909117015625 : ℚ) / 251378277448618859922

def SurrogateDiagonalTailChunk001Sub001Block011Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25183
    = surrogateDiagTailX0RatChunk001Sub001Block011Part003

theorem surrogateDiagonalTailChunk001Sub001Block011Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block011Part003CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block011Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block011Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block011Part003CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block011Part003SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block011Part003] using hcert

def TailChunk001Sub001Block011Part004SupportExplicit : Finset ℕ :=
  ([25185] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block011Part004 : ℚ :=
  (1760672180075 : ℚ) / 10746233315905241088

def SurrogateDiagonalTailChunk001Sub001Block011Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25185
    = surrogateDiagTailX0RatChunk001Sub001Block011Part004

theorem surrogateDiagonalTailChunk001Sub001Block011Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block011Part004CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block011Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block011Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block011Part004CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block011Part004SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block011Part004] using hcert

def TailChunk001Sub001Block011Part005SupportExplicit : Finset ℕ :=
  ([25187] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block011Part005 : ℚ :=
  (38604231986425 : ℚ) / 948317971158669754368

def SurrogateDiagonalTailChunk001Sub001Block011Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25187
    = surrogateDiagTailX0RatChunk001Sub001Block011Part005

theorem surrogateDiagonalTailChunk001Sub001Block011Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block011Part005CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block011Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block011Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block011Part005CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block011Part005SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block011Part005] using hcert

def TailChunk001Sub001Block011Part006SupportExplicit : Finset ℕ :=
  ([25189] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block011Part006 : ℚ :=
  (9913839390625 : ℚ) / 251617942098463509792

def SurrogateDiagonalTailChunk001Sub001Block011Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25189
    = surrogateDiagTailX0RatChunk001Sub001Block011Part006

theorem surrogateDiagonalTailChunk001Sub001Block011Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block011Part006CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block011Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block011Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block011Part006CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block011Part006SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block011Part006] using hcert

def TailChunk001Sub001Block011Part007SupportExplicit : Finset ℕ :=
  ([25190] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block011Part007 : ℚ :=
  (23184757903 : ℚ) / 69193644115230720

def SurrogateDiagonalTailChunk001Sub001Block011Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25190
    = surrogateDiagTailX0RatChunk001Sub001Block011Part007

theorem surrogateDiagonalTailChunk001Sub001Block011Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block011Part007CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block011Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block011Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block011Part007CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block011Part007SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block011Part007] using hcert

def TailChunk001Sub001Block011Part008SupportExplicit : Finset ℕ :=
  ([25193] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block011Part008 : ℚ :=
  (564235194533 : ℚ) / 9505584609542553600

def SurrogateDiagonalTailChunk001Sub001Block011Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25193
    = surrogateDiagTailX0RatChunk001Sub001Block011Part008

theorem surrogateDiagonalTailChunk001Sub001Block011Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block011Part008CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block011Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block011Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block011Part008CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block011Part008SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block011Part008] using hcert

def TailChunk001Sub001Block011Part009SupportExplicit : Finset ℕ :=
  ([25194] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block011Part009 : ℚ :=
  (140233461625 : ℚ) / 237810231155884032

def SurrogateDiagonalTailChunk001Sub001Block011Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25194
    = surrogateDiagTailX0RatChunk001Sub001Block011Part009

theorem surrogateDiagonalTailChunk001Sub001Block011Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block011Part009CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block011Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block011Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block011Part009CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block011Part009SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block011Part009] using hcert

def TailChunk001Sub001Block011Part010SupportExplicit : Finset ℕ :=
  ([25195] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block011Part010 : ℚ :=
  (1586418390625 : ℚ) / 25773861722601641088

def SurrogateDiagonalTailChunk001Sub001Block011Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25195
    = surrogateDiagTailX0RatChunk001Sub001Block011Part010

theorem surrogateDiagonalTailChunk001Sub001Block011Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block011Part010CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block011Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block011Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block011Part010CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block011Part010SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block011Part010] using hcert

def TailChunk001Sub001Block011Part011SupportExplicit : Finset ℕ :=
  ([25197] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block011Part011 : ℚ :=
  (115937426975 : ℚ) / 1217385456376154112

def SurrogateDiagonalTailChunk001Sub001Block011Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25197
    = surrogateDiagTailX0RatChunk001Sub001Block011Part011

theorem surrogateDiagonalTailChunk001Sub001Block011Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block011Part011CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block011Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block011Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block011Part011CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block011Part011SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block011Part011] using hcert

def TailChunk001Sub001Block011Part012SupportExplicit : Finset ℕ :=
  ([25198] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block011Part012 : ℚ :=
  (4749946635425 : ℚ) / 28282997204902831104

def SurrogateDiagonalTailChunk001Sub001Block011Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25198
    = surrogateDiagTailX0RatChunk001Sub001Block011Part012

theorem surrogateDiagonalTailChunk001Sub001Block011Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block011Part012CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block011Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block011Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block011Part012CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block011Part012SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block011Part012] using hcert

def TailChunk001Sub001Block011Part013SupportExplicit : Finset ℕ :=
  ([25199] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block011Part013 : ℚ :=
  (5534398324375 : ℚ) / 136525195577950470144

def SurrogateDiagonalTailChunk001Sub001Block011Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25199
    = surrogateDiagTailX0RatChunk001Sub001Block011Part013

theorem surrogateDiagonalTailChunk001Sub001Block011Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block011Part013CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block011Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block011Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block011Part013CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block011Part013SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block011Part013] using hcert

def TailChunk001Sub001Block011Part014SupportExplicit : Finset ℕ :=
  ([25201] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block011Part014 : ℚ :=
  (93557410789 : ℚ) / 1750467428152934400

def SurrogateDiagonalTailChunk001Sub001Block011Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25201
    = surrogateDiagTailX0RatChunk001Sub001Block011Part014

theorem surrogateDiagonalTailChunk001Sub001Block011Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block011Part014CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block011Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block011Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block011Part014CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block011Part014SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block011Part014] using hcert

def TailChunk001Sub001Block011Part015SupportExplicit : Finset ℕ :=
  ([25202] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block011Part015 : ℚ :=
  (158785201 : ℚ) / 1008391141900800

def SurrogateDiagonalTailChunk001Sub001Block011Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25202
    = surrogateDiagTailX0RatChunk001Sub001Block011Part015

theorem surrogateDiagonalTailChunk001Sub001Block011Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block011Part015CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block011Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block011Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block011Part015CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block011Part015SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block011Part015] using hcert

def TailChunk001Sub001Block011Part016SupportExplicit : Finset ℕ :=
  ([25203] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block011Part016 : ℚ :=
  (662665769053 : ℚ) / 6888852855072000000

def SurrogateDiagonalTailChunk001Sub001Block011Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25203
    = surrogateDiagTailX0RatChunk001Sub001Block011Part016

theorem surrogateDiagonalTailChunk001Sub001Block011Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block011Part016CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block011Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block011Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block011Part016CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block011Part016SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block011Part016] using hcert

def TailChunk001Sub001Block011Part017SupportExplicit : Finset ℕ :=
  ([25206] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block011Part017 : ℚ :=
  (176424983197 : ℚ) / 497970934272000000

def SurrogateDiagonalTailChunk001Sub001Block011Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25206
    = surrogateDiagTailX0RatChunk001Sub001Block011Part017

theorem surrogateDiagonalTailChunk001Sub001Block011Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block011Part017CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block011Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block011Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block011Part017CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block011Part017SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block011Part017] using hcert

def TailChunk001Sub001Block011Part018SupportExplicit : Finset ℕ :=
  ([25207] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block011Part018 : ℚ :=
  (25799709794125 : ℚ) / 389935856817736777728

def SurrogateDiagonalTailChunk001Sub001Block011Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25207
    = surrogateDiagTailX0RatChunk001Sub001Block011Part018

theorem surrogateDiagonalTailChunk001Sub001Block011Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block011Part018CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block011Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block011Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block011Part018CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block011Part018SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block011Part018] using hcert

def TailChunk001Sub001Block011Part019SupportExplicit : Finset ℕ :=
  ([25210] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block011Part019 : ℚ :=
  (269967416659 : ℚ) / 1032592529306419200

def SurrogateDiagonalTailChunk001Sub001Block011Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25210
    = surrogateDiagTailX0RatChunk001Sub001Block011Part019

theorem surrogateDiagonalTailChunk001Sub001Block011Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block011Part019CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block011Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block011Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block011Part019CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block011Part019SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block011Part019] using hcert

def TailChunk001Sub001Block011Part020SupportExplicit : Finset ℕ :=
  ([25211] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block011Part020 : ℚ :=
  (8855600222125 : ℚ) / 197623966957510459392

def SurrogateDiagonalTailChunk001Sub001Block011Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25211
    = surrogateDiagTailX0RatChunk001Sub001Block011Part020

theorem surrogateDiagonalTailChunk001Sub001Block011Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block011Part020CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block011Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block011Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block011Part020CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block011Part020SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block011Part020] using hcert

def TailChunk001Sub001Block011Part021SupportExplicit : Finset ℕ :=
  ([25213] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block011Part021 : ℚ :=
  (35942600657425 : ℚ) / 811504580589094773888

def SurrogateDiagonalTailChunk001Sub001Block011Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25213
    = surrogateDiagTailX0RatChunk001Sub001Block011Part021

theorem surrogateDiagonalTailChunk001Sub001Block011Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block011Part021CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block011Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block011Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block011Part021CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block011Part021SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block011Part021] using hcert

def TailChunk001Sub001Block011Part022SupportExplicit : Finset ℕ :=
  ([25214] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block011Part022 : ℚ :=
  (76977621763 : ℚ) / 340190264448000000

def SurrogateDiagonalTailChunk001Sub001Block011Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25214
    = surrogateDiagTailX0RatChunk001Sub001Block011Part022

theorem surrogateDiagonalTailChunk001Sub001Block011Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block011Part022CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block011Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block011Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block011Part022CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block011Part022SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block011Part022] using hcert

def TailChunk001Sub001Block011Part023SupportExplicit : Finset ℕ :=
  ([25217] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block011Part023 : ℚ :=
  (776934553211 : ℚ) / 19224464129001000000

def SurrogateDiagonalTailChunk001Sub001Block011Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25217
    = surrogateDiagTailX0RatChunk001Sub001Block011Part023

theorem surrogateDiagonalTailChunk001Sub001Block011Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block011Part023CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block011Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block011Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block011Part023CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block011Part023SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block011Part023] using hcert

def TailChunk001Sub001Block011Part024SupportExplicit : Finset ℕ :=
  ([25219] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block011Part024 : ℚ :=
  (9937468140625 : ℚ) / 252818836957741826322

def SurrogateDiagonalTailChunk001Sub001Block011Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25219
    = surrogateDiagTailX0RatChunk001Sub001Block011Part024

theorem surrogateDiagonalTailChunk001Sub001Block011Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block011Part024CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block011Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block011Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block011Part024CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block011Part024SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block011Part024] using hcert

def surrogateDiagonalTailChunk001Sub001Block011HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub001Block011Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block011Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block011Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block011Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block011Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block011Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block011Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block011Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block011Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block011Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub001Block011Head : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block011Part000
    + surrogateDiagTailX0RatChunk001Sub001Block011Part001
    + surrogateDiagTailX0RatChunk001Sub001Block011Part002
    + surrogateDiagTailX0RatChunk001Sub001Block011Part003
    + surrogateDiagTailX0RatChunk001Sub001Block011Part004
    + surrogateDiagTailX0RatChunk001Sub001Block011Part005
    + surrogateDiagTailX0RatChunk001Sub001Block011Part006
    + surrogateDiagTailX0RatChunk001Sub001Block011Part007
    + surrogateDiagTailX0RatChunk001Sub001Block011Part008
    + surrogateDiagTailX0RatChunk001Sub001Block011Part009

def surrogateDiagonalTailChunk001Sub001Block011MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub001Block011Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block011Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block011Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block011Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block011Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block011Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block011Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block011Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block011Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block011Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub001Block011Mid : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block011Part010
    + surrogateDiagTailX0RatChunk001Sub001Block011Part011
    + surrogateDiagTailX0RatChunk001Sub001Block011Part012
    + surrogateDiagTailX0RatChunk001Sub001Block011Part013
    + surrogateDiagTailX0RatChunk001Sub001Block011Part014
    + surrogateDiagTailX0RatChunk001Sub001Block011Part015
    + surrogateDiagTailX0RatChunk001Sub001Block011Part016
    + surrogateDiagTailX0RatChunk001Sub001Block011Part017
    + surrogateDiagTailX0RatChunk001Sub001Block011Part018
    + surrogateDiagTailX0RatChunk001Sub001Block011Part019

def surrogateDiagonalTailChunk001Sub001Block011TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub001Block011Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block011Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block011Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block011Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block011Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub001Block011Tail : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block011Part020
    + surrogateDiagTailX0RatChunk001Sub001Block011Part021
    + surrogateDiagTailX0RatChunk001Sub001Block011Part022
    + surrogateDiagTailX0RatChunk001Sub001Block011Part023
    + surrogateDiagTailX0RatChunk001Sub001Block011Part024

def surrogateDiagonalTailChunk001Sub001Block011Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk001Sub001Block011HeadSum X0
    + surrogateDiagonalTailChunk001Sub001Block011MidSum X0
    + surrogateDiagonalTailChunk001Sub001Block011TailSum X0

def surrogateDiagTailX0RatChunk001Sub001Block011 : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block011Part000
    + surrogateDiagTailX0RatChunk001Sub001Block011Part001
    + surrogateDiagTailX0RatChunk001Sub001Block011Part002
    + surrogateDiagTailX0RatChunk001Sub001Block011Part003
    + surrogateDiagTailX0RatChunk001Sub001Block011Part004
    + surrogateDiagTailX0RatChunk001Sub001Block011Part005
    + surrogateDiagTailX0RatChunk001Sub001Block011Part006
    + surrogateDiagTailX0RatChunk001Sub001Block011Part007
    + surrogateDiagTailX0RatChunk001Sub001Block011Part008
    + surrogateDiagTailX0RatChunk001Sub001Block011Part009
    + surrogateDiagTailX0RatChunk001Sub001Block011Part010
    + surrogateDiagTailX0RatChunk001Sub001Block011Part011
    + surrogateDiagTailX0RatChunk001Sub001Block011Part012
    + surrogateDiagTailX0RatChunk001Sub001Block011Part013
    + surrogateDiagTailX0RatChunk001Sub001Block011Part014
    + surrogateDiagTailX0RatChunk001Sub001Block011Part015
    + surrogateDiagTailX0RatChunk001Sub001Block011Part016
    + surrogateDiagTailX0RatChunk001Sub001Block011Part017
    + surrogateDiagTailX0RatChunk001Sub001Block011Part018
    + surrogateDiagTailX0RatChunk001Sub001Block011Part019
    + surrogateDiagTailX0RatChunk001Sub001Block011Part020
    + surrogateDiagTailX0RatChunk001Sub001Block011Part021
    + surrogateDiagTailX0RatChunk001Sub001Block011Part022
    + surrogateDiagTailX0RatChunk001Sub001Block011Part023
    + surrogateDiagTailX0RatChunk001Sub001Block011Part024

theorem surrogateDiagTailX0RatChunk001Sub001Block011_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk001Sub001Block011Head + surrogateDiagTailX0RatChunk001Sub001Block011Mid + surrogateDiagTailX0RatChunk001Sub001Block011Tail =
      surrogateDiagTailX0RatChunk001Sub001Block011 := by
  unfold surrogateDiagTailX0RatChunk001Sub001Block011Head surrogateDiagTailX0RatChunk001Sub001Block011Mid surrogateDiagTailX0RatChunk001Sub001Block011Tail surrogateDiagTailX0RatChunk001Sub001Block011
  ring

def SurrogateDiagonalTailChunk001Sub001Block011HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub001Block011HeadSum X0 = surrogateDiagTailX0RatChunk001Sub001Block011Head

def SurrogateDiagonalTailChunk001Sub001Block011MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub001Block011MidSum X0 = surrogateDiagTailX0RatChunk001Sub001Block011Mid

def SurrogateDiagonalTailChunk001Sub001Block011TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub001Block011TailSum X0 = surrogateDiagTailX0RatChunk001Sub001Block011Tail

theorem surrogateDiagonalTailChunk001Sub001Block011_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk001Sub001Block011HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk001Sub001Block011MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk001Sub001Block011TailCertificateAt X0) :
    surrogateDiagonalTailChunk001Sub001Block011Sum X0 = surrogateDiagTailX0RatChunk001Sub001Block011 := by
  unfold SurrogateDiagonalTailChunk001Sub001Block011HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk001Sub001Block011MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk001Sub001Block011TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk001Sub001Block011Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk001Sub001Block011_eq_head_add_mid_add_tail

/-- Block 012 covers tail-support indices [15300,15325) and q from 25221 to 25262. -/

def TailChunk001Sub001Block012Part000SupportExplicit : Finset ℕ :=
  ([25221] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block012Part000 : ℚ :=
  (15004271029 : ℚ) / 119463247872000000

def SurrogateDiagonalTailChunk001Sub001Block012Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25221
    = surrogateDiagTailX0RatChunk001Sub001Block012Part000

theorem surrogateDiagonalTailChunk001Sub001Block012Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block012Part000CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block012Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block012Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block012Part000CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block012Part000SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block012Part000] using hcert

def TailChunk001Sub001Block012Part001SupportExplicit : Finset ℕ :=
  ([25222] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block012Part001 : ℚ :=
  (3975933025 : ℚ) / 25289904915999282

def SurrogateDiagonalTailChunk001Sub001Block012Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25222
    = surrogateDiagTailX0RatChunk001Sub001Block012Part001

theorem surrogateDiagonalTailChunk001Sub001Block012Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block012Part001CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block012Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block012Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block012Part001CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block012Part001SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block012Part001] using hcert

def TailChunk001Sub001Block012Part002SupportExplicit : Finset ℕ :=
  ([25223] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block012Part002 : ℚ :=
  (8291415481 : ℚ) / 172514387563917120

def SurrogateDiagonalTailChunk001Sub001Block012Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25223
    = surrogateDiagTailX0RatChunk001Sub001Block012Part002

theorem surrogateDiagonalTailChunk001Sub001Block012Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block012Part002CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block012Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block012Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block012Part002CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block012Part002SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block012Part002] using hcert

def TailChunk001Sub001Block012Part003SupportExplicit : Finset ℕ :=
  ([25226] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block012Part003 : ℚ :=
  (2485746390625 : ℚ) / 15816220676457928992

def SurrogateDiagonalTailChunk001Sub001Block012Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25226
    = surrogateDiagTailX0RatChunk001Sub001Block012Part003

theorem surrogateDiagonalTailChunk001Sub001Block012Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block012Part003CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block012Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block012Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block012Part003CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block012Part003SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block012Part003] using hcert

def TailChunk001Sub001Block012Part004SupportExplicit : Finset ℕ :=
  ([25229] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block012Part004 : ℚ :=
  (9945350640625 : ℚ) / 253220088851952352032

def SurrogateDiagonalTailChunk001Sub001Block012Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25229
    = surrogateDiagTailX0RatChunk001Sub001Block012Part004

theorem surrogateDiagonalTailChunk001Sub001Block012Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block012Part004CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block012Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block012Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block012Part004CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block012Part004SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block012Part004] using hcert

def TailChunk001Sub001Block012Part005SupportExplicit : Finset ℕ :=
  ([25231] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block012Part005 : ℚ :=
  (18323185394975 : ℚ) / 422600302027823529984

def SurrogateDiagonalTailChunk001Sub001Block012Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25231
    = surrogateDiagTailX0RatChunk001Sub001Block012Part005

theorem surrogateDiagonalTailChunk001Sub001Block012Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block012Part005CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block012Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block012Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block012Part005CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block012Part005SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block012Part005] using hcert

def TailChunk001Sub001Block012Part006SupportExplicit : Finset ℕ :=
  ([25233] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block012Part006 : ℚ :=
  (1280808736625 : ℚ) / 12039838229475385344

def SurrogateDiagonalTailChunk001Sub001Block012Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25233
    = surrogateDiagTailX0RatChunk001Sub001Block012Part006

theorem surrogateDiagonalTailChunk001Sub001Block012Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block012Part006CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block012Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block012Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block012Part006CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block012Part006SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block012Part006] using hcert

def TailChunk001Sub001Block012Part007SupportExplicit : Finset ℕ :=
  ([25234] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block012Part007 : ℚ :=
  (77653651201 : ℚ) / 340190264448000000

def SurrogateDiagonalTailChunk001Sub001Block012Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25234
    = surrogateDiagTailX0RatChunk001Sub001Block012Part007

theorem surrogateDiagonalTailChunk001Sub001Block012Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block012Part007CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block012Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block012Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block012Part007CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block012Part007SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block012Part007] using hcert

def TailChunk001Sub001Block012Part008SupportExplicit : Finset ℕ :=
  ([25237] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block012Part008 : ℚ :=
  (9951658890625 : ℚ) / 253541434101968715552

def SurrogateDiagonalTailChunk001Sub001Block012Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25237
    = surrogateDiagTailX0RatChunk001Sub001Block012Part008

theorem surrogateDiagonalTailChunk001Sub001Block012Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block012Part008CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block012Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block012Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block012Part008CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block012Part008SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block012Part008] using hcert

def TailChunk001Sub001Block012Part009SupportExplicit : Finset ℕ :=
  ([25238] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block012Part009 : ℚ :=
  (2488111890625 : ℚ) / 15846339631373044722

def SurrogateDiagonalTailChunk001Sub001Block012Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25238
    = surrogateDiagTailX0RatChunk001Sub001Block012Part009

theorem surrogateDiagonalTailChunk001Sub001Block012Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block012Part009CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block012Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block012Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block012Part009CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block012Part009SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block012Part009] using hcert

def TailChunk001Sub001Block012Part010SupportExplicit : Finset ℕ :=
  ([25239] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block012Part010 : ℚ :=
  (2814926096475 : ℚ) / 29971392911315176448

def SurrogateDiagonalTailChunk001Sub001Block012Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25239
    = surrogateDiagTailX0RatChunk001Sub001Block012Part010

theorem surrogateDiagonalTailChunk001Sub001Block012Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block012Part010CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block012Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block012Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block012Part010CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block012Part010SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block012Part010] using hcert

def TailChunk001Sub001Block012Part011SupportExplicit : Finset ℕ :=
  ([25241] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block012Part011 : ℚ :=
  (19023422762675 : ℚ) / 458758885375758993984

def SurrogateDiagonalTailChunk001Sub001Block012Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25241
    = surrogateDiagTailX0RatChunk001Sub001Block012Part011

theorem surrogateDiagonalTailChunk001Sub001Block012Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block012Part011CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block012Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block012Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block012Part011CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block012Part011SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block012Part011] using hcert

def TailChunk001Sub001Block012Part012SupportExplicit : Finset ℕ :=
  ([25242] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block012Part012 : ℚ :=
  (17387539297 : ℚ) / 26879230771200000

def SurrogateDiagonalTailChunk001Sub001Block012Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25242
    = surrogateDiagTailX0RatChunk001Sub001Block012Part012

theorem surrogateDiagonalTailChunk001Sub001Block012Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block012Part012CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block012Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block012Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block012Part012CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block012Part012SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block012Part012] using hcert

def TailChunk001Sub001Block012Part013SupportExplicit : Finset ℕ :=
  ([25243] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block012Part013 : ℚ :=
  (9956391390625 : ℚ) / 253782643678548627762

def SurrogateDiagonalTailChunk001Sub001Block012Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25243
    = surrogateDiagTailX0RatChunk001Sub001Block012Part013

theorem surrogateDiagonalTailChunk001Sub001Block012Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block012Part013CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block012Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block012Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block012Part013CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block012Part013SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block012Part013] using hcert

def TailChunk001Sub001Block012Part014SupportExplicit : Finset ℕ :=
  ([25246] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block012Part014 : ℚ :=
  (350682072079 : ℚ) / 1836110319450163200

def SurrogateDiagonalTailChunk001Sub001Block012Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25246
    = surrogateDiagTailX0RatChunk001Sub001Block012Part014

theorem surrogateDiagonalTailChunk001Sub001Block012Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block012Part014CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block012Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block012Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block012Part014CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block012Part014SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block012Part014] using hcert

def TailChunk001Sub001Block012Part015SupportExplicit : Finset ℕ :=
  ([25247] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block012Part015 : ℚ :=
  (9959547015625 : ℚ) / 253943545650785883282

def SurrogateDiagonalTailChunk001Sub001Block012Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25247
    = surrogateDiagTailX0RatChunk001Sub001Block012Part015

theorem surrogateDiagonalTailChunk001Sub001Block012Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block012Part015CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block012Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block012Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block012Part015CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block012Part015SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block012Part015] using hcert

def TailChunk001Sub001Block012Part016SupportExplicit : Finset ℕ :=
  ([25249] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block012Part016 : ℚ :=
  (30073802628025 : ℚ) / 547942201095208699008

def SurrogateDiagonalTailChunk001Sub001Block012Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25249
    = surrogateDiagTailX0RatChunk001Sub001Block012Part016

theorem surrogateDiagonalTailChunk001Sub001Block012Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block012Part016CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block012Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block012Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block012Part016CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block012Part016SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block012Part016] using hcert

def TailChunk001Sub001Block012Part017SupportExplicit : Finset ℕ :=
  ([25251] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block012Part017 : ℚ :=
  (85169794975 : ℚ) / 53432400368006240256

def SurrogateDiagonalTailChunk001Sub001Block012Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25251
    = surrogateDiagTailX0RatChunk001Sub001Block012Part017

theorem surrogateDiagonalTailChunk001Sub001Block012Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block012Part017CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block012Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block012Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block012Part017CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block012Part017SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block012Part017] using hcert

def TailChunk001Sub001Block012Part018SupportExplicit : Finset ℕ :=
  ([25253] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block012Part018 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block012Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25253
    = surrogateDiagTailX0RatChunk001Sub001Block012Part018

theorem surrogateDiagonalTailChunk001Sub001Block012Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block012Part018CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block012Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block012Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block012Part018CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block012Part018SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block012Part018] using hcert

def TailChunk001Sub001Block012Part019SupportExplicit : Finset ℕ :=
  ([25255] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block012Part019 : ℚ :=
  (4253751483 : ℚ) / 1110199606188800000

def SurrogateDiagonalTailChunk001Sub001Block012Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25255
    = surrogateDiagTailX0RatChunk001Sub001Block012Part019

theorem surrogateDiagonalTailChunk001Sub001Block012Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block012Part019CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block012Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block012Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block012Part019CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block012Part019SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block012Part019] using hcert

def TailChunk001Sub001Block012Part020SupportExplicit : Finset ℕ :=
  ([25257] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block012Part020 : ℚ :=
  (41675 : ℚ) / 13390735073867136

def SurrogateDiagonalTailChunk001Sub001Block012Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25257
    = surrogateDiagTailX0RatChunk001Sub001Block012Part020

theorem surrogateDiagonalTailChunk001Sub001Block012Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block012Part020CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block012Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block012Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block012Part020CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block012Part020SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block012Part020] using hcert

def TailChunk001Sub001Block012Part021SupportExplicit : Finset ℕ :=
  ([25258] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block012Part021 : ℚ :=
  (6305390575 : ℚ) / 4901052855456497664

def SurrogateDiagonalTailChunk001Sub001Block012Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25258
    = surrogateDiagTailX0RatChunk001Sub001Block012Part021

theorem surrogateDiagonalTailChunk001Sub001Block012Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block012Part021CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block012Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block012Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block012Part021CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block012Part021SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block012Part021] using hcert

def TailChunk001Sub001Block012Part022SupportExplicit : Finset ℕ :=
  ([25259] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block012Part022 : ℚ :=
  (33838460275 : ℚ) / 27487613130136879104

def SurrogateDiagonalTailChunk001Sub001Block012Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25259
    = surrogateDiagTailX0RatChunk001Sub001Block012Part022

theorem surrogateDiagonalTailChunk001Sub001Block012Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block012Part022CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block012Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block012Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block012Part022CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block012Part022SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block012Part022] using hcert

def TailChunk001Sub001Block012Part023SupportExplicit : Finset ℕ :=
  ([25261] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block012Part023 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block012Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25261
    = surrogateDiagTailX0RatChunk001Sub001Block012Part023

theorem surrogateDiagonalTailChunk001Sub001Block012Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block012Part023CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block012Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block012Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block012Part023CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block012Part023SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block012Part023] using hcert

def TailChunk001Sub001Block012Part024SupportExplicit : Finset ℕ :=
  ([25262] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block012Part024 : ℚ :=
  (17541495275 : ℚ) / 3548087936609943552

def SurrogateDiagonalTailChunk001Sub001Block012Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25262
    = surrogateDiagTailX0RatChunk001Sub001Block012Part024

theorem surrogateDiagonalTailChunk001Sub001Block012Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block012Part024CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block012Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block012Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block012Part024CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block012Part024SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block012Part024] using hcert

def surrogateDiagonalTailChunk001Sub001Block012HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub001Block012Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block012Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block012Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block012Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block012Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block012Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block012Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block012Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block012Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block012Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub001Block012Head : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block012Part000
    + surrogateDiagTailX0RatChunk001Sub001Block012Part001
    + surrogateDiagTailX0RatChunk001Sub001Block012Part002
    + surrogateDiagTailX0RatChunk001Sub001Block012Part003
    + surrogateDiagTailX0RatChunk001Sub001Block012Part004
    + surrogateDiagTailX0RatChunk001Sub001Block012Part005
    + surrogateDiagTailX0RatChunk001Sub001Block012Part006
    + surrogateDiagTailX0RatChunk001Sub001Block012Part007
    + surrogateDiagTailX0RatChunk001Sub001Block012Part008
    + surrogateDiagTailX0RatChunk001Sub001Block012Part009

def surrogateDiagonalTailChunk001Sub001Block012MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub001Block012Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block012Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block012Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block012Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block012Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block012Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block012Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block012Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block012Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block012Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub001Block012Mid : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block012Part010
    + surrogateDiagTailX0RatChunk001Sub001Block012Part011
    + surrogateDiagTailX0RatChunk001Sub001Block012Part012
    + surrogateDiagTailX0RatChunk001Sub001Block012Part013
    + surrogateDiagTailX0RatChunk001Sub001Block012Part014
    + surrogateDiagTailX0RatChunk001Sub001Block012Part015
    + surrogateDiagTailX0RatChunk001Sub001Block012Part016
    + surrogateDiagTailX0RatChunk001Sub001Block012Part017
    + surrogateDiagTailX0RatChunk001Sub001Block012Part018
    + surrogateDiagTailX0RatChunk001Sub001Block012Part019

def surrogateDiagonalTailChunk001Sub001Block012TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub001Block012Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block012Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block012Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block012Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block012Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub001Block012Tail : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block012Part020
    + surrogateDiagTailX0RatChunk001Sub001Block012Part021
    + surrogateDiagTailX0RatChunk001Sub001Block012Part022
    + surrogateDiagTailX0RatChunk001Sub001Block012Part023
    + surrogateDiagTailX0RatChunk001Sub001Block012Part024

def surrogateDiagonalTailChunk001Sub001Block012Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk001Sub001Block012HeadSum X0
    + surrogateDiagonalTailChunk001Sub001Block012MidSum X0
    + surrogateDiagonalTailChunk001Sub001Block012TailSum X0

def surrogateDiagTailX0RatChunk001Sub001Block012 : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block012Part000
    + surrogateDiagTailX0RatChunk001Sub001Block012Part001
    + surrogateDiagTailX0RatChunk001Sub001Block012Part002
    + surrogateDiagTailX0RatChunk001Sub001Block012Part003
    + surrogateDiagTailX0RatChunk001Sub001Block012Part004
    + surrogateDiagTailX0RatChunk001Sub001Block012Part005
    + surrogateDiagTailX0RatChunk001Sub001Block012Part006
    + surrogateDiagTailX0RatChunk001Sub001Block012Part007
    + surrogateDiagTailX0RatChunk001Sub001Block012Part008
    + surrogateDiagTailX0RatChunk001Sub001Block012Part009
    + surrogateDiagTailX0RatChunk001Sub001Block012Part010
    + surrogateDiagTailX0RatChunk001Sub001Block012Part011
    + surrogateDiagTailX0RatChunk001Sub001Block012Part012
    + surrogateDiagTailX0RatChunk001Sub001Block012Part013
    + surrogateDiagTailX0RatChunk001Sub001Block012Part014
    + surrogateDiagTailX0RatChunk001Sub001Block012Part015
    + surrogateDiagTailX0RatChunk001Sub001Block012Part016
    + surrogateDiagTailX0RatChunk001Sub001Block012Part017
    + surrogateDiagTailX0RatChunk001Sub001Block012Part018
    + surrogateDiagTailX0RatChunk001Sub001Block012Part019
    + surrogateDiagTailX0RatChunk001Sub001Block012Part020
    + surrogateDiagTailX0RatChunk001Sub001Block012Part021
    + surrogateDiagTailX0RatChunk001Sub001Block012Part022
    + surrogateDiagTailX0RatChunk001Sub001Block012Part023
    + surrogateDiagTailX0RatChunk001Sub001Block012Part024

theorem surrogateDiagTailX0RatChunk001Sub001Block012_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk001Sub001Block012Head + surrogateDiagTailX0RatChunk001Sub001Block012Mid + surrogateDiagTailX0RatChunk001Sub001Block012Tail =
      surrogateDiagTailX0RatChunk001Sub001Block012 := by
  unfold surrogateDiagTailX0RatChunk001Sub001Block012Head surrogateDiagTailX0RatChunk001Sub001Block012Mid surrogateDiagTailX0RatChunk001Sub001Block012Tail surrogateDiagTailX0RatChunk001Sub001Block012
  ring

def SurrogateDiagonalTailChunk001Sub001Block012HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub001Block012HeadSum X0 = surrogateDiagTailX0RatChunk001Sub001Block012Head

def SurrogateDiagonalTailChunk001Sub001Block012MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub001Block012MidSum X0 = surrogateDiagTailX0RatChunk001Sub001Block012Mid

def SurrogateDiagonalTailChunk001Sub001Block012TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub001Block012TailSum X0 = surrogateDiagTailX0RatChunk001Sub001Block012Tail

theorem surrogateDiagonalTailChunk001Sub001Block012_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk001Sub001Block012HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk001Sub001Block012MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk001Sub001Block012TailCertificateAt X0) :
    surrogateDiagonalTailChunk001Sub001Block012Sum X0 = surrogateDiagTailX0RatChunk001Sub001Block012 := by
  unfold SurrogateDiagonalTailChunk001Sub001Block012HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk001Sub001Block012MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk001Sub001Block012TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk001Sub001Block012Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk001Sub001Block012_eq_head_add_mid_add_tail

/-- Block 013 covers tail-support indices [15325,15350) and q from 25265 to 25305. -/

def TailChunk001Sub001Block013Part000SupportExplicit : Finset ℕ :=
  ([25265] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block013Part000 : ℚ :=
  (570376573 : ℚ) / 119039377335644160

def SurrogateDiagonalTailChunk001Sub001Block013Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25265
    = surrogateDiagTailX0RatChunk001Sub001Block013Part000

theorem surrogateDiagonalTailChunk001Sub001Block013Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block013Part000CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block013Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block013Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block013Part000CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block013Part000SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block013Part000] using hcert

def TailChunk001Sub001Block013Part001SupportExplicit : Finset ℕ :=
  ([25266] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block013Part001 : ℚ :=
  (4433525329 : ℚ) / 50273047928665920

def SurrogateDiagonalTailChunk001Sub001Block013Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25266
    = surrogateDiagTailX0RatChunk001Sub001Block013Part001

theorem surrogateDiagonalTailChunk001Sub001Block013Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block013Part001CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block013Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block013Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block013Part001CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block013Part001SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block013Part001] using hcert

def TailChunk001Sub001Block013Part002SupportExplicit : Finset ℕ :=
  ([25267] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block013Part002 : ℚ :=
  (6619478959 : ℚ) / 6948873309626572800

def SurrogateDiagonalTailChunk001Sub001Block013Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25267
    = surrogateDiagTailX0RatChunk001Sub001Block013Part002

theorem surrogateDiagonalTailChunk001Sub001Block013Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block013Part002CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block013Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block013Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block013Part002CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block013Part002SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block013Part002] using hcert

def TailChunk001Sub001Block013Part003SupportExplicit : Finset ℕ :=
  ([25269] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block013Part003 : ℚ :=
  (125025 : ℚ) / 40248614529976448

def SurrogateDiagonalTailChunk001Sub001Block013Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25269
    = surrogateDiagTailX0RatChunk001Sub001Block013Part003

theorem surrogateDiagonalTailChunk001Sub001Block013Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block013Part003CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block013Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block013Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block013Part003CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block013Part003SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block013Part003] using hcert

def TailChunk001Sub001Block013Part004SupportExplicit : Finset ℕ :=
  ([25271] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block013Part004 : ℚ :=
  (214488375775 : ℚ) / 908603406201610487808

def SurrogateDiagonalTailChunk001Sub001Block013Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25271
    = surrogateDiagTailX0RatChunk001Sub001Block013Part004

theorem surrogateDiagonalTailChunk001Sub001Block013Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block013Part004CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block013Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block013Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block013Part004CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block013Part004SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block013Part004] using hcert

def TailChunk001Sub001Block013Part005SupportExplicit : Finset ℕ :=
  ([25273] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block013Part005 : ℚ :=
  (12497396675 : ℚ) / 121082063428656536976

def SurrogateDiagonalTailChunk001Sub001Block013Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25273
    = surrogateDiagTailX0RatChunk001Sub001Block013Part005

theorem surrogateDiagonalTailChunk001Sub001Block013Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block013Part005CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block013Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block013Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block013Part005CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block013Part005SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block013Part005] using hcert

def TailChunk001Sub001Block013Part006SupportExplicit : Finset ℕ :=
  ([25274] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block013Part006 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block013Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25274
    = surrogateDiagTailX0RatChunk001Sub001Block013Part006

theorem surrogateDiagonalTailChunk001Sub001Block013Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block013Part006CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block013Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block013Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block013Part006CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block013Part006SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block013Part006] using hcert

def TailChunk001Sub001Block013Part007SupportExplicit : Finset ℕ :=
  ([25277] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block013Part007 : ℚ :=
  (1090634972275 : ℚ) / 449594486917338267648

def SurrogateDiagonalTailChunk001Sub001Block013Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25277
    = surrogateDiagTailX0RatChunk001Sub001Block013Part007

theorem surrogateDiagonalTailChunk001Sub001Block013Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block013Part007CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block013Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block013Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block013Part007CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block013Part007SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block013Part007] using hcert

def TailChunk001Sub001Block013Part008SupportExplicit : Finset ℕ :=
  ([25278] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block013Part008 : ℚ :=
  (45488328181 : ℚ) / 340769160620083200

def SurrogateDiagonalTailChunk001Sub001Block013Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25278
    = surrogateDiagTailX0RatChunk001Sub001Block013Part008

theorem surrogateDiagonalTailChunk001Sub001Block013Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block013Part008CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block013Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block013Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block013Part008CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block013Part008SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block013Part008] using hcert

def TailChunk001Sub001Block013Part009SupportExplicit : Finset ℕ :=
  ([25279] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block013Part009 : ℚ :=
  (34905844575 : ℚ) / 66588737540517658624

def SurrogateDiagonalTailChunk001Sub001Block013Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25279
    = surrogateDiagTailX0RatChunk001Sub001Block013Part009

theorem surrogateDiagonalTailChunk001Sub001Block013Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block013Part009CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block013Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block013Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block013Part009CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block013Part009SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block013Part009] using hcert

def TailChunk001Sub001Block013Part010SupportExplicit : Finset ℕ :=
  ([25282] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block013Part010 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block013Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25282
    = surrogateDiagTailX0RatChunk001Sub001Block013Part010

theorem surrogateDiagonalTailChunk001Sub001Block013Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block013Part010CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block013Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block013Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block013Part010CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block013Part010SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block013Part010] using hcert

def TailChunk001Sub001Block013Part011SupportExplicit : Finset ℕ :=
  ([25283] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block013Part011 : ℚ :=
  (83381881 : ℚ) / 808767957919334400

def SurrogateDiagonalTailChunk001Sub001Block013Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25283
    = surrogateDiagTailX0RatChunk001Sub001Block013Part011

theorem surrogateDiagonalTailChunk001Sub001Block013Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block013Part011CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block013Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block013Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block013Part011CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block013Part011SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block013Part011] using hcert

def TailChunk001Sub001Block013Part012SupportExplicit : Finset ℕ :=
  ([25285] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block013Part012 : ℚ :=
  (1765241377975 : ℚ) / 300828314738714738688

def SurrogateDiagonalTailChunk001Sub001Block013Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25285
    = surrogateDiagTailX0RatChunk001Sub001Block013Part012

theorem surrogateDiagonalTailChunk001Sub001Block013Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block013Part012CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block013Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block013Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block013Part012CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block013Part012SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block013Part012] using hcert

def TailChunk001Sub001Block013Part013SupportExplicit : Finset ℕ :=
  ([25286] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block013Part013 : ℚ :=
  (49655033525 : ℚ) / 28878016889504523264

def SurrogateDiagonalTailChunk001Sub001Block013Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25286
    = surrogateDiagTailX0RatChunk001Sub001Block013Part013

theorem surrogateDiagonalTailChunk001Sub001Block013Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block013Part013CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block013Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block013Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block013Part013CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block013Part013SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block013Part013] using hcert

def TailChunk001Sub001Block013Part014SupportExplicit : Finset ℕ :=
  ([25287] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block013Part014 : ℚ :=
  (125025 : ℚ) / 40363432803534848

def SurrogateDiagonalTailChunk001Sub001Block013Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25287
    = surrogateDiagTailX0RatChunk001Sub001Block013Part014

theorem surrogateDiagonalTailChunk001Sub001Block013Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block013Part014CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block013Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block013Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block013Part014CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block013Part014SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block013Part014] using hcert

def TailChunk001Sub001Block013Part015SupportExplicit : Finset ℕ :=
  ([25291] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block013Part015 : ℚ :=
  (817283930425 : ℚ) / 551598183091455510528

def SurrogateDiagonalTailChunk001Sub001Block013Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25291
    = surrogateDiagTailX0RatChunk001Sub001Block013Part015

theorem surrogateDiagonalTailChunk001Sub001Block013Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block013Part015CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block013Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block013Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block013Part015CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block013Part015SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block013Part015] using hcert

def TailChunk001Sub001Block013Part016SupportExplicit : Finset ℕ :=
  ([25293] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block013Part016 : ℚ :=
  (1667 : ℚ) / 538690134614400

def SurrogateDiagonalTailChunk001Sub001Block013Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25293
    = surrogateDiagTailX0RatChunk001Sub001Block013Part016

theorem surrogateDiagonalTailChunk001Sub001Block013Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block013Part016CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block013Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block013Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block013Part016CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block013Part016SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block013Part016] using hcert

def TailChunk001Sub001Block013Part017SupportExplicit : Finset ℕ :=
  ([25294] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block013Part017 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block013Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25294
    = surrogateDiagTailX0RatChunk001Sub001Block013Part017

theorem surrogateDiagonalTailChunk001Sub001Block013Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block013Part017CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block013Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block013Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block013Part017CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block013Part017SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block013Part017] using hcert

def TailChunk001Sub001Block013Part018SupportExplicit : Finset ℕ :=
  ([25295] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block013Part018 : ℚ :=
  (1600210805125 : ℚ) / 418969225765892671488

def SurrogateDiagonalTailChunk001Sub001Block013Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25295
    = surrogateDiagTailX0RatChunk001Sub001Block013Part018

theorem surrogateDiagonalTailChunk001Sub001Block013Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block013Part018CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block013Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block013Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block013Part018CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block013Part018SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block013Part018] using hcert

def TailChunk001Sub001Block013Part019SupportExplicit : Finset ℕ :=
  ([25297] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block013Part019 : ℚ :=
  (323149135 : ℚ) / 1474720289865596928

def SurrogateDiagonalTailChunk001Sub001Block013Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25297
    = surrogateDiagTailX0RatChunk001Sub001Block013Part019

theorem surrogateDiagonalTailChunk001Sub001Block013Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block013Part019CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block013Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block013Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block013Part019CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block013Part019SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block013Part019] using hcert

def TailChunk001Sub001Block013Part020SupportExplicit : Finset ℕ :=
  ([25298] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block013Part020 : ℚ :=
  (10192250275 : ℚ) / 300876432729735168

def SurrogateDiagonalTailChunk001Sub001Block013Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25298
    = surrogateDiagTailX0RatChunk001Sub001Block013Part020

theorem surrogateDiagonalTailChunk001Sub001Block013Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block013Part020CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block013Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block013Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block013Part020CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block013Part020SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block013Part020] using hcert

def TailChunk001Sub001Block013Part021SupportExplicit : Finset ℕ :=
  ([25301] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block013Part021 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block013Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25301
    = surrogateDiagTailX0RatChunk001Sub001Block013Part021

theorem surrogateDiagonalTailChunk001Sub001Block013Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block013Part021CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block013Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block013Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block013Part021CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block013Part021SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block013Part021] using hcert

def TailChunk001Sub001Block013Part022SupportExplicit : Finset ℕ :=
  ([25302] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block013Part022 : ℚ :=
  (277885270525 : ℚ) / 3160015835975196672

def SurrogateDiagonalTailChunk001Sub001Block013Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25302
    = surrogateDiagTailX0RatChunk001Sub001Block013Part022

theorem surrogateDiagonalTailChunk001Sub001Block013Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block013Part022CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block013Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block013Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block013Part022CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block013Part022SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block013Part022] using hcert

def TailChunk001Sub001Block013Part023SupportExplicit : Finset ℕ :=
  ([25303] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block013Part023 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block013Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25303
    = surrogateDiagTailX0RatChunk001Sub001Block013Part023

theorem surrogateDiagonalTailChunk001Sub001Block013Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block013Part023CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block013Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block013Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block013Part023CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block013Part023SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block013Part023] using hcert

def TailChunk001Sub001Block013Part024SupportExplicit : Finset ℕ :=
  ([25305] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block013Part024 : ℚ :=
  (5417674963 : ℚ) / 176155726782136320

def SurrogateDiagonalTailChunk001Sub001Block013Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25305
    = surrogateDiagTailX0RatChunk001Sub001Block013Part024

theorem surrogateDiagonalTailChunk001Sub001Block013Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block013Part024CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block013Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block013Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block013Part024CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block013Part024SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block013Part024] using hcert

def surrogateDiagonalTailChunk001Sub001Block013HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub001Block013Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block013Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block013Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block013Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block013Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block013Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block013Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block013Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block013Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block013Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub001Block013Head : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block013Part000
    + surrogateDiagTailX0RatChunk001Sub001Block013Part001
    + surrogateDiagTailX0RatChunk001Sub001Block013Part002
    + surrogateDiagTailX0RatChunk001Sub001Block013Part003
    + surrogateDiagTailX0RatChunk001Sub001Block013Part004
    + surrogateDiagTailX0RatChunk001Sub001Block013Part005
    + surrogateDiagTailX0RatChunk001Sub001Block013Part006
    + surrogateDiagTailX0RatChunk001Sub001Block013Part007
    + surrogateDiagTailX0RatChunk001Sub001Block013Part008
    + surrogateDiagTailX0RatChunk001Sub001Block013Part009

def surrogateDiagonalTailChunk001Sub001Block013MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub001Block013Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block013Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block013Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block013Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block013Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block013Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block013Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block013Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block013Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block013Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub001Block013Mid : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block013Part010
    + surrogateDiagTailX0RatChunk001Sub001Block013Part011
    + surrogateDiagTailX0RatChunk001Sub001Block013Part012
    + surrogateDiagTailX0RatChunk001Sub001Block013Part013
    + surrogateDiagTailX0RatChunk001Sub001Block013Part014
    + surrogateDiagTailX0RatChunk001Sub001Block013Part015
    + surrogateDiagTailX0RatChunk001Sub001Block013Part016
    + surrogateDiagTailX0RatChunk001Sub001Block013Part017
    + surrogateDiagTailX0RatChunk001Sub001Block013Part018
    + surrogateDiagTailX0RatChunk001Sub001Block013Part019

def surrogateDiagonalTailChunk001Sub001Block013TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub001Block013Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block013Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block013Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block013Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block013Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub001Block013Tail : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block013Part020
    + surrogateDiagTailX0RatChunk001Sub001Block013Part021
    + surrogateDiagTailX0RatChunk001Sub001Block013Part022
    + surrogateDiagTailX0RatChunk001Sub001Block013Part023
    + surrogateDiagTailX0RatChunk001Sub001Block013Part024

def surrogateDiagonalTailChunk001Sub001Block013Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk001Sub001Block013HeadSum X0
    + surrogateDiagonalTailChunk001Sub001Block013MidSum X0
    + surrogateDiagonalTailChunk001Sub001Block013TailSum X0

def surrogateDiagTailX0RatChunk001Sub001Block013 : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block013Part000
    + surrogateDiagTailX0RatChunk001Sub001Block013Part001
    + surrogateDiagTailX0RatChunk001Sub001Block013Part002
    + surrogateDiagTailX0RatChunk001Sub001Block013Part003
    + surrogateDiagTailX0RatChunk001Sub001Block013Part004
    + surrogateDiagTailX0RatChunk001Sub001Block013Part005
    + surrogateDiagTailX0RatChunk001Sub001Block013Part006
    + surrogateDiagTailX0RatChunk001Sub001Block013Part007
    + surrogateDiagTailX0RatChunk001Sub001Block013Part008
    + surrogateDiagTailX0RatChunk001Sub001Block013Part009
    + surrogateDiagTailX0RatChunk001Sub001Block013Part010
    + surrogateDiagTailX0RatChunk001Sub001Block013Part011
    + surrogateDiagTailX0RatChunk001Sub001Block013Part012
    + surrogateDiagTailX0RatChunk001Sub001Block013Part013
    + surrogateDiagTailX0RatChunk001Sub001Block013Part014
    + surrogateDiagTailX0RatChunk001Sub001Block013Part015
    + surrogateDiagTailX0RatChunk001Sub001Block013Part016
    + surrogateDiagTailX0RatChunk001Sub001Block013Part017
    + surrogateDiagTailX0RatChunk001Sub001Block013Part018
    + surrogateDiagTailX0RatChunk001Sub001Block013Part019
    + surrogateDiagTailX0RatChunk001Sub001Block013Part020
    + surrogateDiagTailX0RatChunk001Sub001Block013Part021
    + surrogateDiagTailX0RatChunk001Sub001Block013Part022
    + surrogateDiagTailX0RatChunk001Sub001Block013Part023
    + surrogateDiagTailX0RatChunk001Sub001Block013Part024

theorem surrogateDiagTailX0RatChunk001Sub001Block013_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk001Sub001Block013Head + surrogateDiagTailX0RatChunk001Sub001Block013Mid + surrogateDiagTailX0RatChunk001Sub001Block013Tail =
      surrogateDiagTailX0RatChunk001Sub001Block013 := by
  unfold surrogateDiagTailX0RatChunk001Sub001Block013Head surrogateDiagTailX0RatChunk001Sub001Block013Mid surrogateDiagTailX0RatChunk001Sub001Block013Tail surrogateDiagTailX0RatChunk001Sub001Block013
  ring

def SurrogateDiagonalTailChunk001Sub001Block013HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub001Block013HeadSum X0 = surrogateDiagTailX0RatChunk001Sub001Block013Head

def SurrogateDiagonalTailChunk001Sub001Block013MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub001Block013MidSum X0 = surrogateDiagTailX0RatChunk001Sub001Block013Mid

def SurrogateDiagonalTailChunk001Sub001Block013TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub001Block013TailSum X0 = surrogateDiagTailX0RatChunk001Sub001Block013Tail

theorem surrogateDiagonalTailChunk001Sub001Block013_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk001Sub001Block013HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk001Sub001Block013MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk001Sub001Block013TailCertificateAt X0) :
    surrogateDiagonalTailChunk001Sub001Block013Sum X0 = surrogateDiagTailX0RatChunk001Sub001Block013 := by
  unfold SurrogateDiagonalTailChunk001Sub001Block013HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk001Sub001Block013MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk001Sub001Block013TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk001Sub001Block013Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk001Sub001Block013_eq_head_add_mid_add_tail

/-- Block 014 covers tail-support indices [15350,15375) and q from 25306 to 25345. -/

def TailChunk001Sub001Block014Part000SupportExplicit : Finset ℕ :=
  ([25306] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block014Part000 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block014Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25306
    = surrogateDiagTailX0RatChunk001Sub001Block014Part000

theorem surrogateDiagonalTailChunk001Sub001Block014Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block014Part000CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block014Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block014Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block014Part000CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block014Part000SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block014Part000] using hcert

def TailChunk001Sub001Block014Part001SupportExplicit : Finset ℕ :=
  ([25307] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block014Part001 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block014Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25307
    = surrogateDiagTailX0RatChunk001Sub001Block014Part001

theorem surrogateDiagonalTailChunk001Sub001Block014Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block014Part001CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block014Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block014Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block014Part001CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block014Part001SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block014Part001] using hcert

def TailChunk001Sub001Block014Part002SupportExplicit : Finset ℕ :=
  ([25309] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block014Part002 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block014Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25309
    = surrogateDiagTailX0RatChunk001Sub001Block014Part002

theorem surrogateDiagonalTailChunk001Sub001Block014Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block014Part002CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block014Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block014Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block014Part002CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block014Part002SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block014Part002] using hcert

def TailChunk001Sub001Block014Part003SupportExplicit : Finset ℕ :=
  ([25310] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block014Part003 : ℚ :=
  (32048113729 : ℚ) / 1049080706922547200

def SurrogateDiagonalTailChunk001Sub001Block014Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25310
    = surrogateDiagTailX0RatChunk001Sub001Block014Part003

theorem surrogateDiagonalTailChunk001Sub001Block014Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block014Part003CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block014Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block014Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block014Part003CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block014Part003SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block014Part003] using hcert

def TailChunk001Sub001Block014Part004SupportExplicit : Finset ℕ :=
  ([25311] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block014Part004 : ℚ :=
  (34270566103 : ℚ) / 3755292685251379200

def SurrogateDiagonalTailChunk001Sub001Block014Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25311
    = surrogateDiagTailX0RatChunk001Sub001Block014Part004

theorem surrogateDiagonalTailChunk001Sub001Block014Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block014Part004CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block014Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block014Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block014Part004CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block014Part004SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block014Part004] using hcert

def TailChunk001Sub001Block014Part005SupportExplicit : Finset ℕ :=
  ([25313] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block014Part005 : ℚ :=
  (558202666675 : ℚ) / 803375372610199093248

def SurrogateDiagonalTailChunk001Sub001Block014Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25313
    = surrogateDiagTailX0RatChunk001Sub001Block014Part005

theorem surrogateDiagonalTailChunk001Sub001Block014Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block014Part005CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block014Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block014Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block014Part005CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block014Part005SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block014Part005] using hcert

def TailChunk001Sub001Block014Part006SupportExplicit : Finset ℕ :=
  ([25314] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block014Part006 : ℚ :=
  (556297666025 : ℚ) / 6332032678156490304

def SurrogateDiagonalTailChunk001Sub001Block014Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25314
    = surrogateDiagTailX0RatChunk001Sub001Block014Part006

theorem surrogateDiagonalTailChunk001Sub001Block014Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block014Part006CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block014Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block014Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block014Part006CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block014Part006SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block014Part006] using hcert

def TailChunk001Sub001Block014Part007SupportExplicit : Finset ℕ :=
  ([25315] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block014Part007 : ℚ :=
  (67472534761 : ℚ) / 15003314967556915200

def SurrogateDiagonalTailChunk001Sub001Block014Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25315
    = surrogateDiagTailX0RatChunk001Sub001Block014Part007

theorem surrogateDiagonalTailChunk001Sub001Block014Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block014Part007CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block014Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block014Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block014Part007CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block014Part007SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block014Part007] using hcert

def TailChunk001Sub001Block014Part008SupportExplicit : Finset ℕ :=
  ([25318] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block014Part008 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block014Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25318
    = surrogateDiagTailX0RatChunk001Sub001Block014Part008

theorem surrogateDiagonalTailChunk001Sub001Block014Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block014Part008CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block014Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block014Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block014Part008CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block014Part008SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block014Part008] using hcert

def TailChunk001Sub001Block014Part009SupportExplicit : Finset ℕ :=
  ([25319] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block014Part009 : ℚ :=
  (819090930625 : ℚ) / 554045647701858582528

def SurrogateDiagonalTailChunk001Sub001Block014Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25319
    = surrogateDiagTailX0RatChunk001Sub001Block014Part009

theorem surrogateDiagonalTailChunk001Sub001Block014Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block014Part009CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block014Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block014Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block014Part009CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block014Part009SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block014Part009] using hcert

def TailChunk001Sub001Block014Part010SupportExplicit : Finset ℕ :=
  ([25321] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block014Part010 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block014Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25321
    = surrogateDiagTailX0RatChunk001Sub001Block014Part010

theorem surrogateDiagonalTailChunk001Sub001Block014Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block014Part010CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block014Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block014Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block014Part010CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block014Part010SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block014Part010] using hcert

def TailChunk001Sub001Block014Part011SupportExplicit : Finset ℕ :=
  ([25322] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block014Part011 : ℚ :=
  (4447386063 : ℚ) / 583118683750000000

def SurrogateDiagonalTailChunk001Sub001Block014Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25322
    = surrogateDiagTailX0RatChunk001Sub001Block014Part011

theorem surrogateDiagonalTailChunk001Sub001Block014Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block014Part011CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block014Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block014Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block014Part011CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block014Part011SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block014Part011] using hcert

def TailChunk001Sub001Block014Part012SupportExplicit : Finset ℕ :=
  ([25323] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block014Part012 : ℚ :=
  (231412299025 : ℚ) / 168175182021446780928

def SurrogateDiagonalTailChunk001Sub001Block014Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25323
    = surrogateDiagTailX0RatChunk001Sub001Block014Part012

theorem surrogateDiagonalTailChunk001Sub001Block014Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block014Part012CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block014Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block014Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block014Part012CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block014Part012SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block014Part012] using hcert

def TailChunk001Sub001Block014Part013SupportExplicit : Finset ℕ :=
  ([25327] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block014Part013 : ℚ :=
  (218339 : ℚ) / 195992039577600

def SurrogateDiagonalTailChunk001Sub001Block014Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25327
    = surrogateDiagTailX0RatChunk001Sub001Block014Part013

theorem surrogateDiagonalTailChunk001Sub001Block014Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block014Part013CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block014Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block014Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block014Part013CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block014Part013SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block014Part013] using hcert

def TailChunk001Sub001Block014Part014SupportExplicit : Finset ℕ :=
  ([25329] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block014Part014 : ℚ :=
  (41675 : ℚ) / 13544099124022656

def SurrogateDiagonalTailChunk001Sub001Block014Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25329
    = surrogateDiagTailX0RatChunk001Sub001Block014Part014

theorem surrogateDiagonalTailChunk001Sub001Block014Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block014Part014CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block014Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block014Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block014Part014CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block014Part014SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block014Part014] using hcert

def TailChunk001Sub001Block014Part015SupportExplicit : Finset ℕ :=
  ([25330] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block014Part015 : ℚ :=
  (887874060925 : ℚ) / 20127675236197859328

def SurrogateDiagonalTailChunk001Sub001Block014Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25330
    = surrogateDiagTailX0RatChunk001Sub001Block014Part015

theorem surrogateDiagonalTailChunk001Sub001Block014Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block014Part015CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block014Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block014Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block014Part015CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block014Part015SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block014Part015] using hcert

def TailChunk001Sub001Block014Part016SupportExplicit : Finset ℕ :=
  ([25331] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block014Part016 : ℚ :=
  (134266186825 : ℚ) / 963077506767880224768

def SurrogateDiagonalTailChunk001Sub001Block014Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25331
    = surrogateDiagTailX0RatChunk001Sub001Block014Part016

theorem surrogateDiagonalTailChunk001Sub001Block014Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block014Part016CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block014Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block014Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block014Part016CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block014Part016SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block014Part016] using hcert

def TailChunk001Sub001Block014Part017SupportExplicit : Finset ℕ :=
  ([25334] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block014Part017 : ℚ :=
  (86893125625 : ℚ) / 58660810829256050688

def SurrogateDiagonalTailChunk001Sub001Block014Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25334
    = surrogateDiagTailX0RatChunk001Sub001Block014Part017

theorem surrogateDiagonalTailChunk001Sub001Block014Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block014Part017CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block014Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block014Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block014Part017CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block014Part017SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block014Part017] using hcert

def TailChunk001Sub001Block014Part018SupportExplicit : Finset ℕ :=
  ([25337] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block014Part018 : ℚ :=
  (357487718525 : ℚ) / 373316905813679161344

def SurrogateDiagonalTailChunk001Sub001Block014Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25337
    = surrogateDiagTailX0RatChunk001Sub001Block014Part018

theorem surrogateDiagonalTailChunk001Sub001Block014Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block014Part018CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block014Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block014Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block014Part018CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block014Part018SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block014Part018] using hcert

def TailChunk001Sub001Block014Part019SupportExplicit : Finset ℕ :=
  ([25338] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block014Part019 : ℚ :=
  (22537776791 : ℚ) / 221726442789273600

def SurrogateDiagonalTailChunk001Sub001Block014Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25338
    = surrogateDiagTailX0RatChunk001Sub001Block014Part019

theorem surrogateDiagonalTailChunk001Sub001Block014Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block014Part019CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block014Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block014Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block014Part019CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block014Part019SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block014Part019] using hcert

def TailChunk001Sub001Block014Part020SupportExplicit : Finset ℕ :=
  ([25339] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block014Part020 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block014Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25339
    = surrogateDiagTailX0RatChunk001Sub001Block014Part020

theorem surrogateDiagonalTailChunk001Sub001Block014Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block014Part020CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block014Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block014Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block014Part020CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block014Part020SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block014Part020] using hcert

def TailChunk001Sub001Block014Part021SupportExplicit : Finset ℕ :=
  ([25341] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block014Part021 : ℚ :=
  (125025 : ℚ) / 40709361925816448

def SurrogateDiagonalTailChunk001Sub001Block014Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25341
    = surrogateDiagTailX0RatChunk001Sub001Block014Part021

theorem surrogateDiagonalTailChunk001Sub001Block014Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block014Part021CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block014Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block014Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block014Part021CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block014Part021SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block014Part021] using hcert

def TailChunk001Sub001Block014Part022SupportExplicit : Finset ℕ :=
  ([25342] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block014Part022 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block014Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25342
    = surrogateDiagTailX0RatChunk001Sub001Block014Part022

theorem surrogateDiagonalTailChunk001Sub001Block014Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block014Part022CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block014Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block014Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block014Part022CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block014Part022SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block014Part022] using hcert

def TailChunk001Sub001Block014Part023SupportExplicit : Finset ℕ :=
  ([25343] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block014Part023 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block014Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25343
    = surrogateDiagTailX0RatChunk001Sub001Block014Part023

theorem surrogateDiagonalTailChunk001Sub001Block014Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block014Part023CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block014Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block014Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block014Part023CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block014Part023SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block014Part023] using hcert

def TailChunk001Sub001Block014Part024SupportExplicit : Finset ℕ :=
  ([25345] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block014Part024 : ℚ :=
  (430837085875 : ℚ) / 91954390353567547392

def SurrogateDiagonalTailChunk001Sub001Block014Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25345
    = surrogateDiagTailX0RatChunk001Sub001Block014Part024

theorem surrogateDiagonalTailChunk001Sub001Block014Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block014Part024CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block014Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block014Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block014Part024CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block014Part024SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block014Part024] using hcert

def surrogateDiagonalTailChunk001Sub001Block014HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub001Block014Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block014Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block014Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block014Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block014Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block014Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block014Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block014Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block014Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block014Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub001Block014Head : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block014Part000
    + surrogateDiagTailX0RatChunk001Sub001Block014Part001
    + surrogateDiagTailX0RatChunk001Sub001Block014Part002
    + surrogateDiagTailX0RatChunk001Sub001Block014Part003
    + surrogateDiagTailX0RatChunk001Sub001Block014Part004
    + surrogateDiagTailX0RatChunk001Sub001Block014Part005
    + surrogateDiagTailX0RatChunk001Sub001Block014Part006
    + surrogateDiagTailX0RatChunk001Sub001Block014Part007
    + surrogateDiagTailX0RatChunk001Sub001Block014Part008
    + surrogateDiagTailX0RatChunk001Sub001Block014Part009

def surrogateDiagonalTailChunk001Sub001Block014MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub001Block014Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block014Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block014Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block014Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block014Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block014Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block014Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block014Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block014Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block014Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub001Block014Mid : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block014Part010
    + surrogateDiagTailX0RatChunk001Sub001Block014Part011
    + surrogateDiagTailX0RatChunk001Sub001Block014Part012
    + surrogateDiagTailX0RatChunk001Sub001Block014Part013
    + surrogateDiagTailX0RatChunk001Sub001Block014Part014
    + surrogateDiagTailX0RatChunk001Sub001Block014Part015
    + surrogateDiagTailX0RatChunk001Sub001Block014Part016
    + surrogateDiagTailX0RatChunk001Sub001Block014Part017
    + surrogateDiagTailX0RatChunk001Sub001Block014Part018
    + surrogateDiagTailX0RatChunk001Sub001Block014Part019

def surrogateDiagonalTailChunk001Sub001Block014TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub001Block014Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block014Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block014Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block014Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block014Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub001Block014Tail : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block014Part020
    + surrogateDiagTailX0RatChunk001Sub001Block014Part021
    + surrogateDiagTailX0RatChunk001Sub001Block014Part022
    + surrogateDiagTailX0RatChunk001Sub001Block014Part023
    + surrogateDiagTailX0RatChunk001Sub001Block014Part024

def surrogateDiagonalTailChunk001Sub001Block014Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk001Sub001Block014HeadSum X0
    + surrogateDiagonalTailChunk001Sub001Block014MidSum X0
    + surrogateDiagonalTailChunk001Sub001Block014TailSum X0

def surrogateDiagTailX0RatChunk001Sub001Block014 : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block014Part000
    + surrogateDiagTailX0RatChunk001Sub001Block014Part001
    + surrogateDiagTailX0RatChunk001Sub001Block014Part002
    + surrogateDiagTailX0RatChunk001Sub001Block014Part003
    + surrogateDiagTailX0RatChunk001Sub001Block014Part004
    + surrogateDiagTailX0RatChunk001Sub001Block014Part005
    + surrogateDiagTailX0RatChunk001Sub001Block014Part006
    + surrogateDiagTailX0RatChunk001Sub001Block014Part007
    + surrogateDiagTailX0RatChunk001Sub001Block014Part008
    + surrogateDiagTailX0RatChunk001Sub001Block014Part009
    + surrogateDiagTailX0RatChunk001Sub001Block014Part010
    + surrogateDiagTailX0RatChunk001Sub001Block014Part011
    + surrogateDiagTailX0RatChunk001Sub001Block014Part012
    + surrogateDiagTailX0RatChunk001Sub001Block014Part013
    + surrogateDiagTailX0RatChunk001Sub001Block014Part014
    + surrogateDiagTailX0RatChunk001Sub001Block014Part015
    + surrogateDiagTailX0RatChunk001Sub001Block014Part016
    + surrogateDiagTailX0RatChunk001Sub001Block014Part017
    + surrogateDiagTailX0RatChunk001Sub001Block014Part018
    + surrogateDiagTailX0RatChunk001Sub001Block014Part019
    + surrogateDiagTailX0RatChunk001Sub001Block014Part020
    + surrogateDiagTailX0RatChunk001Sub001Block014Part021
    + surrogateDiagTailX0RatChunk001Sub001Block014Part022
    + surrogateDiagTailX0RatChunk001Sub001Block014Part023
    + surrogateDiagTailX0RatChunk001Sub001Block014Part024

theorem surrogateDiagTailX0RatChunk001Sub001Block014_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk001Sub001Block014Head + surrogateDiagTailX0RatChunk001Sub001Block014Mid + surrogateDiagTailX0RatChunk001Sub001Block014Tail =
      surrogateDiagTailX0RatChunk001Sub001Block014 := by
  unfold surrogateDiagTailX0RatChunk001Sub001Block014Head surrogateDiagTailX0RatChunk001Sub001Block014Mid surrogateDiagTailX0RatChunk001Sub001Block014Tail surrogateDiagTailX0RatChunk001Sub001Block014
  ring

def SurrogateDiagonalTailChunk001Sub001Block014HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub001Block014HeadSum X0 = surrogateDiagTailX0RatChunk001Sub001Block014Head

def SurrogateDiagonalTailChunk001Sub001Block014MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub001Block014MidSum X0 = surrogateDiagTailX0RatChunk001Sub001Block014Mid

def SurrogateDiagonalTailChunk001Sub001Block014TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub001Block014TailSum X0 = surrogateDiagTailX0RatChunk001Sub001Block014Tail

theorem surrogateDiagonalTailChunk001Sub001Block014_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk001Sub001Block014HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk001Sub001Block014MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk001Sub001Block014TailCertificateAt X0) :
    surrogateDiagonalTailChunk001Sub001Block014Sum X0 = surrogateDiagTailX0RatChunk001Sub001Block014 := by
  unfold SurrogateDiagonalTailChunk001Sub001Block014HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk001Sub001Block014MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk001Sub001Block014TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk001Sub001Block014Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk001Sub001Block014_eq_head_add_mid_add_tail

/-- Block 015 covers tail-support indices [15375,15400) and q from 25346 to 25386. -/

def TailChunk001Sub001Block015Part000SupportExplicit : Finset ℕ :=
  ([25346] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block015Part000 : ℚ :=
  (76494179375 : ℚ) / 6299244675656368128

def SurrogateDiagonalTailChunk001Sub001Block015Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25346
    = surrogateDiagTailX0RatChunk001Sub001Block015Part000

theorem surrogateDiagonalTailChunk001Sub001Block015Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block015Part000CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block015Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block015Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block015Part000CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block015Part000SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block015Part000] using hcert

def TailChunk001Sub001Block015Part001SupportExplicit : Finset ℕ :=
  ([25347] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block015Part001 : ℚ :=
  (17056660361 : ℚ) / 1631751157422489600

def SurrogateDiagonalTailChunk001Sub001Block015Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25347
    = surrogateDiagTailX0RatChunk001Sub001Block015Part001

theorem surrogateDiagonalTailChunk001Sub001Block015Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block015Part001CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block015Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block015Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block015Part001CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block015Part001SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block015Part001] using hcert

def TailChunk001Sub001Block015Part002SupportExplicit : Finset ℕ :=
  ([25349] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block015Part002 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block015Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25349
    = surrogateDiagTailX0RatChunk001Sub001Block015Part002

theorem surrogateDiagonalTailChunk001Sub001Block015Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block015Part002CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block015Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block015Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block015Part002CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block015Part002SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block015Part002] using hcert

def TailChunk001Sub001Block015Part003SupportExplicit : Finset ℕ :=
  ([25351] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block015Part003 : ℚ :=
  (703386609 : ℚ) / 6511718750000000000

def SurrogateDiagonalTailChunk001Sub001Block015Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25351
    = surrogateDiagTailX0RatChunk001Sub001Block015Part003

theorem surrogateDiagonalTailChunk001Sub001Block015Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block015Part003CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block015Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block015Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block015Part003CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block015Part003SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block015Part003] using hcert

def TailChunk001Sub001Block015Part004SupportExplicit : Finset ℕ :=
  ([25354] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block015Part004 : ℚ :=
  (8226107507 : ℚ) / 695626559900481600

def SurrogateDiagonalTailChunk001Sub001Block015Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25354
    = surrogateDiagTailX0RatChunk001Sub001Block015Part004

theorem surrogateDiagonalTailChunk001Sub001Block015Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block015Part004CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block015Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block015Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block015Part004CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block015Part004SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block015Part004] using hcert

def TailChunk001Sub001Block015Part005SupportExplicit : Finset ℕ :=
  ([25355] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block015Part005 : ℚ :=
  (1031096507 : ℚ) / 143307247718400000

def SurrogateDiagonalTailChunk001Sub001Block015Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25355
    = surrogateDiagTailX0RatChunk001Sub001Block015Part005

theorem surrogateDiagonalTailChunk001Sub001Block015Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block015Part005CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block015Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block015Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block015Part005CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block015Part005SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block015Part005] using hcert

def TailChunk001Sub001Block015Part006SupportExplicit : Finset ℕ :=
  ([25357] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block015Part006 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block015Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25357
    = surrogateDiagTailX0RatChunk001Sub001Block015Part006

theorem surrogateDiagonalTailChunk001Sub001Block015Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block015Part006CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block015Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block015Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block015Part006CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block015Part006SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block015Part006] using hcert

def TailChunk001Sub001Block015Part007SupportExplicit : Finset ℕ :=
  ([25358] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block015Part007 : ℚ :=
  (2678659223 : ℚ) / 1122490116620697600

def SurrogateDiagonalTailChunk001Sub001Block015Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25358
    = surrogateDiagTailX0RatChunk001Sub001Block015Part007

theorem surrogateDiagonalTailChunk001Sub001Block015Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block015Part007CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block015Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block015Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block015Part007CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block015Part007SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block015Part007] using hcert

def TailChunk001Sub001Block015Part008SupportExplicit : Finset ℕ :=
  ([25359] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block015Part008 : ℚ :=
  (28814866675 : ℚ) / 46740001504184381952

def SurrogateDiagonalTailChunk001Sub001Block015Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25359
    = surrogateDiagTailX0RatChunk001Sub001Block015Part008

theorem surrogateDiagonalTailChunk001Sub001Block015Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block015Part008CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block015Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block015Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block015Part008CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block015Part008SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block015Part008] using hcert

def TailChunk001Sub001Block015Part009SupportExplicit : Finset ℕ :=
  ([25361] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block015Part009 : ℚ :=
  (821805180925 : ℚ) / 557732104509756175488

def SurrogateDiagonalTailChunk001Sub001Block015Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25361
    = surrogateDiagTailX0RatChunk001Sub001Block015Part009

theorem surrogateDiagonalTailChunk001Sub001Block015Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block015Part009CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block015Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block015Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block015Part009CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block015Part009SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block015Part009] using hcert

def TailChunk001Sub001Block015Part010SupportExplicit : Finset ℕ :=
  ([25363] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block015Part010 : ℚ :=
  (2128759901 : ℚ) / 3332021311008000000

def SurrogateDiagonalTailChunk001Sub001Block015Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25363
    = surrogateDiagTailX0RatChunk001Sub001Block015Part010

theorem surrogateDiagonalTailChunk001Sub001Block015Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block015Part010CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block015Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block015Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block015Part010CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block015Part010SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block015Part010] using hcert

def TailChunk001Sub001Block015Part011SupportExplicit : Finset ℕ :=
  ([25365] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block015Part011 : ℚ :=
  (602283112175 : ℚ) / 32238699947715723264

def SurrogateDiagonalTailChunk001Sub001Block015Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25365
    = surrogateDiagTailX0RatChunk001Sub001Block015Part011

theorem surrogateDiagonalTailChunk001Sub001Block015Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block015Part011CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block015Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block015Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block015Part011CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block015Part011SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block015Part011] using hcert

def TailChunk001Sub001Block015Part012SupportExplicit : Finset ℕ :=
  ([25366] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block015Part012 : ℚ :=
  (13388170501 : ℚ) / 1761557267821363200

def SurrogateDiagonalTailChunk001Sub001Block015Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25366
    = surrogateDiagTailX0RatChunk001Sub001Block015Part012

theorem surrogateDiagonalTailChunk001Sub001Block015Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block015Part012CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block015Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block015Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block015Part012CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block015Part012SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block015Part012] using hcert

def TailChunk001Sub001Block015Part013SupportExplicit : Finset ℕ :=
  ([25367] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block015Part013 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block015Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25367
    = surrogateDiagTailX0RatChunk001Sub001Block015Part013

theorem surrogateDiagonalTailChunk001Sub001Block015Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block015Part013CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block015Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block015Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block015Part013CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block015Part013SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block015Part013] using hcert

def TailChunk001Sub001Block015Part014SupportExplicit : Finset ℕ :=
  ([25369] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block015Part014 : ℚ :=
  (155141936375 : ℚ) / 431930592009382069824

def SurrogateDiagonalTailChunk001Sub001Block015Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25369
    = surrogateDiagTailX0RatChunk001Sub001Block015Part014

theorem surrogateDiagonalTailChunk001Sub001Block015Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block015Part014CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block015Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block015Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block015Part014CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block015Part014SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block015Part014] using hcert

def TailChunk001Sub001Block015Part015SupportExplicit : Finset ℕ :=
  ([25370] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block015Part015 : ℚ :=
  (216151236325 : ℚ) / 5635286085805350912

def SurrogateDiagonalTailChunk001Sub001Block015Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25370
    = surrogateDiagTailX0RatChunk001Sub001Block015Part015

theorem surrogateDiagonalTailChunk001Sub001Block015Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block015Part015CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block015Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block015Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block015Part015CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block015Part015SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block015Part015] using hcert

def TailChunk001Sub001Block015Part016SupportExplicit : Finset ℕ :=
  ([25373] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block015Part016 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block015Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25373
    = surrogateDiagTailX0RatChunk001Sub001Block015Part016

theorem surrogateDiagonalTailChunk001Sub001Block015Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block015Part016CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block015Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block015Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block015Part016CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block015Part016SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block015Part016] using hcert

def TailChunk001Sub001Block015Part017SupportExplicit : Finset ℕ :=
  ([25374] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block015Part017 : ℚ :=
  (19962037175 : ℚ) / 228296224377892608

def SurrogateDiagonalTailChunk001Sub001Block015Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25374
    = surrogateDiagTailX0RatChunk001Sub001Block015Part017

theorem surrogateDiagonalTailChunk001Sub001Block015Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block015Part017CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block015Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block015Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block015Part017CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block015Part017SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block015Part017] using hcert

def TailChunk001Sub001Block015Part018SupportExplicit : Finset ℕ :=
  ([25377] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block015Part018 : ℚ :=
  (17948756473 : ℚ) / 5567390871139123200

def SurrogateDiagonalTailChunk001Sub001Block015Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25377
    = surrogateDiagTailX0RatChunk001Sub001Block015Part018

theorem surrogateDiagonalTailChunk001Sub001Block015Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block015Part018CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block015Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block015Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block015Part018CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block015Part018SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block015Part018] using hcert

def TailChunk001Sub001Block015Part019SupportExplicit : Finset ℕ :=
  ([25378] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block015Part019 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block015Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25378
    = surrogateDiagTailX0RatChunk001Sub001Block015Part019

theorem surrogateDiagonalTailChunk001Sub001Block015Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block015Part019CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block015Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block015Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block015Part019CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block015Part019SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block015Part019] using hcert

def TailChunk001Sub001Block015Part020SupportExplicit : Finset ℕ :=
  ([25379] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block015Part020 : ℚ :=
  (2709339709 : ℚ) / 12449716476958310400

def SurrogateDiagonalTailChunk001Sub001Block015Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25379
    = surrogateDiagTailX0RatChunk001Sub001Block015Part020

theorem surrogateDiagonalTailChunk001Sub001Block015Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block015Part020CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block015Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block015Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block015Part020CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block015Part020SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block015Part020] using hcert

def TailChunk001Sub001Block015Part021SupportExplicit : Finset ℕ :=
  ([25381] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block015Part021 : ℚ :=
  (561180878275 : ℚ) / 812048712381631561728

def SurrogateDiagonalTailChunk001Sub001Block015Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25381
    = surrogateDiagTailX0RatChunk001Sub001Block015Part021

theorem surrogateDiagonalTailChunk001Sub001Block015Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block015Part021CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block015Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block015Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block015Part021CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block015Part021SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block015Part021] using hcert

def TailChunk001Sub001Block015Part022SupportExplicit : Finset ℕ :=
  ([25383] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block015Part022 : ℚ :=
  (1667 : ℚ) / 546399352166400

def SurrogateDiagonalTailChunk001Sub001Block015Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25383
    = surrogateDiagTailX0RatChunk001Sub001Block015Part022

theorem surrogateDiagonalTailChunk001Sub001Block015Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block015Part022CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block015Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block015Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block015Part022CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block015Part022SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block015Part022] using hcert

def TailChunk001Sub001Block015Part023SupportExplicit : Finset ℕ :=
  ([25385] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block015Part023 : ℚ :=
  (1611611552875 : ℚ) / 424965112271841558528

def SurrogateDiagonalTailChunk001Sub001Block015Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25385
    = surrogateDiagTailX0RatChunk001Sub001Block015Part023

theorem surrogateDiagonalTailChunk001Sub001Block015Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block015Part023CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block015Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block015Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block015Part023CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block015Part023SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block015Part023] using hcert

def TailChunk001Sub001Block015Part024SupportExplicit : Finset ℕ :=
  ([25386] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block015Part024 : ℚ :=
  (4475725327 : ℚ) / 51235184253453120

def SurrogateDiagonalTailChunk001Sub001Block015Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25386
    = surrogateDiagTailX0RatChunk001Sub001Block015Part024

theorem surrogateDiagonalTailChunk001Sub001Block015Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block015Part024CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block015Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block015Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block015Part024CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block015Part024SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block015Part024] using hcert

def surrogateDiagonalTailChunk001Sub001Block015HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub001Block015Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block015Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block015Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block015Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block015Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block015Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block015Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block015Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block015Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block015Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub001Block015Head : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block015Part000
    + surrogateDiagTailX0RatChunk001Sub001Block015Part001
    + surrogateDiagTailX0RatChunk001Sub001Block015Part002
    + surrogateDiagTailX0RatChunk001Sub001Block015Part003
    + surrogateDiagTailX0RatChunk001Sub001Block015Part004
    + surrogateDiagTailX0RatChunk001Sub001Block015Part005
    + surrogateDiagTailX0RatChunk001Sub001Block015Part006
    + surrogateDiagTailX0RatChunk001Sub001Block015Part007
    + surrogateDiagTailX0RatChunk001Sub001Block015Part008
    + surrogateDiagTailX0RatChunk001Sub001Block015Part009

def surrogateDiagonalTailChunk001Sub001Block015MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub001Block015Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block015Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block015Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block015Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block015Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block015Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block015Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block015Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block015Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block015Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub001Block015Mid : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block015Part010
    + surrogateDiagTailX0RatChunk001Sub001Block015Part011
    + surrogateDiagTailX0RatChunk001Sub001Block015Part012
    + surrogateDiagTailX0RatChunk001Sub001Block015Part013
    + surrogateDiagTailX0RatChunk001Sub001Block015Part014
    + surrogateDiagTailX0RatChunk001Sub001Block015Part015
    + surrogateDiagTailX0RatChunk001Sub001Block015Part016
    + surrogateDiagTailX0RatChunk001Sub001Block015Part017
    + surrogateDiagTailX0RatChunk001Sub001Block015Part018
    + surrogateDiagTailX0RatChunk001Sub001Block015Part019

def surrogateDiagonalTailChunk001Sub001Block015TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub001Block015Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block015Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block015Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block015Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block015Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub001Block015Tail : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block015Part020
    + surrogateDiagTailX0RatChunk001Sub001Block015Part021
    + surrogateDiagTailX0RatChunk001Sub001Block015Part022
    + surrogateDiagTailX0RatChunk001Sub001Block015Part023
    + surrogateDiagTailX0RatChunk001Sub001Block015Part024

def surrogateDiagonalTailChunk001Sub001Block015Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk001Sub001Block015HeadSum X0
    + surrogateDiagonalTailChunk001Sub001Block015MidSum X0
    + surrogateDiagonalTailChunk001Sub001Block015TailSum X0

def surrogateDiagTailX0RatChunk001Sub001Block015 : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block015Part000
    + surrogateDiagTailX0RatChunk001Sub001Block015Part001
    + surrogateDiagTailX0RatChunk001Sub001Block015Part002
    + surrogateDiagTailX0RatChunk001Sub001Block015Part003
    + surrogateDiagTailX0RatChunk001Sub001Block015Part004
    + surrogateDiagTailX0RatChunk001Sub001Block015Part005
    + surrogateDiagTailX0RatChunk001Sub001Block015Part006
    + surrogateDiagTailX0RatChunk001Sub001Block015Part007
    + surrogateDiagTailX0RatChunk001Sub001Block015Part008
    + surrogateDiagTailX0RatChunk001Sub001Block015Part009
    + surrogateDiagTailX0RatChunk001Sub001Block015Part010
    + surrogateDiagTailX0RatChunk001Sub001Block015Part011
    + surrogateDiagTailX0RatChunk001Sub001Block015Part012
    + surrogateDiagTailX0RatChunk001Sub001Block015Part013
    + surrogateDiagTailX0RatChunk001Sub001Block015Part014
    + surrogateDiagTailX0RatChunk001Sub001Block015Part015
    + surrogateDiagTailX0RatChunk001Sub001Block015Part016
    + surrogateDiagTailX0RatChunk001Sub001Block015Part017
    + surrogateDiagTailX0RatChunk001Sub001Block015Part018
    + surrogateDiagTailX0RatChunk001Sub001Block015Part019
    + surrogateDiagTailX0RatChunk001Sub001Block015Part020
    + surrogateDiagTailX0RatChunk001Sub001Block015Part021
    + surrogateDiagTailX0RatChunk001Sub001Block015Part022
    + surrogateDiagTailX0RatChunk001Sub001Block015Part023
    + surrogateDiagTailX0RatChunk001Sub001Block015Part024

theorem surrogateDiagTailX0RatChunk001Sub001Block015_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk001Sub001Block015Head + surrogateDiagTailX0RatChunk001Sub001Block015Mid + surrogateDiagTailX0RatChunk001Sub001Block015Tail =
      surrogateDiagTailX0RatChunk001Sub001Block015 := by
  unfold surrogateDiagTailX0RatChunk001Sub001Block015Head surrogateDiagTailX0RatChunk001Sub001Block015Mid surrogateDiagTailX0RatChunk001Sub001Block015Tail surrogateDiagTailX0RatChunk001Sub001Block015
  ring

def SurrogateDiagonalTailChunk001Sub001Block015HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub001Block015HeadSum X0 = surrogateDiagTailX0RatChunk001Sub001Block015Head

def SurrogateDiagonalTailChunk001Sub001Block015MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub001Block015MidSum X0 = surrogateDiagTailX0RatChunk001Sub001Block015Mid

def SurrogateDiagonalTailChunk001Sub001Block015TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub001Block015TailSum X0 = surrogateDiagTailX0RatChunk001Sub001Block015Tail

theorem surrogateDiagonalTailChunk001Sub001Block015_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk001Sub001Block015HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk001Sub001Block015MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk001Sub001Block015TailCertificateAt X0) :
    surrogateDiagonalTailChunk001Sub001Block015Sum X0 = surrogateDiagTailX0RatChunk001Sub001Block015 := by
  unfold SurrogateDiagonalTailChunk001Sub001Block015HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk001Sub001Block015MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk001Sub001Block015TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk001Sub001Block015Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk001Sub001Block015_eq_head_add_mid_add_tail

/-- Block 016 covers tail-support indices [15400,15425) and q from 25387 to 25426. -/

def TailChunk001Sub001Block016Part000SupportExplicit : Finset ℕ :=
  ([25387] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block016Part000 : ℚ :=
  (173126853625 : ℚ) / 954447005809870030848

def SurrogateDiagonalTailChunk001Sub001Block016Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25387
    = surrogateDiagTailX0RatChunk001Sub001Block016Part000

theorem surrogateDiagonalTailChunk001Sub001Block016Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block016Part000CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block016Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block016Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block016Part000CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block016Part000SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block016Part000] using hcert

def TailChunk001Sub001Block016Part001SupportExplicit : Finset ℕ :=
  ([25390] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block016Part001 : ℚ :=
  (5718225725 : ℚ) / 188371060404185088

def SurrogateDiagonalTailChunk001Sub001Block016Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25390
    = surrogateDiagTailX0RatChunk001Sub001Block016Part001

theorem surrogateDiagonalTailChunk001Sub001Block016Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block016Part001CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block016Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block016Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block016Part001CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block016Part001SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block016Part001] using hcert

def TailChunk001Sub001Block016Part002SupportExplicit : Finset ℕ :=
  ([25391] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block016Part002 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block016Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25391
    = surrogateDiagTailX0RatChunk001Sub001Block016Part002

theorem surrogateDiagonalTailChunk001Sub001Block016Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block016Part002CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block016Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block016Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block016Part002CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block016Part002SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block016Part002] using hcert

def TailChunk001Sub001Block016Part003SupportExplicit : Finset ℕ :=
  ([25393] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block016Part003 : ℚ :=
  (34135005325 : ℚ) / 242164126857313073952

def SurrogateDiagonalTailChunk001Sub001Block016Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25393
    = surrogateDiagTailX0RatChunk001Sub001Block016Part003

theorem surrogateDiagonalTailChunk001Sub001Block016Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block016Part003CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block016Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block016Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block016Part003CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block016Part003SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block016Part003] using hcert

def TailChunk001Sub001Block016Part004SupportExplicit : Finset ℕ :=
  ([25394] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block016Part004 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block016Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25394
    = surrogateDiagTailX0RatChunk001Sub001Block016Part004

theorem surrogateDiagonalTailChunk001Sub001Block016Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block016Part004CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block016Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block016Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block016Part004CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block016Part004SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block016Part004] using hcert

def TailChunk001Sub001Block016Part005SupportExplicit : Finset ℕ :=
  ([25395] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block016Part005 : ℚ :=
  (269072240875 : ℚ) / 20985931470214397952

def SurrogateDiagonalTailChunk001Sub001Block016Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25395
    = surrogateDiagTailX0RatChunk001Sub001Block016Part005

theorem surrogateDiagonalTailChunk001Sub001Block016Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block016Part005CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block016Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block016Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block016Part005CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block016Part005SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block016Part005] using hcert

def TailChunk001Sub001Block016Part006SupportExplicit : Finset ℕ :=
  ([25397] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block016Part006 : ℚ :=
  (17923627675 : ℚ) / 164256502052895326208

def SurrogateDiagonalTailChunk001Sub001Block016Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25397
    = surrogateDiagTailX0RatChunk001Sub001Block016Part006

theorem surrogateDiagonalTailChunk001Sub001Block016Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block016Part006CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block016Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block016Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block016Part006CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block016Part006SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block016Part006] using hcert

def TailChunk001Sub001Block016Part007SupportExplicit : Finset ℕ :=
  ([25399] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block016Part007 : ℚ :=
  (6688525111 : ℚ) / 7095288792627724800

def SurrogateDiagonalTailChunk001Sub001Block016Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25399
    = surrogateDiagTailX0RatChunk001Sub001Block016Part007

theorem surrogateDiagonalTailChunk001Sub001Block016Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block016Part007CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block016Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block016Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block016Part007CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block016Part007SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block016Part007] using hcert

def TailChunk001Sub001Block016Part008SupportExplicit : Finset ℕ :=
  ([25401] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block016Part008 : ℚ :=
  (41675 : ℚ) / 13698776776000896

def SurrogateDiagonalTailChunk001Sub001Block016Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25401
    = surrogateDiagTailX0RatChunk001Sub001Block016Part008

theorem surrogateDiagonalTailChunk001Sub001Block016Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block016Part008CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block016Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block016Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block016Part008CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block016Part008SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block016Part008] using hcert

def TailChunk001Sub001Block016Part009SupportExplicit : Finset ℕ :=
  ([25402] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block016Part009 : ℚ :=
  (301194695125 : ℚ) / 47049077628566765568

def SurrogateDiagonalTailChunk001Sub001Block016Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25402
    = surrogateDiagTailX0RatChunk001Sub001Block016Part009

theorem surrogateDiagonalTailChunk001Sub001Block016Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block016Part009CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block016Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block016Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block016Part009CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block016Part009SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block016Part009] using hcert

def TailChunk001Sub001Block016Part010SupportExplicit : Finset ℕ :=
  ([25403] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block016Part010 : ℚ :=
  (37300162781 : ℚ) / 8866787090625561600

def SurrogateDiagonalTailChunk001Sub001Block016Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25403
    = surrogateDiagTailX0RatChunk001Sub001Block016Part010

theorem surrogateDiagonalTailChunk001Sub001Block016Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block016Part010CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block016Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block016Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block016Part010CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block016Part010SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block016Part010] using hcert

def TailChunk001Sub001Block016Part011SupportExplicit : Finset ℕ :=
  ([25405] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block016Part011 : ℚ :=
  (4304401473 : ℚ) / 1136816597360967680

def SurrogateDiagonalTailChunk001Sub001Block016Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25405
    = surrogateDiagTailX0RatChunk001Sub001Block016Part011

theorem surrogateDiagonalTailChunk001Sub001Block016Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block016Part011CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block016Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block016Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block016Part011CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block016Part011SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block016Part011] using hcert

def TailChunk001Sub001Block016Part012SupportExplicit : Finset ℕ :=
  ([25406] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block016Part012 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block016Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25406
    = surrogateDiagTailX0RatChunk001Sub001Block016Part012

theorem surrogateDiagonalTailChunk001Sub001Block016Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block016Part012CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block016Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block016Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block016Part012CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block016Part012SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block016Part012] using hcert

def TailChunk001Sub001Block016Part013SupportExplicit : Finset ℕ :=
  ([25409] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block016Part013 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block016Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25409
    = surrogateDiagTailX0RatChunk001Sub001Block016Part013

theorem surrogateDiagonalTailChunk001Sub001Block016Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block016Part013CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block016Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block016Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block016Part013CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block016Part013SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block016Part013] using hcert

def TailChunk001Sub001Block016Part014SupportExplicit : Finset ℕ :=
  ([25411] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block016Part014 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block016Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25411
    = surrogateDiagTailX0RatChunk001Sub001Block016Part014

theorem surrogateDiagonalTailChunk001Sub001Block016Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block016Part014CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block016Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block016Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block016Part014CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block016Part014SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block016Part014] using hcert

def TailChunk001Sub001Block016Part015SupportExplicit : Finset ℕ :=
  ([25413] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block016Part015 : ℚ :=
  (144083263375 : ℚ) / 183725013751178231808

def SurrogateDiagonalTailChunk001Sub001Block016Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25413
    = surrogateDiagTailX0RatChunk001Sub001Block016Part015

theorem surrogateDiagonalTailChunk001Sub001Block016Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block016Part015CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block016Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block016Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block016Part015CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block016Part015SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block016Part015] using hcert

def TailChunk001Sub001Block016Part016SupportExplicit : Finset ℕ :=
  ([25414] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block016Part016 : ℚ :=
  (2803815451 : ℚ) / 2426303873758003200

def SurrogateDiagonalTailChunk001Sub001Block016Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25414
    = surrogateDiagTailX0RatChunk001Sub001Block016Part016

theorem surrogateDiagonalTailChunk001Sub001Block016Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block016Part016CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block016Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block016Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block016Part016CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block016Part016SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block016Part016] using hcert

def TailChunk001Sub001Block016Part017SupportExplicit : Finset ℕ :=
  ([25415] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block016Part017 : ℚ :=
  (1047096687125 : ℚ) / 101890212180434878464

def SurrogateDiagonalTailChunk001Sub001Block016Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25415
    = surrogateDiagTailX0RatChunk001Sub001Block016Part017

theorem surrogateDiagonalTailChunk001Sub001Block016Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block016Part017CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block016Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block016Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block016Part017CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block016Part017SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block016Part017] using hcert

def TailChunk001Sub001Block016Part018SupportExplicit : Finset ℕ :=
  ([25417] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block016Part018 : ℚ :=
  (32973158927 : ℚ) / 11253519199717185600

def SurrogateDiagonalTailChunk001Sub001Block016Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25417
    = surrogateDiagTailX0RatChunk001Sub001Block016Part018

theorem surrogateDiagonalTailChunk001Sub001Block016Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block016Part018CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block016Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block016Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block016Part018CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block016Part018SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block016Part018] using hcert

def TailChunk001Sub001Block016Part019SupportExplicit : Finset ℕ :=
  ([25418] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block016Part019 : ℚ :=
  (439407121 : ℚ) / 344398284491721600

def SurrogateDiagonalTailChunk001Sub001Block016Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25418
    = surrogateDiagTailX0RatChunk001Sub001Block016Part019

theorem surrogateDiagonalTailChunk001Sub001Block016Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block016Part019CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block016Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block016Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block016Part019CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block016Part019SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block016Part019] using hcert

def TailChunk001Sub001Block016Part020SupportExplicit : Finset ℕ :=
  ([25419] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block016Part020 : ℚ :=
  (171961138825 : ℚ) / 181591799616011501568

def SurrogateDiagonalTailChunk001Sub001Block016Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25419
    = surrogateDiagTailX0RatChunk001Sub001Block016Part020

theorem surrogateDiagonalTailChunk001Sub001Block016Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block016Part020CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block016Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block016Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block016Part020CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block016Part020SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block016Part020] using hcert

def TailChunk001Sub001Block016Part021SupportExplicit : Finset ℕ :=
  ([25421] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block016Part021 : ℚ :=
  (558338983 : ℚ) / 593326208388375000

def SurrogateDiagonalTailChunk001Sub001Block016Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25421
    = surrogateDiagTailX0RatChunk001Sub001Block016Part021

theorem surrogateDiagonalTailChunk001Sub001Block016Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block016Part021CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block016Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block016Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block016Part021CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block016Part021SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block016Part021] using hcert

def TailChunk001Sub001Block016Part022SupportExplicit : Finset ℕ :=
  ([25422] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block016Part022 : ℚ :=
  (3846746525 : ℚ) / 34463314930169088

def SurrogateDiagonalTailChunk001Sub001Block016Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25422
    = surrogateDiagTailX0RatChunk001Sub001Block016Part022

theorem surrogateDiagonalTailChunk001Sub001Block016Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block016Part022CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block016Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block016Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block016Part022CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block016Part022SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block016Part022] using hcert

def TailChunk001Sub001Block016Part023SupportExplicit : Finset ℕ :=
  ([25423] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block016Part023 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block016Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25423
    = surrogateDiagTailX0RatChunk001Sub001Block016Part023

theorem surrogateDiagonalTailChunk001Sub001Block016Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block016Part023CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block016Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block016Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block016Part023CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block016Part023SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block016Part023] using hcert

def TailChunk001Sub001Block016Part024SupportExplicit : Finset ℕ :=
  ([25426] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block016Part024 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block016Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25426
    = surrogateDiagTailX0RatChunk001Sub001Block016Part024

theorem surrogateDiagonalTailChunk001Sub001Block016Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block016Part024CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block016Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block016Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block016Part024CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block016Part024SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block016Part024] using hcert

def surrogateDiagonalTailChunk001Sub001Block016HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub001Block016Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block016Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block016Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block016Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block016Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block016Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block016Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block016Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block016Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block016Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub001Block016Head : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block016Part000
    + surrogateDiagTailX0RatChunk001Sub001Block016Part001
    + surrogateDiagTailX0RatChunk001Sub001Block016Part002
    + surrogateDiagTailX0RatChunk001Sub001Block016Part003
    + surrogateDiagTailX0RatChunk001Sub001Block016Part004
    + surrogateDiagTailX0RatChunk001Sub001Block016Part005
    + surrogateDiagTailX0RatChunk001Sub001Block016Part006
    + surrogateDiagTailX0RatChunk001Sub001Block016Part007
    + surrogateDiagTailX0RatChunk001Sub001Block016Part008
    + surrogateDiagTailX0RatChunk001Sub001Block016Part009

def surrogateDiagonalTailChunk001Sub001Block016MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub001Block016Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block016Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block016Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block016Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block016Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block016Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block016Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block016Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block016Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block016Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub001Block016Mid : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block016Part010
    + surrogateDiagTailX0RatChunk001Sub001Block016Part011
    + surrogateDiagTailX0RatChunk001Sub001Block016Part012
    + surrogateDiagTailX0RatChunk001Sub001Block016Part013
    + surrogateDiagTailX0RatChunk001Sub001Block016Part014
    + surrogateDiagTailX0RatChunk001Sub001Block016Part015
    + surrogateDiagTailX0RatChunk001Sub001Block016Part016
    + surrogateDiagTailX0RatChunk001Sub001Block016Part017
    + surrogateDiagTailX0RatChunk001Sub001Block016Part018
    + surrogateDiagTailX0RatChunk001Sub001Block016Part019

def surrogateDiagonalTailChunk001Sub001Block016TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub001Block016Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block016Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block016Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block016Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block016Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub001Block016Tail : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block016Part020
    + surrogateDiagTailX0RatChunk001Sub001Block016Part021
    + surrogateDiagTailX0RatChunk001Sub001Block016Part022
    + surrogateDiagTailX0RatChunk001Sub001Block016Part023
    + surrogateDiagTailX0RatChunk001Sub001Block016Part024

def surrogateDiagonalTailChunk001Sub001Block016Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk001Sub001Block016HeadSum X0
    + surrogateDiagonalTailChunk001Sub001Block016MidSum X0
    + surrogateDiagonalTailChunk001Sub001Block016TailSum X0

def surrogateDiagTailX0RatChunk001Sub001Block016 : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block016Part000
    + surrogateDiagTailX0RatChunk001Sub001Block016Part001
    + surrogateDiagTailX0RatChunk001Sub001Block016Part002
    + surrogateDiagTailX0RatChunk001Sub001Block016Part003
    + surrogateDiagTailX0RatChunk001Sub001Block016Part004
    + surrogateDiagTailX0RatChunk001Sub001Block016Part005
    + surrogateDiagTailX0RatChunk001Sub001Block016Part006
    + surrogateDiagTailX0RatChunk001Sub001Block016Part007
    + surrogateDiagTailX0RatChunk001Sub001Block016Part008
    + surrogateDiagTailX0RatChunk001Sub001Block016Part009
    + surrogateDiagTailX0RatChunk001Sub001Block016Part010
    + surrogateDiagTailX0RatChunk001Sub001Block016Part011
    + surrogateDiagTailX0RatChunk001Sub001Block016Part012
    + surrogateDiagTailX0RatChunk001Sub001Block016Part013
    + surrogateDiagTailX0RatChunk001Sub001Block016Part014
    + surrogateDiagTailX0RatChunk001Sub001Block016Part015
    + surrogateDiagTailX0RatChunk001Sub001Block016Part016
    + surrogateDiagTailX0RatChunk001Sub001Block016Part017
    + surrogateDiagTailX0RatChunk001Sub001Block016Part018
    + surrogateDiagTailX0RatChunk001Sub001Block016Part019
    + surrogateDiagTailX0RatChunk001Sub001Block016Part020
    + surrogateDiagTailX0RatChunk001Sub001Block016Part021
    + surrogateDiagTailX0RatChunk001Sub001Block016Part022
    + surrogateDiagTailX0RatChunk001Sub001Block016Part023
    + surrogateDiagTailX0RatChunk001Sub001Block016Part024

theorem surrogateDiagTailX0RatChunk001Sub001Block016_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk001Sub001Block016Head + surrogateDiagTailX0RatChunk001Sub001Block016Mid + surrogateDiagTailX0RatChunk001Sub001Block016Tail =
      surrogateDiagTailX0RatChunk001Sub001Block016 := by
  unfold surrogateDiagTailX0RatChunk001Sub001Block016Head surrogateDiagTailX0RatChunk001Sub001Block016Mid surrogateDiagTailX0RatChunk001Sub001Block016Tail surrogateDiagTailX0RatChunk001Sub001Block016
  ring

def SurrogateDiagonalTailChunk001Sub001Block016HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub001Block016HeadSum X0 = surrogateDiagTailX0RatChunk001Sub001Block016Head

def SurrogateDiagonalTailChunk001Sub001Block016MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub001Block016MidSum X0 = surrogateDiagTailX0RatChunk001Sub001Block016Mid

def SurrogateDiagonalTailChunk001Sub001Block016TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub001Block016TailSum X0 = surrogateDiagTailX0RatChunk001Sub001Block016Tail

theorem surrogateDiagonalTailChunk001Sub001Block016_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk001Sub001Block016HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk001Sub001Block016MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk001Sub001Block016TailCertificateAt X0) :
    surrogateDiagonalTailChunk001Sub001Block016Sum X0 = surrogateDiagTailX0RatChunk001Sub001Block016 := by
  unfold SurrogateDiagonalTailChunk001Sub001Block016HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk001Sub001Block016MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk001Sub001Block016TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk001Sub001Block016Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk001Sub001Block016_eq_head_add_mid_add_tail

/-- Block 017 covers tail-support indices [15425,15450) and q from 25427 to 25466. -/

def TailChunk001Sub001Block017Part000SupportExplicit : Finset ℕ :=
  ([25427] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block017Part000 : ℚ :=
  (7123620541 : ℚ) / 38079673517357107200

def SurrogateDiagonalTailChunk001Sub001Block017Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25427
    = surrogateDiagTailX0RatChunk001Sub001Block017Part000

theorem surrogateDiagonalTailChunk001Sub001Block017Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block017Part000CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block017Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block017Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block017Part000CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block017Part000SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block017Part000] using hcert

def TailChunk001Sub001Block017Part001SupportExplicit : Finset ℕ :=
  ([25429] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block017Part001 : ℚ :=
  (96695331 : ℚ) / 644943093514404320

def SurrogateDiagonalTailChunk001Sub001Block017Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25429
    = surrogateDiagTailX0RatChunk001Sub001Block017Part001

theorem surrogateDiagonalTailChunk001Sub001Block017Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block017Part001CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block017Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block017Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block017Part001CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block017Part001SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block017Part001] using hcert

def TailChunk001Sub001Block017Part002SupportExplicit : Finset ℕ :=
  ([25430] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block017Part002 : ℚ :=
  (808809318025 : ℚ) / 26728156717116377088

def SurrogateDiagonalTailChunk001Sub001Block017Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25430
    = surrogateDiagTailX0RatChunk001Sub001Block017Part002

theorem surrogateDiagonalTailChunk001Sub001Block017Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block017Part002CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block017Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block017Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block017Part002CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block017Part002SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block017Part002] using hcert

def TailChunk001Sub001Block017Part003SupportExplicit : Finset ℕ :=
  ([25433] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block017Part003 : ℚ :=
  (62086319275 : ℚ) / 226263977639222648832

def SurrogateDiagonalTailChunk001Sub001Block017Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25433
    = surrogateDiagTailX0RatChunk001Sub001Block017Part003

theorem surrogateDiagonalTailChunk001Sub001Block017Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block017Part003CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block017Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block017Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block017Part003CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block017Part003SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block017Part003] using hcert

def TailChunk001Sub001Block017Part004SupportExplicit : Finset ℕ :=
  ([25435] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block017Part004 : ℚ :=
  (539320933875 : ℚ) / 142774613387942434816

def SurrogateDiagonalTailChunk001Sub001Block017Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25435
    = surrogateDiagTailX0RatChunk001Sub001Block017Part004

theorem surrogateDiagonalTailChunk001Sub001Block017Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block017Part004CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block017Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block017Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block017Part004CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block017Part004SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block017Part004] using hcert

def TailChunk001Sub001Block017Part005SupportExplicit : Finset ℕ :=
  ([25437] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block017Part005 : ℚ :=
  (1224017711 : ℚ) / 52235491793356800

def SurrogateDiagonalTailChunk001Sub001Block017Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25437
    = surrogateDiagTailX0RatChunk001Sub001Block017Part005

theorem surrogateDiagonalTailChunk001Sub001Block017Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block017Part005CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block017Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block017Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block017Part005CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block017Part005SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block017Part005] using hcert

def TailChunk001Sub001Block017Part006SupportExplicit : Finset ℕ :=
  ([25438] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block017Part006 : ℚ :=
  (138023911375 : ℚ) / 7024913858083410432

def SurrogateDiagonalTailChunk001Sub001Block017Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25438
    = surrogateDiagTailX0RatChunk001Sub001Block017Part006

theorem surrogateDiagonalTailChunk001Sub001Block017Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block017Part006CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block017Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block017Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block017Part006CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block017Part006SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block017Part006] using hcert

def TailChunk001Sub001Block017Part007SupportExplicit : Finset ℕ :=
  ([25439] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block017Part007 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block017Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25439
    = surrogateDiagTailX0RatChunk001Sub001Block017Part007

theorem surrogateDiagonalTailChunk001Sub001Block017Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block017Part007CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block017Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block017Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block017Part007CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block017Part007SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block017Part007] using hcert

def TailChunk001Sub001Block017Part008SupportExplicit : Finset ℕ :=
  ([25441] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block017Part008 : ℚ :=
  (61093504075 : ℚ) / 32731811800659542016

def SurrogateDiagonalTailChunk001Sub001Block017Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25441
    = surrogateDiagTailX0RatChunk001Sub001Block017Part008

theorem surrogateDiagonalTailChunk001Sub001Block017Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block017Part008CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block017Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block017Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block017Part008CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block017Part008SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block017Part008] using hcert

def TailChunk001Sub001Block017Part009SupportExplicit : Finset ℕ :=
  ([25442] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block017Part009 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block017Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25442
    = surrogateDiagTailX0RatChunk001Sub001Block017Part009

theorem surrogateDiagonalTailChunk001Sub001Block017Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block017Part009CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block017Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block017Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block017Part009CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block017Part009SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block017Part009] using hcert

def TailChunk001Sub001Block017Part010SupportExplicit : Finset ℕ :=
  ([25445] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block017Part010 : ℚ :=
  (471355338475 : ℚ) / 57618018302551990272

def SurrogateDiagonalTailChunk001Sub001Block017Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25445
    = surrogateDiagTailX0RatChunk001Sub001Block017Part010

theorem surrogateDiagonalTailChunk001Sub001Block017Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block017Part010CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block017Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block017Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block017Part010CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block017Part010SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block017Part010] using hcert

def TailChunk001Sub001Block017Part011SupportExplicit : Finset ℕ :=
  ([25446] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block017Part011 : ℚ :=
  (44947505219 : ℚ) / 258606992464281600

def SurrogateDiagonalTailChunk001Sub001Block017Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25446
    = surrogateDiagTailX0RatChunk001Sub001Block017Part011

theorem surrogateDiagonalTailChunk001Sub001Block017Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block017Part011CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block017Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block017Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block017Part011CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block017Part011SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block017Part011] using hcert

def TailChunk001Sub001Block017Part012SupportExplicit : Finset ℕ :=
  ([25447] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block017Part012 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block017Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25447
    = surrogateDiagTailX0RatChunk001Sub001Block017Part012

theorem surrogateDiagonalTailChunk001Sub001Block017Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block017Part012CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block017Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block017Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block017Part012CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block017Part012SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block017Part012] using hcert

def TailChunk001Sub001Block017Part013SupportExplicit : Finset ℕ :=
  ([25449] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block017Part013 : ℚ :=
  (2128551178175 : ℚ) / 80633246794125410304

def SurrogateDiagonalTailChunk001Sub001Block017Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25449
    = surrogateDiagTailX0RatChunk001Sub001Block017Part013

theorem surrogateDiagonalTailChunk001Sub001Block017Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block017Part013CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block017Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block017Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block017Part013CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block017Part013SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block017Part013] using hcert

def TailChunk001Sub001Block017Part014SupportExplicit : Finset ℕ :=
  ([25451] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block017Part014 : ℚ :=
  (10450343539 : ℚ) / 36629186932512000000

def SurrogateDiagonalTailChunk001Sub001Block017Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25451
    = surrogateDiagTailX0RatChunk001Sub001Block017Part014

theorem surrogateDiagonalTailChunk001Sub001Block017Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block017Part014CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block017Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block017Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block017Part014CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block017Part014SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block017Part014] using hcert

def TailChunk001Sub001Block017Part015SupportExplicit : Finset ℕ :=
  ([25453] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block017Part015 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block017Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25453
    = surrogateDiagTailX0RatChunk001Sub001Block017Part015

theorem surrogateDiagonalTailChunk001Sub001Block017Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block017Part015CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block017Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block017Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block017Part015CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block017Part015SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block017Part015] using hcert

def TailChunk001Sub001Block017Part016SupportExplicit : Finset ℕ :=
  ([25454] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block017Part016 : ℚ :=
  (3875681401 : ℚ) / 207296167359283200

def SurrogateDiagonalTailChunk001Sub001Block017Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25454
    = surrogateDiagTailX0RatChunk001Sub001Block017Part016

theorem surrogateDiagonalTailChunk001Sub001Block017Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block017Part016CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block017Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block017Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block017Part016CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block017Part016SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block017Part016] using hcert

def TailChunk001Sub001Block017Part017SupportExplicit : Finset ℕ :=
  ([25455] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block017Part017 : ℚ :=
  (629608758525 : ℚ) / 14123389881782632448

def SurrogateDiagonalTailChunk001Sub001Block017Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25455
    = surrogateDiagTailX0RatChunk001Sub001Block017Part017

theorem surrogateDiagonalTailChunk001Sub001Block017Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block017Part017CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block017Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block017Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block017Part017CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block017Part017SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block017Part017] using hcert

def TailChunk001Sub001Block017Part018SupportExplicit : Finset ℕ :=
  ([25457] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block017Part018 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block017Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25457
    = surrogateDiagTailX0RatChunk001Sub001Block017Part018

theorem surrogateDiagonalTailChunk001Sub001Block017Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block017Part018CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block017Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block017Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block017Part018CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block017Part018SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block017Part018] using hcert

def TailChunk001Sub001Block017Part019SupportExplicit : Finset ℕ :=
  ([25458] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block017Part019 : ℚ :=
  (1124747668325 : ℚ) / 6477381888336120384

def SurrogateDiagonalTailChunk001Sub001Block017Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25458
    = surrogateDiagTailX0RatChunk001Sub001Block017Part019

theorem surrogateDiagonalTailChunk001Sub001Block017Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block017Part019CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block017Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block017Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block017Part019CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block017Part019SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block017Part019] using hcert

def TailChunk001Sub001Block017Part020SupportExplicit : Finset ℕ :=
  ([25459] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block017Part020 : ℚ :=
  (828155931625 : ℚ) / 566405365356078778368

def SurrogateDiagonalTailChunk001Sub001Block017Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25459
    = surrogateDiagTailX0RatChunk001Sub001Block017Part020

theorem surrogateDiagonalTailChunk001Sub001Block017Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block017Part020CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block017Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block017Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block017Part020CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block017Part020SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block017Part020] using hcert

def TailChunk001Sub001Block017Part021SupportExplicit : Finset ℕ :=
  ([25462] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block017Part021 : ℚ :=
  (38074349275 : ℚ) / 14141498602451415552

def SurrogateDiagonalTailChunk001Sub001Block017Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25462
    = surrogateDiagTailX0RatChunk001Sub001Block017Part021

theorem surrogateDiagonalTailChunk001Sub001Block017Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block017Part021CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block017Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block017Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block017Part021CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block017Part021SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block017Part021] using hcert

def TailChunk001Sub001Block017Part022SupportExplicit : Finset ℕ :=
  ([25463] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block017Part022 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block017Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25463
    = surrogateDiagTailX0RatChunk001Sub001Block017Part022

theorem surrogateDiagonalTailChunk001Sub001Block017Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block017Part022CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block017Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block017Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block017Part022CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block017Part022SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block017Part022] using hcert

def TailChunk001Sub001Block017Part023SupportExplicit : Finset ℕ :=
  ([25465] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block017Part023 : ℚ :=
  (8320220569 : ℚ) / 1166526791788216320

def SurrogateDiagonalTailChunk001Sub001Block017Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25465
    = surrogateDiagTailX0RatChunk001Sub001Block017Part023

theorem surrogateDiagonalTailChunk001Sub001Block017Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block017Part023CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block017Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block017Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block017Part023CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block017Part023SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block017Part023] using hcert

def TailChunk001Sub001Block017Part024SupportExplicit : Finset ℕ :=
  ([25466] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block017Part024 : ℚ :=
  (771952386625 : ℚ) / 26812372978696716288

def SurrogateDiagonalTailChunk001Sub001Block017Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25466
    = surrogateDiagTailX0RatChunk001Sub001Block017Part024

theorem surrogateDiagonalTailChunk001Sub001Block017Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block017Part024CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block017Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block017Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block017Part024CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block017Part024SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block017Part024] using hcert

def surrogateDiagonalTailChunk001Sub001Block017HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub001Block017Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block017Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block017Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block017Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block017Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block017Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block017Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block017Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block017Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block017Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub001Block017Head : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block017Part000
    + surrogateDiagTailX0RatChunk001Sub001Block017Part001
    + surrogateDiagTailX0RatChunk001Sub001Block017Part002
    + surrogateDiagTailX0RatChunk001Sub001Block017Part003
    + surrogateDiagTailX0RatChunk001Sub001Block017Part004
    + surrogateDiagTailX0RatChunk001Sub001Block017Part005
    + surrogateDiagTailX0RatChunk001Sub001Block017Part006
    + surrogateDiagTailX0RatChunk001Sub001Block017Part007
    + surrogateDiagTailX0RatChunk001Sub001Block017Part008
    + surrogateDiagTailX0RatChunk001Sub001Block017Part009

def surrogateDiagonalTailChunk001Sub001Block017MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub001Block017Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block017Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block017Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block017Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block017Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block017Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block017Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block017Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block017Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block017Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub001Block017Mid : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block017Part010
    + surrogateDiagTailX0RatChunk001Sub001Block017Part011
    + surrogateDiagTailX0RatChunk001Sub001Block017Part012
    + surrogateDiagTailX0RatChunk001Sub001Block017Part013
    + surrogateDiagTailX0RatChunk001Sub001Block017Part014
    + surrogateDiagTailX0RatChunk001Sub001Block017Part015
    + surrogateDiagTailX0RatChunk001Sub001Block017Part016
    + surrogateDiagTailX0RatChunk001Sub001Block017Part017
    + surrogateDiagTailX0RatChunk001Sub001Block017Part018
    + surrogateDiagTailX0RatChunk001Sub001Block017Part019

def surrogateDiagonalTailChunk001Sub001Block017TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub001Block017Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block017Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block017Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block017Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block017Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub001Block017Tail : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block017Part020
    + surrogateDiagTailX0RatChunk001Sub001Block017Part021
    + surrogateDiagTailX0RatChunk001Sub001Block017Part022
    + surrogateDiagTailX0RatChunk001Sub001Block017Part023
    + surrogateDiagTailX0RatChunk001Sub001Block017Part024

def surrogateDiagonalTailChunk001Sub001Block017Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk001Sub001Block017HeadSum X0
    + surrogateDiagonalTailChunk001Sub001Block017MidSum X0
    + surrogateDiagonalTailChunk001Sub001Block017TailSum X0

def surrogateDiagTailX0RatChunk001Sub001Block017 : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block017Part000
    + surrogateDiagTailX0RatChunk001Sub001Block017Part001
    + surrogateDiagTailX0RatChunk001Sub001Block017Part002
    + surrogateDiagTailX0RatChunk001Sub001Block017Part003
    + surrogateDiagTailX0RatChunk001Sub001Block017Part004
    + surrogateDiagTailX0RatChunk001Sub001Block017Part005
    + surrogateDiagTailX0RatChunk001Sub001Block017Part006
    + surrogateDiagTailX0RatChunk001Sub001Block017Part007
    + surrogateDiagTailX0RatChunk001Sub001Block017Part008
    + surrogateDiagTailX0RatChunk001Sub001Block017Part009
    + surrogateDiagTailX0RatChunk001Sub001Block017Part010
    + surrogateDiagTailX0RatChunk001Sub001Block017Part011
    + surrogateDiagTailX0RatChunk001Sub001Block017Part012
    + surrogateDiagTailX0RatChunk001Sub001Block017Part013
    + surrogateDiagTailX0RatChunk001Sub001Block017Part014
    + surrogateDiagTailX0RatChunk001Sub001Block017Part015
    + surrogateDiagTailX0RatChunk001Sub001Block017Part016
    + surrogateDiagTailX0RatChunk001Sub001Block017Part017
    + surrogateDiagTailX0RatChunk001Sub001Block017Part018
    + surrogateDiagTailX0RatChunk001Sub001Block017Part019
    + surrogateDiagTailX0RatChunk001Sub001Block017Part020
    + surrogateDiagTailX0RatChunk001Sub001Block017Part021
    + surrogateDiagTailX0RatChunk001Sub001Block017Part022
    + surrogateDiagTailX0RatChunk001Sub001Block017Part023
    + surrogateDiagTailX0RatChunk001Sub001Block017Part024

theorem surrogateDiagTailX0RatChunk001Sub001Block017_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk001Sub001Block017Head + surrogateDiagTailX0RatChunk001Sub001Block017Mid + surrogateDiagTailX0RatChunk001Sub001Block017Tail =
      surrogateDiagTailX0RatChunk001Sub001Block017 := by
  unfold surrogateDiagTailX0RatChunk001Sub001Block017Head surrogateDiagTailX0RatChunk001Sub001Block017Mid surrogateDiagTailX0RatChunk001Sub001Block017Tail surrogateDiagTailX0RatChunk001Sub001Block017
  ring

def SurrogateDiagonalTailChunk001Sub001Block017HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub001Block017HeadSum X0 = surrogateDiagTailX0RatChunk001Sub001Block017Head

def SurrogateDiagonalTailChunk001Sub001Block017MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub001Block017MidSum X0 = surrogateDiagTailX0RatChunk001Sub001Block017Mid

def SurrogateDiagonalTailChunk001Sub001Block017TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub001Block017TailSum X0 = surrogateDiagTailX0RatChunk001Sub001Block017Tail

theorem surrogateDiagonalTailChunk001Sub001Block017_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk001Sub001Block017HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk001Sub001Block017MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk001Sub001Block017TailCertificateAt X0) :
    surrogateDiagonalTailChunk001Sub001Block017Sum X0 = surrogateDiagTailX0RatChunk001Sub001Block017 := by
  unfold SurrogateDiagonalTailChunk001Sub001Block017HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk001Sub001Block017MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk001Sub001Block017TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk001Sub001Block017Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk001Sub001Block017_eq_head_add_mid_add_tail

/-- Block 018 covers tail-support indices [15450,15475) and q from 25467 to 25505. -/

def TailChunk001Sub001Block018Part000SupportExplicit : Finset ℕ :=
  ([25467] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block018Part000 : ℚ :=
  (174125600125 : ℚ) / 6246704568896520192

def SurrogateDiagonalTailChunk001Sub001Block018Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25467
    = surrogateDiagTailX0RatChunk001Sub001Block018Part000

theorem surrogateDiagonalTailChunk001Sub001Block018Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block018Part000CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block018Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block018Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block018Part000CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block018Part000SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block018Part000] using hcert

def TailChunk001Sub001Block018Part001SupportExplicit : Finset ℕ :=
  ([25469] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block018Part001 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block018Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25469
    = surrogateDiagTailX0RatChunk001Sub001Block018Part001

theorem surrogateDiagonalTailChunk001Sub001Block018Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block018Part001CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block018Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block018Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block018Part001CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block018Part001SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block018Part001] using hcert

def TailChunk001Sub001Block018Part002SupportExplicit : Finset ℕ :=
  ([25471] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block018Part002 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block018Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25471
    = surrogateDiagTailX0RatChunk001Sub001Block018Part002

theorem surrogateDiagonalTailChunk001Sub001Block018Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block018Part002CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block018Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block018Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block018Part002CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block018Part002SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block018Part002] using hcert

def TailChunk001Sub001Block018Part003SupportExplicit : Finset ℕ :=
  ([25473] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block018Part003 : ℚ :=
  (26804403325 : ℚ) / 776962092395169792

def SurrogateDiagonalTailChunk001Sub001Block018Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25473
    = surrogateDiagTailX0RatChunk001Sub001Block018Part003

theorem surrogateDiagonalTailChunk001Sub001Block018Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block018Part003CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block018Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block018Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block018Part003CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block018Part003SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block018Part003] using hcert

def TailChunk001Sub001Block018Part004SupportExplicit : Finset ℕ :=
  ([25474] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block018Part004 : ℚ :=
  (1921199123 : ℚ) / 1189989797417409600

def SurrogateDiagonalTailChunk001Sub001Block018Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25474
    = surrogateDiagTailX0RatChunk001Sub001Block018Part004

theorem surrogateDiagonalTailChunk001Sub001Block018Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block018Part004CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block018Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block018Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block018Part004CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block018Part004SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block018Part004] using hcert

def TailChunk001Sub001Block018Part005SupportExplicit : Finset ℕ :=
  ([25477] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block018Part005 : ℚ :=
  (128037188575 : ℚ) / 985539012317371957248

def SurrogateDiagonalTailChunk001Sub001Block018Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25477
    = surrogateDiagTailX0RatChunk001Sub001Block018Part005

theorem surrogateDiagonalTailChunk001Sub001Block018Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block018Part005CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block018Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block018Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block018Part005CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block018Part005SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block018Part005] using hcert

def TailChunk001Sub001Block018Part006SupportExplicit : Finset ℕ :=
  ([25478] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block018Part006 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block018Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25478
    = surrogateDiagTailX0RatChunk001Sub001Block018Part006

theorem surrogateDiagonalTailChunk001Sub001Block018Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block018Part006CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block018Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block018Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block018Part006CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block018Part006SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block018Part006] using hcert

def TailChunk001Sub001Block018Part007SupportExplicit : Finset ℕ :=
  ([25481] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block018Part007 : ℚ :=
  (59441810375 : ℚ) / 495607624130034229824

def SurrogateDiagonalTailChunk001Sub001Block018Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25481
    = surrogateDiagTailX0RatChunk001Sub001Block018Part007

theorem surrogateDiagonalTailChunk001Sub001Block018Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block018Part007CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block018Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block018Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block018Part007CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block018Part007SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block018Part007] using hcert

def TailChunk001Sub001Block018Part008SupportExplicit : Finset ℕ :=
  ([25482] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block018Part008 : ℚ :=
  (45694362319 : ℚ) / 443452885578547200

def SurrogateDiagonalTailChunk001Sub001Block018Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25482
    = surrogateDiagTailX0RatChunk001Sub001Block018Part008

theorem surrogateDiagonalTailChunk001Sub001Block018Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block018Part008CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block018Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block018Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block018Part008CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block018Part008SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block018Part008] using hcert

def TailChunk001Sub001Block018Part009SupportExplicit : Finset ℕ :=
  ([25483] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block018Part009 : ℚ :=
  (723777975 : ℚ) / 1403384633554763776

def SurrogateDiagonalTailChunk001Sub001Block018Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25483
    = surrogateDiagTailX0RatChunk001Sub001Block018Part009

theorem surrogateDiagonalTailChunk001Sub001Block018Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block018Part009CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block018Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block018Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block018Part009CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block018Part009SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block018Part009] using hcert

def TailChunk001Sub001Block018Part010SupportExplicit : Finset ℕ :=
  ([25485] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block018Part010 : ℚ :=
  (473320182875 : ℚ) / 10642595684706717696

def SurrogateDiagonalTailChunk001Sub001Block018Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25485
    = surrogateDiagTailX0RatChunk001Sub001Block018Part010

theorem surrogateDiagonalTailChunk001Sub001Block018Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block018Part010CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block018Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block018Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block018Part010CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block018Part010SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block018Part010] using hcert

def TailChunk001Sub001Block018Part011SupportExplicit : Finset ℕ :=
  ([25486] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block018Part011 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block018Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25486
    = surrogateDiagTailX0RatChunk001Sub001Block018Part011

theorem surrogateDiagonalTailChunk001Sub001Block018Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block018Part011CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block018Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block018Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block018Part011CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block018Part011SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block018Part011] using hcert

def TailChunk001Sub001Block018Part012SupportExplicit : Finset ℕ :=
  ([25487] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block018Part012 : ℚ :=
  (25424436677 : ℚ) / 7686305033616000000

def SurrogateDiagonalTailChunk001Sub001Block018Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25487
    = surrogateDiagTailX0RatChunk001Sub001Block018Part012

theorem surrogateDiagonalTailChunk001Sub001Block018Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block018Part012CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block018Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block018Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block018Part012CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block018Part012SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block018Part012] using hcert

def TailChunk001Sub001Block018Part013SupportExplicit : Finset ℕ :=
  ([25489] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block018Part013 : ℚ :=
  (127241157 : ℚ) / 939208093612577600

def SurrogateDiagonalTailChunk001Sub001Block018Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25489
    = surrogateDiagTailX0RatChunk001Sub001Block018Part013

theorem surrogateDiagonalTailChunk001Sub001Block018Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block018Part013CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block018Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block018Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block018Part013CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block018Part013SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block018Part013] using hcert

def TailChunk001Sub001Block018Part014SupportExplicit : Finset ℕ :=
  ([25490] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block018Part014 : ℚ :=
  (812626052725 : ℚ) / 26981402387623477248

def SurrogateDiagonalTailChunk001Sub001Block018Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25490
    = surrogateDiagTailX0RatChunk001Sub001Block018Part014

theorem surrogateDiagonalTailChunk001Sub001Block018Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block018Part014CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block018Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block018Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block018Part014CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block018Part014SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block018Part014] using hcert

def TailChunk001Sub001Block018Part015SupportExplicit : Finset ℕ :=
  ([25491] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block018Part015 : ℚ :=
  (78149953925 : ℚ) / 3192437074274746368

def SurrogateDiagonalTailChunk001Sub001Block018Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25491
    = surrogateDiagTailX0RatChunk001Sub001Block018Part015

theorem surrogateDiagonalTailChunk001Sub001Block018Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block018Part015CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block018Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block018Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block018Part015CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block018Part015SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block018Part015] using hcert

def TailChunk001Sub001Block018Part016SupportExplicit : Finset ℕ :=
  ([25493] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block018Part016 : ℚ :=
  (971717100625 : ℚ) / 636759188629050359808

def SurrogateDiagonalTailChunk001Sub001Block018Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25493
    = surrogateDiagTailX0RatChunk001Sub001Block018Part016

theorem surrogateDiagonalTailChunk001Sub001Block018Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block018Part016CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block018Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block018Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block018Part016CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block018Part016SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block018Part016] using hcert

def TailChunk001Sub001Block018Part017SupportExplicit : Finset ℕ :=
  ([25494] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block018Part017 : ℚ :=
  (1197207318325 : ℚ) / 6992658831556528128

def SurrogateDiagonalTailChunk001Sub001Block018Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25494
    = surrogateDiagTailX0RatChunk001Sub001Block018Part017

theorem surrogateDiagonalTailChunk001Sub001Block018Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block018Part017CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block018Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block018Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block018Part017CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block018Part017SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block018Part017] using hcert

def TailChunk001Sub001Block018Part018SupportExplicit : Finset ℕ :=
  ([25495] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block018Part018 : ℚ :=
  (541866933375 : ℚ) / 144126849702406690816

def SurrogateDiagonalTailChunk001Sub001Block018Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25495
    = surrogateDiagTailX0RatChunk001Sub001Block018Part018

theorem surrogateDiagonalTailChunk001Sub001Block018Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block018Part018CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block018Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block018Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block018Part018CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block018Part018SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block018Part018] using hcert

def TailChunk001Sub001Block018Part019SupportExplicit : Finset ℕ :=
  ([25498] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block018Part019 : ℚ :=
  (2084866693 : ℚ) / 136076105779200000

def SurrogateDiagonalTailChunk001Sub001Block018Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25498
    = surrogateDiagTailX0RatChunk001Sub001Block018Part019

theorem surrogateDiagonalTailChunk001Sub001Block018Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block018Part019CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block018Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block018Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block018Part019CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block018Part019SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block018Part019] using hcert

def TailChunk001Sub001Block018Part020SupportExplicit : Finset ℕ :=
  ([25499] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block018Part020 : ℚ :=
  (2543091875 : ℚ) / 12914545527643963392

def SurrogateDiagonalTailChunk001Sub001Block018Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25499
    = surrogateDiagTailX0RatChunk001Sub001Block018Part020

theorem surrogateDiagonalTailChunk001Sub001Block018Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block018Part020CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block018Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block018Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block018Part020CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block018Part020SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block018Part020] using hcert

def TailChunk001Sub001Block018Part021SupportExplicit : Finset ℕ :=
  ([25501] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block018Part021 : ℚ :=
  (830885181925 : ℚ) / 570153278899432084608

def SurrogateDiagonalTailChunk001Sub001Block018Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25501
    = surrogateDiagTailX0RatChunk001Sub001Block018Part021

theorem surrogateDiagonalTailChunk001Sub001Block018Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block018Part021CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block018Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block018Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block018Part021CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block018Part021SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block018Part021] using hcert

def TailChunk001Sub001Block018Part022SupportExplicit : Finset ℕ :=
  ([25502] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block018Part022 : ℚ :=
  (1444213689 : ℚ) / 788228867584000000

def SurrogateDiagonalTailChunk001Sub001Block018Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25502
    = surrogateDiagTailX0RatChunk001Sub001Block018Part022

theorem surrogateDiagonalTailChunk001Sub001Block018Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block018Part022CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block018Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block018Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block018Part022CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block018Part022SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block018Part022] using hcert

def TailChunk001Sub001Block018Part023SupportExplicit : Finset ℕ :=
  ([25503] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block018Part023 : ℚ :=
  (180649999 : ℚ) / 8353770420000000

def SurrogateDiagonalTailChunk001Sub001Block018Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25503
    = surrogateDiagTailX0RatChunk001Sub001Block018Part023

theorem surrogateDiagonalTailChunk001Sub001Block018Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block018Part023CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block018Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block018Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block018Part023CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block018Part023SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block018Part023] using hcert

def TailChunk001Sub001Block018Part024SupportExplicit : Finset ℕ :=
  ([25505] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block018Part024 : ℚ :=
  (13015004399 : ℚ) / 3464475668582400000

def SurrogateDiagonalTailChunk001Sub001Block018Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25505
    = surrogateDiagTailX0RatChunk001Sub001Block018Part024

theorem surrogateDiagonalTailChunk001Sub001Block018Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block018Part024CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block018Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block018Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block018Part024CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block018Part024SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block018Part024] using hcert

def surrogateDiagonalTailChunk001Sub001Block018HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub001Block018Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block018Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block018Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block018Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block018Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block018Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block018Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block018Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block018Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block018Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub001Block018Head : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block018Part000
    + surrogateDiagTailX0RatChunk001Sub001Block018Part001
    + surrogateDiagTailX0RatChunk001Sub001Block018Part002
    + surrogateDiagTailX0RatChunk001Sub001Block018Part003
    + surrogateDiagTailX0RatChunk001Sub001Block018Part004
    + surrogateDiagTailX0RatChunk001Sub001Block018Part005
    + surrogateDiagTailX0RatChunk001Sub001Block018Part006
    + surrogateDiagTailX0RatChunk001Sub001Block018Part007
    + surrogateDiagTailX0RatChunk001Sub001Block018Part008
    + surrogateDiagTailX0RatChunk001Sub001Block018Part009

def surrogateDiagonalTailChunk001Sub001Block018MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub001Block018Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block018Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block018Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block018Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block018Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block018Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block018Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block018Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block018Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block018Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub001Block018Mid : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block018Part010
    + surrogateDiagTailX0RatChunk001Sub001Block018Part011
    + surrogateDiagTailX0RatChunk001Sub001Block018Part012
    + surrogateDiagTailX0RatChunk001Sub001Block018Part013
    + surrogateDiagTailX0RatChunk001Sub001Block018Part014
    + surrogateDiagTailX0RatChunk001Sub001Block018Part015
    + surrogateDiagTailX0RatChunk001Sub001Block018Part016
    + surrogateDiagTailX0RatChunk001Sub001Block018Part017
    + surrogateDiagTailX0RatChunk001Sub001Block018Part018
    + surrogateDiagTailX0RatChunk001Sub001Block018Part019

def surrogateDiagonalTailChunk001Sub001Block018TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub001Block018Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block018Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block018Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block018Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block018Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub001Block018Tail : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block018Part020
    + surrogateDiagTailX0RatChunk001Sub001Block018Part021
    + surrogateDiagTailX0RatChunk001Sub001Block018Part022
    + surrogateDiagTailX0RatChunk001Sub001Block018Part023
    + surrogateDiagTailX0RatChunk001Sub001Block018Part024

def surrogateDiagonalTailChunk001Sub001Block018Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk001Sub001Block018HeadSum X0
    + surrogateDiagonalTailChunk001Sub001Block018MidSum X0
    + surrogateDiagonalTailChunk001Sub001Block018TailSum X0

def surrogateDiagTailX0RatChunk001Sub001Block018 : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block018Part000
    + surrogateDiagTailX0RatChunk001Sub001Block018Part001
    + surrogateDiagTailX0RatChunk001Sub001Block018Part002
    + surrogateDiagTailX0RatChunk001Sub001Block018Part003
    + surrogateDiagTailX0RatChunk001Sub001Block018Part004
    + surrogateDiagTailX0RatChunk001Sub001Block018Part005
    + surrogateDiagTailX0RatChunk001Sub001Block018Part006
    + surrogateDiagTailX0RatChunk001Sub001Block018Part007
    + surrogateDiagTailX0RatChunk001Sub001Block018Part008
    + surrogateDiagTailX0RatChunk001Sub001Block018Part009
    + surrogateDiagTailX0RatChunk001Sub001Block018Part010
    + surrogateDiagTailX0RatChunk001Sub001Block018Part011
    + surrogateDiagTailX0RatChunk001Sub001Block018Part012
    + surrogateDiagTailX0RatChunk001Sub001Block018Part013
    + surrogateDiagTailX0RatChunk001Sub001Block018Part014
    + surrogateDiagTailX0RatChunk001Sub001Block018Part015
    + surrogateDiagTailX0RatChunk001Sub001Block018Part016
    + surrogateDiagTailX0RatChunk001Sub001Block018Part017
    + surrogateDiagTailX0RatChunk001Sub001Block018Part018
    + surrogateDiagTailX0RatChunk001Sub001Block018Part019
    + surrogateDiagTailX0RatChunk001Sub001Block018Part020
    + surrogateDiagTailX0RatChunk001Sub001Block018Part021
    + surrogateDiagTailX0RatChunk001Sub001Block018Part022
    + surrogateDiagTailX0RatChunk001Sub001Block018Part023
    + surrogateDiagTailX0RatChunk001Sub001Block018Part024

theorem surrogateDiagTailX0RatChunk001Sub001Block018_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk001Sub001Block018Head + surrogateDiagTailX0RatChunk001Sub001Block018Mid + surrogateDiagTailX0RatChunk001Sub001Block018Tail =
      surrogateDiagTailX0RatChunk001Sub001Block018 := by
  unfold surrogateDiagTailX0RatChunk001Sub001Block018Head surrogateDiagTailX0RatChunk001Sub001Block018Mid surrogateDiagTailX0RatChunk001Sub001Block018Tail surrogateDiagTailX0RatChunk001Sub001Block018
  ring

def SurrogateDiagonalTailChunk001Sub001Block018HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub001Block018HeadSum X0 = surrogateDiagTailX0RatChunk001Sub001Block018Head

def SurrogateDiagonalTailChunk001Sub001Block018MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub001Block018MidSum X0 = surrogateDiagTailX0RatChunk001Sub001Block018Mid

def SurrogateDiagonalTailChunk001Sub001Block018TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub001Block018TailSum X0 = surrogateDiagTailX0RatChunk001Sub001Block018Tail

theorem surrogateDiagonalTailChunk001Sub001Block018_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk001Sub001Block018HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk001Sub001Block018MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk001Sub001Block018TailCertificateAt X0) :
    surrogateDiagonalTailChunk001Sub001Block018Sum X0 = surrogateDiagTailX0RatChunk001Sub001Block018 := by
  unfold SurrogateDiagonalTailChunk001Sub001Block018HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk001Sub001Block018MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk001Sub001Block018TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk001Sub001Block018Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk001Sub001Block018_eq_head_add_mid_add_tail

/-- Block 019 covers tail-support indices [15475,15500) and q from 25507 to 25553. -/

def TailChunk001Sub001Block019Part000SupportExplicit : Finset ℕ :=
  ([25507] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block019Part000 : ℚ :=
  (130067695425 : ℚ) / 294276355628483024896

def SurrogateDiagonalTailChunk001Sub001Block019Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25507
    = surrogateDiagTailX0RatChunk001Sub001Block019Part000

theorem surrogateDiagonalTailChunk001Sub001Block019Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block019Part000CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block019Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block019Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block019Part000CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block019Part000SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block019Part000] using hcert

def TailChunk001Sub001Block019Part001SupportExplicit : Finset ℕ :=
  ([25509] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block019Part001 : ℚ :=
  (167129181103 : ℚ) / 5684287482266419200

def SurrogateDiagonalTailChunk001Sub001Block019Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25509
    = surrogateDiagTailX0RatChunk001Sub001Block019Part001

theorem surrogateDiagonalTailChunk001Sub001Block019Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block019Part001CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block019Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block019Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block019Part001CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block019Part001SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block019Part001] using hcert

def TailChunk001Sub001Block019Part002SupportExplicit : Finset ℕ :=
  ([25510] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block019Part002 : ℚ :=
  (3261256949 : ℚ) / 216529729286400000

def SurrogateDiagonalTailChunk001Sub001Block019Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25510
    = surrogateDiagTailX0RatChunk001Sub001Block019Part002

theorem surrogateDiagonalTailChunk001Sub001Block019Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block019Part002CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block019Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block019Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block019Part002CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block019Part002SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block019Part002] using hcert

def TailChunk001Sub001Block019Part003SupportExplicit : Finset ℕ :=
  ([25511] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block019Part003 : ℚ :=
  (37159903325 : ℚ) / 333576695094114779136

def SurrogateDiagonalTailChunk001Sub001Block019Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25511
    = surrogateDiagTailX0RatChunk001Sub001Block019Part003

theorem surrogateDiagonalTailChunk001Sub001Block019Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block019Part003CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block019Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block019Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block019Part003CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block019Part003SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block019Part003] using hcert

def TailChunk001Sub001Block019Part004SupportExplicit : Finset ℕ :=
  ([25513] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block019Part004 : ℚ :=
  (10499554327 : ℚ) / 36987854387995267200

def SurrogateDiagonalTailChunk001Sub001Block019Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25513
    = surrogateDiagTailX0RatChunk001Sub001Block019Part004

theorem surrogateDiagonalTailChunk001Sub001Block019Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block019Part004CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block019Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block019Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block019Part004CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block019Part004SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block019Part004] using hcert

def TailChunk001Sub001Block019Part005SupportExplicit : Finset ℕ :=
  ([25514] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block019Part005 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block019Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25514
    = surrogateDiagTailX0RatChunk001Sub001Block019Part005

theorem surrogateDiagonalTailChunk001Sub001Block019Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block019Part005CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block019Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block019Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block019Part005CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block019Part005SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block019Part005] using hcert

def TailChunk001Sub001Block019Part006SupportExplicit : Finset ℕ :=
  ([25517] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block019Part006 : ℚ :=
  (436335124325 : ℚ) / 318379594314525179904

def SurrogateDiagonalTailChunk001Sub001Block019Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25517
    = surrogateDiagTailX0RatChunk001Sub001Block019Part006

theorem surrogateDiagonalTailChunk001Sub001Block019Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block019Part006CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block019Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block019Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block019Part006CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block019Part006SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block019Part006] using hcert

def TailChunk001Sub001Block019Part007SupportExplicit : Finset ℕ :=
  ([25518] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block019Part007 : ℚ :=
  (70662130075 : ℚ) / 817334596447483008

def SurrogateDiagonalTailChunk001Sub001Block019Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25518
    = surrogateDiagTailX0RatChunk001Sub001Block019Part007

theorem surrogateDiagonalTailChunk001Sub001Block019Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block019Part007CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block019Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block019Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block019Part007CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block019Part007SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block019Part007] using hcert

def TailChunk001Sub001Block019Part008SupportExplicit : Finset ℕ :=
  ([25521] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block019Part008 : ℚ :=
  (35428950161 : ℚ) / 1504382163648675840

def SurrogateDiagonalTailChunk001Sub001Block019Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25521
    = surrogateDiagTailX0RatChunk001Sub001Block019Part008

theorem surrogateDiagonalTailChunk001Sub001Block019Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block019Part008CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block019Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block019Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block019Part008CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block019Part008SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block019Part008] using hcert

def TailChunk001Sub001Block019Part009SupportExplicit : Finset ℕ :=
  ([25522] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block019Part009 : ℚ :=
  (34670355475 : ℚ) / 1984051065641034816

def SurrogateDiagonalTailChunk001Sub001Block019Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25522
    = surrogateDiagTailX0RatChunk001Sub001Block019Part009

theorem surrogateDiagonalTailChunk001Sub001Block019Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block019Part009CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block019Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block019Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block019Part009CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block019Part009SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block019Part009] using hcert

def TailChunk001Sub001Block019Part010SupportExplicit : Finset ℕ :=
  ([25523] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block019Part010 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block019Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25523
    = surrogateDiagTailX0RatChunk001Sub001Block019Part010

theorem surrogateDiagonalTailChunk001Sub001Block019Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block019Part010CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block019Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block019Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block019Part010CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block019Part010SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block019Part010] using hcert

def TailChunk001Sub001Block019Part011SupportExplicit : Finset ℕ :=
  ([25526] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block019Part011 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block019Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25526
    = surrogateDiagTailX0RatChunk001Sub001Block019Part011

theorem surrogateDiagonalTailChunk001Sub001Block019Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block019Part011CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block019Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block019Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block019Part011CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block019Part011SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block019Part011] using hcert

def TailChunk001Sub001Block019Part012SupportExplicit : Finset ℕ :=
  ([25527] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block019Part012 : ℚ :=
  (4439803363075 : ℚ) / 191339557023062181888

def SurrogateDiagonalTailChunk001Sub001Block019Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25527
    = surrogateDiagTailX0RatChunk001Sub001Block019Part012

theorem surrogateDiagonalTailChunk001Sub001Block019Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block019Part012CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block019Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block019Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block019Part012CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block019Part012SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block019Part012] using hcert

def TailChunk001Sub001Block019Part013SupportExplicit : Finset ℕ :=
  ([25530] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block019Part013 : ℚ :=
  (108860479025 : ℚ) / 366348863042224128

def SurrogateDiagonalTailChunk001Sub001Block019Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25530
    = surrogateDiagTailX0RatChunk001Sub001Block019Part013

theorem surrogateDiagonalTailChunk001Sub001Block019Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block019Part013CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block019Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block019Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block019Part013CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block019Part013SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block019Part013] using hcert

def TailChunk001Sub001Block019Part014SupportExplicit : Finset ℕ :=
  ([25534] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block019Part014 : ℚ :=
  (5015933237 : ℚ) / 1037007360000000000

def SurrogateDiagonalTailChunk001Sub001Block019Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25534
    = surrogateDiagTailX0RatChunk001Sub001Block019Part014

theorem surrogateDiagonalTailChunk001Sub001Block019Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block019Part014CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block019Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block019Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block019Part014CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block019Part014SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block019Part014] using hcert

def TailChunk001Sub001Block019Part015SupportExplicit : Finset ℕ :=
  ([25535] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block019Part015 : ℚ :=
  (44073048625 : ℚ) / 11759486070261786624

def SurrogateDiagonalTailChunk001Sub001Block019Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25535
    = surrogateDiagTailX0RatChunk001Sub001Block019Part015

theorem surrogateDiagonalTailChunk001Sub001Block019Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block019Part015CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block019Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block019Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block019Part015CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block019Part015SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block019Part015] using hcert

def TailChunk001Sub001Block019Part016SupportExplicit : Finset ℕ :=
  ([25537] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block019Part016 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block019Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25537
    = surrogateDiagTailX0RatChunk001Sub001Block019Part016

theorem surrogateDiagonalTailChunk001Sub001Block019Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block019Part016CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block019Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block019Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block019Part016CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block019Part016SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block019Part016] using hcert

def TailChunk001Sub001Block019Part017SupportExplicit : Finset ℕ :=
  ([25539] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block019Part017 : ℚ :=
  (161750320525 : ℚ) / 7500932719098986496

def SurrogateDiagonalTailChunk001Sub001Block019Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25539
    = surrogateDiagTailX0RatChunk001Sub001Block019Part017

theorem surrogateDiagonalTailChunk001Sub001Block019Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block019Part017CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block019Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block019Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block019Part017CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block019Part017SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block019Part017] using hcert

def TailChunk001Sub001Block019Part018SupportExplicit : Finset ℕ :=
  ([25541] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block019Part018 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block019Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25541
    = surrogateDiagTailX0RatChunk001Sub001Block019Part018

theorem surrogateDiagonalTailChunk001Sub001Block019Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block019Part018CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block019Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block019Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block019Part018CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block019Part018SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block019Part018] using hcert

def TailChunk001Sub001Block019Part019SupportExplicit : Finset ℕ :=
  ([25543] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block019Part019 : ℚ :=
  (40419471661 : ℚ) / 19900432066491187200

def SurrogateDiagonalTailChunk001Sub001Block019Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25543
    = surrogateDiagTailX0RatChunk001Sub001Block019Part019

theorem surrogateDiagonalTailChunk001Sub001Block019Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block019Part019CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block019Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block019Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block019Part019CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block019Part019SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block019Part019] using hcert

def TailChunk001Sub001Block019Part020SupportExplicit : Finset ℕ :=
  ([25545] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block019Part020 : ℚ :=
  (34854901789 : ℚ) / 606575968439500800

def SurrogateDiagonalTailChunk001Sub001Block019Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25545
    = surrogateDiagTailX0RatChunk001Sub001Block019Part020

theorem surrogateDiagonalTailChunk001Sub001Block019Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block019Part020CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block019Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block019Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block019Part020CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block019Part020SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block019Part020] using hcert

def TailChunk001Sub001Block019Part021SupportExplicit : Finset ℕ :=
  ([25546] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block019Part021 : ℚ :=
  (366616867 : ℚ) / 242630387375800320

def SurrogateDiagonalTailChunk001Sub001Block019Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25546
    = surrogateDiagTailX0RatChunk001Sub001Block019Part021

theorem surrogateDiagonalTailChunk001Sub001Block019Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block019Part021CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block019Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block019Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block019Part021CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block019Part021SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block019Part021] using hcert

def TailChunk001Sub001Block019Part022SupportExplicit : Finset ℕ :=
  ([25547] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block019Part022 : ℚ :=
  (39459519475 : ℚ) / 246384753079342989312

def SurrogateDiagonalTailChunk001Sub001Block019Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25547
    = surrogateDiagTailX0RatChunk001Sub001Block019Part022

theorem surrogateDiagonalTailChunk001Sub001Block019Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block019Part022CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block019Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block019Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block019Part022CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block019Part022SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block019Part022] using hcert

def TailChunk001Sub001Block019Part023SupportExplicit : Finset ℕ :=
  ([25549] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block019Part023 : ℚ :=
  (11953668271 : ℚ) / 36868007246639923200

def SurrogateDiagonalTailChunk001Sub001Block019Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25549
    = surrogateDiagTailX0RatChunk001Sub001Block019Part023

theorem surrogateDiagonalTailChunk001Sub001Block019Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block019Part023CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block019Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block019Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block019Part023CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block019Part023SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block019Part023] using hcert

def TailChunk001Sub001Block019Part024SupportExplicit : Finset ℕ :=
  ([25553] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block019Part024 : ℚ :=
  (7866457 : ℚ) / 4840968000000000

def SurrogateDiagonalTailChunk001Sub001Block019Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25553
    = surrogateDiagTailX0RatChunk001Sub001Block019Part024

theorem surrogateDiagonalTailChunk001Sub001Block019Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block019Part024CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block019Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block019Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block019Part024CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block019Part024SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block019Part024] using hcert

def surrogateDiagonalTailChunk001Sub001Block019HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub001Block019Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block019Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block019Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block019Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block019Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block019Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block019Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block019Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block019Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block019Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub001Block019Head : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block019Part000
    + surrogateDiagTailX0RatChunk001Sub001Block019Part001
    + surrogateDiagTailX0RatChunk001Sub001Block019Part002
    + surrogateDiagTailX0RatChunk001Sub001Block019Part003
    + surrogateDiagTailX0RatChunk001Sub001Block019Part004
    + surrogateDiagTailX0RatChunk001Sub001Block019Part005
    + surrogateDiagTailX0RatChunk001Sub001Block019Part006
    + surrogateDiagTailX0RatChunk001Sub001Block019Part007
    + surrogateDiagTailX0RatChunk001Sub001Block019Part008
    + surrogateDiagTailX0RatChunk001Sub001Block019Part009

def surrogateDiagonalTailChunk001Sub001Block019MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub001Block019Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block019Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block019Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block019Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block019Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block019Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block019Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block019Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block019Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block019Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub001Block019Mid : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block019Part010
    + surrogateDiagTailX0RatChunk001Sub001Block019Part011
    + surrogateDiagTailX0RatChunk001Sub001Block019Part012
    + surrogateDiagTailX0RatChunk001Sub001Block019Part013
    + surrogateDiagTailX0RatChunk001Sub001Block019Part014
    + surrogateDiagTailX0RatChunk001Sub001Block019Part015
    + surrogateDiagTailX0RatChunk001Sub001Block019Part016
    + surrogateDiagTailX0RatChunk001Sub001Block019Part017
    + surrogateDiagTailX0RatChunk001Sub001Block019Part018
    + surrogateDiagTailX0RatChunk001Sub001Block019Part019

def surrogateDiagonalTailChunk001Sub001Block019TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub001Block019Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block019Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block019Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block019Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block019Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub001Block019Tail : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block019Part020
    + surrogateDiagTailX0RatChunk001Sub001Block019Part021
    + surrogateDiagTailX0RatChunk001Sub001Block019Part022
    + surrogateDiagTailX0RatChunk001Sub001Block019Part023
    + surrogateDiagTailX0RatChunk001Sub001Block019Part024

def surrogateDiagonalTailChunk001Sub001Block019Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk001Sub001Block019HeadSum X0
    + surrogateDiagonalTailChunk001Sub001Block019MidSum X0
    + surrogateDiagonalTailChunk001Sub001Block019TailSum X0

def surrogateDiagTailX0RatChunk001Sub001Block019 : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block019Part000
    + surrogateDiagTailX0RatChunk001Sub001Block019Part001
    + surrogateDiagTailX0RatChunk001Sub001Block019Part002
    + surrogateDiagTailX0RatChunk001Sub001Block019Part003
    + surrogateDiagTailX0RatChunk001Sub001Block019Part004
    + surrogateDiagTailX0RatChunk001Sub001Block019Part005
    + surrogateDiagTailX0RatChunk001Sub001Block019Part006
    + surrogateDiagTailX0RatChunk001Sub001Block019Part007
    + surrogateDiagTailX0RatChunk001Sub001Block019Part008
    + surrogateDiagTailX0RatChunk001Sub001Block019Part009
    + surrogateDiagTailX0RatChunk001Sub001Block019Part010
    + surrogateDiagTailX0RatChunk001Sub001Block019Part011
    + surrogateDiagTailX0RatChunk001Sub001Block019Part012
    + surrogateDiagTailX0RatChunk001Sub001Block019Part013
    + surrogateDiagTailX0RatChunk001Sub001Block019Part014
    + surrogateDiagTailX0RatChunk001Sub001Block019Part015
    + surrogateDiagTailX0RatChunk001Sub001Block019Part016
    + surrogateDiagTailX0RatChunk001Sub001Block019Part017
    + surrogateDiagTailX0RatChunk001Sub001Block019Part018
    + surrogateDiagTailX0RatChunk001Sub001Block019Part019
    + surrogateDiagTailX0RatChunk001Sub001Block019Part020
    + surrogateDiagTailX0RatChunk001Sub001Block019Part021
    + surrogateDiagTailX0RatChunk001Sub001Block019Part022
    + surrogateDiagTailX0RatChunk001Sub001Block019Part023
    + surrogateDiagTailX0RatChunk001Sub001Block019Part024

theorem surrogateDiagTailX0RatChunk001Sub001Block019_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk001Sub001Block019Head + surrogateDiagTailX0RatChunk001Sub001Block019Mid + surrogateDiagTailX0RatChunk001Sub001Block019Tail =
      surrogateDiagTailX0RatChunk001Sub001Block019 := by
  unfold surrogateDiagTailX0RatChunk001Sub001Block019Head surrogateDiagTailX0RatChunk001Sub001Block019Mid surrogateDiagTailX0RatChunk001Sub001Block019Tail surrogateDiagTailX0RatChunk001Sub001Block019
  ring

def SurrogateDiagonalTailChunk001Sub001Block019HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub001Block019HeadSum X0 = surrogateDiagTailX0RatChunk001Sub001Block019Head

def SurrogateDiagonalTailChunk001Sub001Block019MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub001Block019MidSum X0 = surrogateDiagTailX0RatChunk001Sub001Block019Mid

def SurrogateDiagonalTailChunk001Sub001Block019TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub001Block019TailSum X0 = surrogateDiagTailX0RatChunk001Sub001Block019Tail

theorem surrogateDiagonalTailChunk001Sub001Block019_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk001Sub001Block019HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk001Sub001Block019MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk001Sub001Block019TailCertificateAt X0) :
    surrogateDiagonalTailChunk001Sub001Block019Sum X0 = surrogateDiagTailX0RatChunk001Sub001Block019 := by
  unfold SurrogateDiagonalTailChunk001Sub001Block019HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk001Sub001Block019MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk001Sub001Block019TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk001Sub001Block019Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk001Sub001Block019_eq_head_add_mid_add_tail

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

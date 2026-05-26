import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0TailPilot25

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

open scoped BigOperators

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

/- Generated direct-term certificate blocks for tail chunk 001, subchunk 001, blocks [60,70). -/

/-- Block 060 covers tail-support indices [16500,16525) and q from 27193 to 27231. -/

def TailChunk001Sub001Block060Part000SupportExplicit : Finset ℕ :=
  ([27193] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block060Part000 : ℚ :=
  (5601206113 : ℚ) / 51136672165551235200

def SurrogateDiagonalTailChunk001Sub001Block060Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27193
    = surrogateDiagTailX0RatChunk001Sub001Block060Part000

theorem surrogateDiagonalTailChunk001Sub001Block060Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block060Part000CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block060Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block060Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block060Part000CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block060Part000SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block060Part000] using hcert

def TailChunk001Sub001Block060Part001SupportExplicit : Finset ℕ :=
  ([27194] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block060Part001 : ℚ :=
  (2888725140625 : ℚ) / 21360503781931244832

def SurrogateDiagonalTailChunk001Sub001Block060Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27194
    = surrogateDiagTailX0RatChunk001Sub001Block060Part001

theorem surrogateDiagonalTailChunk001Sub001Block060Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block060Part001CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block060Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block060Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block060Part001CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block060Part001SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block060Part001] using hcert

def TailChunk001Sub001Block060Part002SupportExplicit : Finset ℕ :=
  ([27197] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block060Part002 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block060Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27197
    = surrogateDiagTailX0RatChunk001Sub001Block060Part002

theorem surrogateDiagonalTailChunk001Sub001Block060Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block060Part002CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block060Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block060Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block060Part002CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block060Part002SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block060Part002] using hcert

def TailChunk001Sub001Block060Part003SupportExplicit : Finset ℕ :=
  ([27199] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block060Part003 : ℚ :=
  (217816437 : ℚ) / 1689308224558627840

def SurrogateDiagonalTailChunk001Sub001Block060Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27199
    = surrogateDiagTailX0RatChunk001Sub001Block060Part003

theorem surrogateDiagonalTailChunk001Sub001Block060Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block060Part003CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block060Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block060Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block060Part003CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block060Part003SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block060Part003] using hcert

def TailChunk001Sub001Block060Part004SupportExplicit : Finset ℕ :=
  ([27201] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block060Part004 : ℚ :=
  (41675 : ℚ) / 18014889026215296

def SurrogateDiagonalTailChunk001Sub001Block060Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27201
    = surrogateDiagTailX0RatChunk001Sub001Block060Part004

theorem surrogateDiagonalTailChunk001Sub001Block060Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block060Part004CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block060Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block060Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block060Part004CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block060Part004SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block060Part004] using hcert

def TailChunk001Sub001Block060Part005SupportExplicit : Finset ℕ :=
  ([27202] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block060Part005 : ℚ :=
  (8052942379975 : ℚ) / 37795468053938208768

def SurrogateDiagonalTailChunk001Sub001Block060Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27202
    = surrogateDiagTailX0RatChunk001Sub001Block060Part005

theorem surrogateDiagonalTailChunk001Sub001Block060Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block060Part005CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block060Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block060Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block060Part005CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block060Part005SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block060Part005] using hcert

def TailChunk001Sub001Block060Part006SupportExplicit : Finset ℕ :=
  ([27203] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block060Part006 : ℚ :=
  (2556076213 : ℚ) / 3112429119239577600

def SurrogateDiagonalTailChunk001Sub001Block060Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27203
    = surrogateDiagTailX0RatChunk001Sub001Block060Part006

theorem surrogateDiagonalTailChunk001Sub001Block060Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block060Part006CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block060Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block060Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block060Part006CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block060Part006SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block060Part006] using hcert

def TailChunk001Sub001Block060Part007SupportExplicit : Finset ℕ :=
  ([27205] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block060Part007 : ℚ :=
  (4935601353 : ℚ) / 1494965448008007680

def SurrogateDiagonalTailChunk001Sub001Block060Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27205
    = surrogateDiagTailX0RatChunk001Sub001Block060Part007

theorem surrogateDiagonalTailChunk001Sub001Block060Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block060Part007CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block060Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block060Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block060Part007CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block060Part007SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block060Part007] using hcert

def TailChunk001Sub001Block060Part008SupportExplicit : Finset ℕ :=
  ([27206] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block060Part008 : ℚ :=
  (446936221723 : ℚ) / 3148500376336435200

def SurrogateDiagonalTailChunk001Sub001Block060Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27206
    = surrogateDiagTailX0RatChunk001Sub001Block060Part008

theorem surrogateDiagonalTailChunk001Sub001Block060Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block060Part008CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block060Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block060Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block060Part008CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block060Part008SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block060Part008] using hcert

def TailChunk001Sub001Block060Part009SupportExplicit : Finset ℕ :=
  ([27210] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block060Part009 : ℚ :=
  (3644849454475 : ℚ) / 6900802490816299008

def SurrogateDiagonalTailChunk001Sub001Block060Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27210
    = surrogateDiagTailX0RatChunk001Sub001Block060Part009

theorem surrogateDiagonalTailChunk001Sub001Block060Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block060Part009CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block060Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block060Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block060Part009CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block060Part009SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block060Part009] using hcert

def TailChunk001Sub001Block060Part010SupportExplicit : Finset ℕ :=
  ([27211] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block060Part010 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block060Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27211
    = surrogateDiagTailX0RatChunk001Sub001Block060Part010

theorem surrogateDiagonalTailChunk001Sub001Block060Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block060Part010CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block060Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block060Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block060Part010CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block060Part010SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block060Part010] using hcert

def TailChunk001Sub001Block060Part011SupportExplicit : Finset ℕ :=
  ([27213] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block060Part011 : ℚ :=
  (150655233625 : ℚ) / 243435035745381777408

def SurrogateDiagonalTailChunk001Sub001Block060Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27213
    = surrogateDiagTailX0RatChunk001Sub001Block060Part011

theorem surrogateDiagonalTailChunk001Sub001Block060Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block060Part011CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block060Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block060Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block060Part011CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block060Part011SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block060Part011] using hcert

def TailChunk001Sub001Block060Part012SupportExplicit : Finset ℕ :=
  ([27214] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block060Part012 : ℚ :=
  (131182608101 : ℚ) / 778107279809894400

def SurrogateDiagonalTailChunk001Sub001Block060Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27214
    = surrogateDiagTailX0RatChunk001Sub001Block060Part012

theorem surrogateDiagonalTailChunk001Sub001Block060Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block060Part012CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block060Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block060Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block060Part012CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block060Part012SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block060Part012] using hcert

def TailChunk001Sub001Block060Part013SupportExplicit : Finset ℕ :=
  ([27215] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block060Part013 : ℚ :=
  (1852210757125 : ℚ) / 561436927238058559488

def SurrogateDiagonalTailChunk001Sub001Block060Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27215
    = surrogateDiagTailX0RatChunk001Sub001Block060Part013

theorem surrogateDiagonalTailChunk001Sub001Block060Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block060Part013CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block060Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block060Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block060Part013CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block060Part013SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block060Part013] using hcert

def TailChunk001Sub001Block060Part014SupportExplicit : Finset ℕ :=
  ([27217] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block060Part014 : ℚ :=
  (404005833 : ℚ) / 894963810304000000

def SurrogateDiagonalTailChunk001Sub001Block060Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27217
    = surrogateDiagTailX0RatChunk001Sub001Block060Part014

theorem surrogateDiagonalTailChunk001Sub001Block060Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block060Part014CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block060Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block060Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block060Part014CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block060Part014SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block060Part014] using hcert

def TailChunk001Sub001Block060Part015SupportExplicit : Finset ℕ :=
  ([27218] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block060Part015 : ℚ :=
  (13667167883 : ℚ) / 93179061686420100

def SurrogateDiagonalTailChunk001Sub001Block060Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27218
    = surrogateDiagTailX0RatChunk001Sub001Block060Part015

theorem surrogateDiagonalTailChunk001Sub001Block060Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block060Part015CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block060Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block060Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block060Part015CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block060Part015SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block060Part015] using hcert

def TailChunk001Sub001Block060Part016SupportExplicit : Finset ℕ :=
  ([27219] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block060Part016 : ℚ :=
  (2939 : ℚ) / 4482709257600

def SurrogateDiagonalTailChunk001Sub001Block060Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27219
    = surrogateDiagTailX0RatChunk001Sub001Block060Part016

theorem surrogateDiagonalTailChunk001Sub001Block060Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block060Part016CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block060Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block060Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block060Part016CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block060Part016SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block060Part016] using hcert

def TailChunk001Sub001Block060Part017SupportExplicit : Finset ℕ :=
  ([27221] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block060Part017 : ℚ :=
  (50411260025 : ℚ) / 653866780235546908224

def SurrogateDiagonalTailChunk001Sub001Block060Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27221
    = surrogateDiagTailX0RatChunk001Sub001Block060Part017

theorem surrogateDiagonalTailChunk001Sub001Block060Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block060Part017CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block060Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block060Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block060Part017CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block060Part017SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block060Part017] using hcert

def TailChunk001Sub001Block060Part018SupportExplicit : Finset ℕ :=
  ([27222] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block060Part018 : ℚ :=
  (78558385825 : ℚ) / 209778418969214976

def SurrogateDiagonalTailChunk001Sub001Block060Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27222
    = surrogateDiagTailX0RatChunk001Sub001Block060Part018

theorem surrogateDiagonalTailChunk001Sub001Block060Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block060Part018CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block060Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block060Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block060Part018CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block060Part018SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block060Part018] using hcert

def TailChunk001Sub001Block060Part019SupportExplicit : Finset ℕ :=
  ([27223] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block060Part019 : ℚ :=
  (946658944225 : ℚ) / 740520158529575190528

def SurrogateDiagonalTailChunk001Sub001Block060Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27223
    = surrogateDiagTailX0RatChunk001Sub001Block060Part019

theorem surrogateDiagonalTailChunk001Sub001Block060Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block060Part019CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block060Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block060Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block060Part019CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block060Part019SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block060Part019] using hcert

def TailChunk001Sub001Block060Part020SupportExplicit : Finset ℕ :=
  ([27226] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block060Part020 : ℚ :=
  (2895527640625 : ℚ) / 21461231005088392992

def SurrogateDiagonalTailChunk001Sub001Block060Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27226
    = surrogateDiagTailX0RatChunk001Sub001Block060Part020

theorem surrogateDiagonalTailChunk001Sub001Block060Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block060Part020CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block060Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block060Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block060Part020CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block060Part020SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block060Part020] using hcert

def TailChunk001Sub001Block060Part021SupportExplicit : Finset ℕ :=
  ([27227] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block060Part021 : ℚ :=
  (517971155725 : ℚ) / 1103796343809574207488

def SurrogateDiagonalTailChunk001Sub001Block060Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27227
    = surrogateDiagTailX0RatChunk001Sub001Block060Part021

theorem surrogateDiagonalTailChunk001Sub001Block060Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block060Part021CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block060Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block060Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block060Part021CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block060Part021SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block060Part021] using hcert

def TailChunk001Sub001Block060Part022SupportExplicit : Finset ℕ :=
  ([27229] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block060Part022 : ℚ :=
  (1245500125 : ℚ) / 11915296358903709696

def SurrogateDiagonalTailChunk001Sub001Block060Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27229
    = surrogateDiagTailX0RatChunk001Sub001Block060Part022

theorem surrogateDiagonalTailChunk001Sub001Block060Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block060Part022CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block060Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block060Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block060Part022CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block060Part022SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block060Part022] using hcert

def TailChunk001Sub001Block060Part023SupportExplicit : Finset ℕ :=
  ([27230] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block060Part023 : ℚ :=
  (667835606425 : ℚ) / 2089085519018852352

def SurrogateDiagonalTailChunk001Sub001Block060Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27230
    = surrogateDiagTailX0RatChunk001Sub001Block060Part023

theorem surrogateDiagonalTailChunk001Sub001Block060Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block060Part023CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block060Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block060Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block060Part023CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block060Part023SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block060Part023] using hcert

def TailChunk001Sub001Block060Part024SupportExplicit : Finset ℕ :=
  ([27231] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block060Part024 : ℚ :=
  (17171040875 : ℚ) / 19418518669643218944

def SurrogateDiagonalTailChunk001Sub001Block060Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27231
    = surrogateDiagTailX0RatChunk001Sub001Block060Part024

theorem surrogateDiagonalTailChunk001Sub001Block060Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block060Part024CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block060Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block060Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block060Part024CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block060Part024SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block060Part024] using hcert

def surrogateDiagonalTailChunk001Sub001Block060HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub001Block060Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block060Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block060Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block060Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block060Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block060Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block060Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block060Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block060Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block060Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub001Block060Head : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block060Part000
    + surrogateDiagTailX0RatChunk001Sub001Block060Part001
    + surrogateDiagTailX0RatChunk001Sub001Block060Part002
    + surrogateDiagTailX0RatChunk001Sub001Block060Part003
    + surrogateDiagTailX0RatChunk001Sub001Block060Part004
    + surrogateDiagTailX0RatChunk001Sub001Block060Part005
    + surrogateDiagTailX0RatChunk001Sub001Block060Part006
    + surrogateDiagTailX0RatChunk001Sub001Block060Part007
    + surrogateDiagTailX0RatChunk001Sub001Block060Part008
    + surrogateDiagTailX0RatChunk001Sub001Block060Part009

def surrogateDiagonalTailChunk001Sub001Block060MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub001Block060Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block060Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block060Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block060Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block060Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block060Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block060Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block060Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block060Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block060Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub001Block060Mid : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block060Part010
    + surrogateDiagTailX0RatChunk001Sub001Block060Part011
    + surrogateDiagTailX0RatChunk001Sub001Block060Part012
    + surrogateDiagTailX0RatChunk001Sub001Block060Part013
    + surrogateDiagTailX0RatChunk001Sub001Block060Part014
    + surrogateDiagTailX0RatChunk001Sub001Block060Part015
    + surrogateDiagTailX0RatChunk001Sub001Block060Part016
    + surrogateDiagTailX0RatChunk001Sub001Block060Part017
    + surrogateDiagTailX0RatChunk001Sub001Block060Part018
    + surrogateDiagTailX0RatChunk001Sub001Block060Part019

def surrogateDiagonalTailChunk001Sub001Block060TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub001Block060Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block060Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block060Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block060Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block060Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub001Block060Tail : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block060Part020
    + surrogateDiagTailX0RatChunk001Sub001Block060Part021
    + surrogateDiagTailX0RatChunk001Sub001Block060Part022
    + surrogateDiagTailX0RatChunk001Sub001Block060Part023
    + surrogateDiagTailX0RatChunk001Sub001Block060Part024

def surrogateDiagonalTailChunk001Sub001Block060Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk001Sub001Block060HeadSum X0
    + surrogateDiagonalTailChunk001Sub001Block060MidSum X0
    + surrogateDiagonalTailChunk001Sub001Block060TailSum X0

def surrogateDiagTailX0RatChunk001Sub001Block060 : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block060Part000
    + surrogateDiagTailX0RatChunk001Sub001Block060Part001
    + surrogateDiagTailX0RatChunk001Sub001Block060Part002
    + surrogateDiagTailX0RatChunk001Sub001Block060Part003
    + surrogateDiagTailX0RatChunk001Sub001Block060Part004
    + surrogateDiagTailX0RatChunk001Sub001Block060Part005
    + surrogateDiagTailX0RatChunk001Sub001Block060Part006
    + surrogateDiagTailX0RatChunk001Sub001Block060Part007
    + surrogateDiagTailX0RatChunk001Sub001Block060Part008
    + surrogateDiagTailX0RatChunk001Sub001Block060Part009
    + surrogateDiagTailX0RatChunk001Sub001Block060Part010
    + surrogateDiagTailX0RatChunk001Sub001Block060Part011
    + surrogateDiagTailX0RatChunk001Sub001Block060Part012
    + surrogateDiagTailX0RatChunk001Sub001Block060Part013
    + surrogateDiagTailX0RatChunk001Sub001Block060Part014
    + surrogateDiagTailX0RatChunk001Sub001Block060Part015
    + surrogateDiagTailX0RatChunk001Sub001Block060Part016
    + surrogateDiagTailX0RatChunk001Sub001Block060Part017
    + surrogateDiagTailX0RatChunk001Sub001Block060Part018
    + surrogateDiagTailX0RatChunk001Sub001Block060Part019
    + surrogateDiagTailX0RatChunk001Sub001Block060Part020
    + surrogateDiagTailX0RatChunk001Sub001Block060Part021
    + surrogateDiagTailX0RatChunk001Sub001Block060Part022
    + surrogateDiagTailX0RatChunk001Sub001Block060Part023
    + surrogateDiagTailX0RatChunk001Sub001Block060Part024

theorem surrogateDiagTailX0RatChunk001Sub001Block060_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk001Sub001Block060Head + surrogateDiagTailX0RatChunk001Sub001Block060Mid + surrogateDiagTailX0RatChunk001Sub001Block060Tail =
      surrogateDiagTailX0RatChunk001Sub001Block060 := by
  unfold surrogateDiagTailX0RatChunk001Sub001Block060Head surrogateDiagTailX0RatChunk001Sub001Block060Mid surrogateDiagTailX0RatChunk001Sub001Block060Tail surrogateDiagTailX0RatChunk001Sub001Block060
  ring

def SurrogateDiagonalTailChunk001Sub001Block060HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub001Block060HeadSum X0 = surrogateDiagTailX0RatChunk001Sub001Block060Head

def SurrogateDiagonalTailChunk001Sub001Block060MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub001Block060MidSum X0 = surrogateDiagTailX0RatChunk001Sub001Block060Mid

def SurrogateDiagonalTailChunk001Sub001Block060TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub001Block060TailSum X0 = surrogateDiagTailX0RatChunk001Sub001Block060Tail

theorem surrogateDiagonalTailChunk001Sub001Block060_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk001Sub001Block060HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk001Sub001Block060MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk001Sub001Block060TailCertificateAt X0) :
    surrogateDiagonalTailChunk001Sub001Block060Sum X0 = surrogateDiagTailX0RatChunk001Sub001Block060 := by
  unfold SurrogateDiagonalTailChunk001Sub001Block060HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk001Sub001Block060MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk001Sub001Block060TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk001Sub001Block060Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk001Sub001Block060_eq_head_add_mid_add_tail

/-- Block 061 covers tail-support indices [16525,16550) and q from 27233 to 27271. -/

def TailChunk001Sub001Block061Part000SupportExplicit : Finset ℕ :=
  ([27233] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block061Part000 : ℚ :=
  (14079973 : ℚ) / 165765196944506880

def SurrogateDiagonalTailChunk001Sub001Block061Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27233
    = surrogateDiagTailX0RatChunk001Sub001Block061Part000

theorem surrogateDiagonalTailChunk001Sub001Block061Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block061Part000CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block061Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block061Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block061Part000CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block061Part000SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block061Part000] using hcert

def TailChunk001Sub001Block061Part001SupportExplicit : Finset ℕ :=
  ([27235] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block061Part001 : ℚ :=
  (1099465467725 : ℚ) / 202612828698218594304

def SurrogateDiagonalTailChunk001Sub001Block061Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27235
    = surrogateDiagTailX0RatChunk001Sub001Block061Part001

theorem surrogateDiagonalTailChunk001Sub001Block061Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block061Part001CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block061Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block061Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block061Part001CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block061Part001SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block061Part001] using hcert

def TailChunk001Sub001Block061Part002SupportExplicit : Finset ℕ :=
  ([27237] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block061Part002 : ℚ :=
  (738707125975 : ℚ) / 146275586870039543808

def SurrogateDiagonalTailChunk001Sub001Block061Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27237
    = surrogateDiagTailX0RatChunk001Sub001Block061Part002

theorem surrogateDiagonalTailChunk001Sub001Block061Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block061Part002CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block061Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block061Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block061Part002CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block061Part002SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block061Part002] using hcert

def TailChunk001Sub001Block061Part003SupportExplicit : Finset ℕ :=
  ([27238] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block061Part003 : ℚ :=
  (2898080640625 : ℚ) / 21499095404042560722

def SurrogateDiagonalTailChunk001Sub001Block061Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27238
    = surrogateDiagTailX0RatChunk001Sub001Block061Part003

theorem surrogateDiagonalTailChunk001Sub001Block061Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block061Part003CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block061Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block061Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block061Part003CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block061Part003SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block061Part003] using hcert

def TailChunk001Sub001Block061Part004SupportExplicit : Finset ℕ :=
  ([27239] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block061Part004 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block061Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27239
    = surrogateDiagTailX0RatChunk001Sub001Block061Part004

theorem surrogateDiagonalTailChunk001Sub001Block061Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block061Part004CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block061Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block061Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block061Part004CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block061Part004SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block061Part004] using hcert

def TailChunk001Sub001Block061Part005SupportExplicit : Finset ℕ :=
  ([27241] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block061Part005 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block061Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27241
    = surrogateDiagTailX0RatChunk001Sub001Block061Part005

theorem surrogateDiagonalTailChunk001Sub001Block061Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block061Part005CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block061Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block061Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block061Part005CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block061Part005SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block061Part005] using hcert

def TailChunk001Sub001Block061Part006SupportExplicit : Finset ℕ :=
  ([27242] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block061Part006 : ℚ :=
  (2791697401375 : ℚ) / 19630895144519073792

def SurrogateDiagonalTailChunk001Sub001Block061Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27242
    = surrogateDiagTailX0RatChunk001Sub001Block061Part006

theorem surrogateDiagonalTailChunk001Sub001Block061Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block061Part006CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block061Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block061Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block061Part006CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block061Part006SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block061Part006] using hcert

def TailChunk001Sub001Block061Part007SupportExplicit : Finset ℕ :=
  ([27245] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block061Part007 : ℚ :=
  (1856294506375 : ℚ) / 563917042415105998848

def SurrogateDiagonalTailChunk001Sub001Block061Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27245
    = surrogateDiagTailX0RatChunk001Sub001Block061Part007

theorem surrogateDiagonalTailChunk001Sub001Block061Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block061Part007CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block061Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block061Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block061Part007CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block061Part007SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block061Part007] using hcert

def TailChunk001Sub001Block061Part008SupportExplicit : Finset ℕ :=
  ([27246] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block061Part008 : ℚ :=
  (4730306654575 : ℚ) / 13475493850031474688

def SurrogateDiagonalTailChunk001Sub001Block061Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27246
    = surrogateDiagTailX0RatChunk001Sub001Block061Part008

theorem surrogateDiagonalTailChunk001Sub001Block061Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block061Part008CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block061Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block061Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block061Part008CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block061Part008SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block061Part008] using hcert

def TailChunk001Sub001Block061Part009SupportExplicit : Finset ℕ :=
  ([27247] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block061Part009 : ℚ :=
  (7692963679 : ℚ) / 9397869721048588800

def SurrogateDiagonalTailChunk001Sub001Block061Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27247
    = surrogateDiagTailX0RatChunk001Sub001Block061Part009

theorem surrogateDiagonalTailChunk001Sub001Block061Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block061Part009CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block061Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block061Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block061Part009CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block061Part009SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block061Part009] using hcert

def TailChunk001Sub001Block061Part010SupportExplicit : Finset ℕ :=
  ([27249] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block061Part010 : ℚ :=
  (684420817 : ℚ) / 785311598081433600

def SurrogateDiagonalTailChunk001Sub001Block061Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27249
    = surrogateDiagTailX0RatChunk001Sub001Block061Part010

theorem surrogateDiagonalTailChunk001Sub001Block061Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block061Part010CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block061Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block061Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block061Part010CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block061Part010SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block061Part010] using hcert

def TailChunk001Sub001Block061Part011SupportExplicit : Finset ℕ :=
  ([27251] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block061Part011 : ℚ :=
  (1384724922775 : ℚ) / 573919761749369683968

def SurrogateDiagonalTailChunk001Sub001Block061Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27251
    = surrogateDiagTailX0RatChunk001Sub001Block061Part011

theorem surrogateDiagonalTailChunk001Sub001Block061Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block061Part011CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block061Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block061Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block061Part011CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block061Part011SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block061Part011] using hcert

def TailChunk001Sub001Block061Part012SupportExplicit : Finset ℕ :=
  ([27253] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block061Part012 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block061Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27253
    = surrogateDiagTailX0RatChunk001Sub001Block061Part012

theorem surrogateDiagonalTailChunk001Sub001Block061Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block061Part012CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block061Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block061Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block061Part012CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block061Part012SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block061Part012] using hcert

def TailChunk001Sub001Block061Part013SupportExplicit : Finset ℕ :=
  ([27254] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block061Part013 : ℚ :=
  (2901486390625 : ℚ) / 21549659181491903922

def SurrogateDiagonalTailChunk001Sub001Block061Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27254
    = surrogateDiagTailX0RatChunk001Sub001Block061Part013

theorem surrogateDiagonalTailChunk001Sub001Block061Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block061Part013CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block061Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block061Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block061Part013CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block061Part013SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block061Part013] using hcert

def TailChunk001Sub001Block061Part014SupportExplicit : Finset ℕ :=
  ([27255] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block061Part014 : ℚ :=
  (1180411823425 : ℚ) / 88808787539227312128

def SurrogateDiagonalTailChunk001Sub001Block061Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27255
    = surrogateDiagTailX0RatChunk001Sub001Block061Part014

theorem surrogateDiagonalTailChunk001Sub001Block061Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block061Part014CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block061Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block061Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block061Part014CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block061Part014SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block061Part014] using hcert

def TailChunk001Sub001Block061Part015SupportExplicit : Finset ℕ :=
  ([27257] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block061Part015 : ℚ :=
  (4726345081 : ℚ) / 52216037037519667200

def SurrogateDiagonalTailChunk001Sub001Block061Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27257
    = surrogateDiagTailX0RatChunk001Sub001Block061Part015

theorem surrogateDiagonalTailChunk001Sub001Block061Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block061Part015CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block061Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block061Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block061Part015CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block061Part015SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block061Part015] using hcert

def TailChunk001Sub001Block061Part016SupportExplicit : Finset ℕ :=
  ([27258] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block061Part016 : ℚ :=
  (28137697043 : ℚ) / 46941158565642240

def SurrogateDiagonalTailChunk001Sub001Block061Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27258
    = surrogateDiagTailX0RatChunk001Sub001Block061Part016

theorem surrogateDiagonalTailChunk001Sub001Block061Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block061Part016CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block061Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block061Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block061Part016CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block061Part016SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block061Part016] using hcert

def TailChunk001Sub001Block061Part017SupportExplicit : Finset ℕ :=
  ([27259] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block061Part017 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block061Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27259
    = surrogateDiagTailX0RatChunk001Sub001Block061Part017

theorem surrogateDiagonalTailChunk001Sub001Block061Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block061Part017CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block061Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block061Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block061Part017CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block061Part017SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block061Part017] using hcert

def TailChunk001Sub001Block061Part018SupportExplicit : Finset ℕ :=
  ([27262] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block061Part018 : ℚ :=
  (205873077425 : ℚ) / 1436741350040005632

def SurrogateDiagonalTailChunk001Sub001Block061Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27262
    = surrogateDiagTailX0RatChunk001Sub001Block061Part018

theorem surrogateDiagonalTailChunk001Sub001Block061Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block061Part018CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block061Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block061Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block061Part018CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block061Part018SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block061Part018] using hcert

def TailChunk001Sub001Block061Part019SupportExplicit : Finset ℕ :=
  ([27263] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block061Part019 : ℚ :=
  (34679968925 : ℚ) / 438250074598496894976

def SurrogateDiagonalTailChunk001Sub001Block061Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27263
    = surrogateDiagTailX0RatChunk001Sub001Block061Part019

theorem surrogateDiagonalTailChunk001Sub001Block061Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block061Part019CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block061Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block061Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block061Part019CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block061Part019SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block061Part019] using hcert

def TailChunk001Sub001Block061Part020SupportExplicit : Finset ℕ :=
  ([27265] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block061Part020 : ℚ :=
  (22447375357 : ℚ) / 2229470917086412800

def SurrogateDiagonalTailChunk001Sub001Block061Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27265
    = surrogateDiagTailX0RatChunk001Sub001Block061Part020

theorem surrogateDiagonalTailChunk001Sub001Block061Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block061Part020CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block061Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block061Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block061Part020CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block061Part020SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block061Part020] using hcert

def TailChunk001Sub001Block061Part021SupportExplicit : Finset ℕ :=
  ([27266] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block061Part021 : ℚ :=
  (2904042015625 : ℚ) / 21587640505935593472

def SurrogateDiagonalTailChunk001Sub001Block061Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27266
    = surrogateDiagTailX0RatChunk001Sub001Block061Part021

theorem surrogateDiagonalTailChunk001Sub001Block061Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block061Part021CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block061Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block061Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block061Part021CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block061Part021SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block061Part021] using hcert

def TailChunk001Sub001Block061Part022SupportExplicit : Finset ℕ :=
  ([27267] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block061Part022 : ℚ :=
  (86022667 : ℚ) / 165846933403729920

def SurrogateDiagonalTailChunk001Sub001Block061Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27267
    = surrogateDiagTailX0RatChunk001Sub001Block061Part022

theorem surrogateDiagonalTailChunk001Sub001Block061Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block061Part022CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block061Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block061Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block061Part022CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block061Part022SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block061Part022] using hcert

def TailChunk001Sub001Block061Part023SupportExplicit : Finset ℕ :=
  ([27269] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block061Part023 : ℚ :=
  (6827393491 : ℚ) / 5312774039235379200

def SurrogateDiagonalTailChunk001Sub001Block061Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27269
    = surrogateDiagTailX0RatChunk001Sub001Block061Part023

theorem surrogateDiagonalTailChunk001Sub001Block061Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block061Part023CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block061Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block061Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block061Part023CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block061Part023SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block061Part023] using hcert

def TailChunk001Sub001Block061Part024SupportExplicit : Finset ℕ :=
  ([27271] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block061Part024 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block061Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27271
    = surrogateDiagTailX0RatChunk001Sub001Block061Part024

theorem surrogateDiagonalTailChunk001Sub001Block061Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block061Part024CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block061Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block061Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block061Part024CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block061Part024SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block061Part024] using hcert

def surrogateDiagonalTailChunk001Sub001Block061HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub001Block061Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block061Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block061Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block061Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block061Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block061Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block061Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block061Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block061Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block061Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub001Block061Head : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block061Part000
    + surrogateDiagTailX0RatChunk001Sub001Block061Part001
    + surrogateDiagTailX0RatChunk001Sub001Block061Part002
    + surrogateDiagTailX0RatChunk001Sub001Block061Part003
    + surrogateDiagTailX0RatChunk001Sub001Block061Part004
    + surrogateDiagTailX0RatChunk001Sub001Block061Part005
    + surrogateDiagTailX0RatChunk001Sub001Block061Part006
    + surrogateDiagTailX0RatChunk001Sub001Block061Part007
    + surrogateDiagTailX0RatChunk001Sub001Block061Part008
    + surrogateDiagTailX0RatChunk001Sub001Block061Part009

def surrogateDiagonalTailChunk001Sub001Block061MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub001Block061Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block061Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block061Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block061Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block061Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block061Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block061Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block061Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block061Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block061Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub001Block061Mid : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block061Part010
    + surrogateDiagTailX0RatChunk001Sub001Block061Part011
    + surrogateDiagTailX0RatChunk001Sub001Block061Part012
    + surrogateDiagTailX0RatChunk001Sub001Block061Part013
    + surrogateDiagTailX0RatChunk001Sub001Block061Part014
    + surrogateDiagTailX0RatChunk001Sub001Block061Part015
    + surrogateDiagTailX0RatChunk001Sub001Block061Part016
    + surrogateDiagTailX0RatChunk001Sub001Block061Part017
    + surrogateDiagTailX0RatChunk001Sub001Block061Part018
    + surrogateDiagTailX0RatChunk001Sub001Block061Part019

def surrogateDiagonalTailChunk001Sub001Block061TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub001Block061Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block061Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block061Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block061Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block061Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub001Block061Tail : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block061Part020
    + surrogateDiagTailX0RatChunk001Sub001Block061Part021
    + surrogateDiagTailX0RatChunk001Sub001Block061Part022
    + surrogateDiagTailX0RatChunk001Sub001Block061Part023
    + surrogateDiagTailX0RatChunk001Sub001Block061Part024

def surrogateDiagonalTailChunk001Sub001Block061Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk001Sub001Block061HeadSum X0
    + surrogateDiagonalTailChunk001Sub001Block061MidSum X0
    + surrogateDiagonalTailChunk001Sub001Block061TailSum X0

def surrogateDiagTailX0RatChunk001Sub001Block061 : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block061Part000
    + surrogateDiagTailX0RatChunk001Sub001Block061Part001
    + surrogateDiagTailX0RatChunk001Sub001Block061Part002
    + surrogateDiagTailX0RatChunk001Sub001Block061Part003
    + surrogateDiagTailX0RatChunk001Sub001Block061Part004
    + surrogateDiagTailX0RatChunk001Sub001Block061Part005
    + surrogateDiagTailX0RatChunk001Sub001Block061Part006
    + surrogateDiagTailX0RatChunk001Sub001Block061Part007
    + surrogateDiagTailX0RatChunk001Sub001Block061Part008
    + surrogateDiagTailX0RatChunk001Sub001Block061Part009
    + surrogateDiagTailX0RatChunk001Sub001Block061Part010
    + surrogateDiagTailX0RatChunk001Sub001Block061Part011
    + surrogateDiagTailX0RatChunk001Sub001Block061Part012
    + surrogateDiagTailX0RatChunk001Sub001Block061Part013
    + surrogateDiagTailX0RatChunk001Sub001Block061Part014
    + surrogateDiagTailX0RatChunk001Sub001Block061Part015
    + surrogateDiagTailX0RatChunk001Sub001Block061Part016
    + surrogateDiagTailX0RatChunk001Sub001Block061Part017
    + surrogateDiagTailX0RatChunk001Sub001Block061Part018
    + surrogateDiagTailX0RatChunk001Sub001Block061Part019
    + surrogateDiagTailX0RatChunk001Sub001Block061Part020
    + surrogateDiagTailX0RatChunk001Sub001Block061Part021
    + surrogateDiagTailX0RatChunk001Sub001Block061Part022
    + surrogateDiagTailX0RatChunk001Sub001Block061Part023
    + surrogateDiagTailX0RatChunk001Sub001Block061Part024

theorem surrogateDiagTailX0RatChunk001Sub001Block061_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk001Sub001Block061Head + surrogateDiagTailX0RatChunk001Sub001Block061Mid + surrogateDiagTailX0RatChunk001Sub001Block061Tail =
      surrogateDiagTailX0RatChunk001Sub001Block061 := by
  unfold surrogateDiagTailX0RatChunk001Sub001Block061Head surrogateDiagTailX0RatChunk001Sub001Block061Mid surrogateDiagTailX0RatChunk001Sub001Block061Tail surrogateDiagTailX0RatChunk001Sub001Block061
  ring

def SurrogateDiagonalTailChunk001Sub001Block061HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub001Block061HeadSum X0 = surrogateDiagTailX0RatChunk001Sub001Block061Head

def SurrogateDiagonalTailChunk001Sub001Block061MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub001Block061MidSum X0 = surrogateDiagTailX0RatChunk001Sub001Block061Mid

def SurrogateDiagonalTailChunk001Sub001Block061TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub001Block061TailSum X0 = surrogateDiagTailX0RatChunk001Sub001Block061Tail

theorem surrogateDiagonalTailChunk001Sub001Block061_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk001Sub001Block061HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk001Sub001Block061MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk001Sub001Block061TailCertificateAt X0) :
    surrogateDiagonalTailChunk001Sub001Block061Sum X0 = surrogateDiagTailX0RatChunk001Sub001Block061 := by
  unfold SurrogateDiagonalTailChunk001Sub001Block061HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk001Sub001Block061MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk001Sub001Block061TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk001Sub001Block061Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk001Sub001Block061_eq_head_add_mid_add_tail

/-- Block 062 covers tail-support indices [16550,16575) and q from 27273 to 27311. -/

def TailChunk001Sub001Block062Part000SupportExplicit : Finset ℕ :=
  ([27273] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block062Part000 : ℚ :=
  (20659524841 : ℚ) / 1092602942430707520

def SurrogateDiagonalTailChunk001Sub001Block062Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27273
    = surrogateDiagTailX0RatChunk001Sub001Block062Part000

theorem surrogateDiagonalTailChunk001Sub001Block062Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block062Part000CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block062Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block062Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block062Part000CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block062Part000SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block062Part000] using hcert

def TailChunk001Sub001Block062Part001SupportExplicit : Finset ℕ :=
  ([27274] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block062Part001 : ℚ :=
  (1694034896575 : ℚ) / 10424271721691086848

def SurrogateDiagonalTailChunk001Sub001Block062Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27274
    = surrogateDiagTailX0RatChunk001Sub001Block062Part001

theorem surrogateDiagonalTailChunk001Sub001Block062Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block062Part001CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block062Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block062Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block062Part001CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block062Part001SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block062Part001] using hcert

def TailChunk001Sub001Block062Part002SupportExplicit : Finset ℕ :=
  ([27277] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block062Part002 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block062Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27277
    = surrogateDiagTailX0RatChunk001Sub001Block062Part002

theorem surrogateDiagonalTailChunk001Sub001Block062Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block062Part002CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block062Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block062Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block062Part002CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block062Part002SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block062Part002] using hcert

def TailChunk001Sub001Block062Part003SupportExplicit : Finset ℕ :=
  ([27278] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block062Part003 : ℚ :=
  (21021206375 : ℚ) / 140518805090509824

def SurrogateDiagonalTailChunk001Sub001Block062Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27278
    = surrogateDiagTailX0RatChunk001Sub001Block062Part003

theorem surrogateDiagonalTailChunk001Sub001Block062Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block062Part003CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block062Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block062Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block062Part003CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block062Part003SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block062Part003] using hcert

def TailChunk001Sub001Block062Part004SupportExplicit : Finset ℕ :=
  ([27281] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block062Part004 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block062Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27281
    = surrogateDiagTailX0RatChunk001Sub001Block062Part004

theorem surrogateDiagonalTailChunk001Sub001Block062Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block062Part004CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block062Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block062Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block062Part004CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block062Part004SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block062Part004] using hcert

def TailChunk001Sub001Block062Part005SupportExplicit : Finset ℕ :=
  ([27282] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block062Part005 : ℚ :=
  (403738711225 : ℚ) / 1067934420488902728

def SurrogateDiagonalTailChunk001Sub001Block062Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27282
    = surrogateDiagTailX0RatChunk001Sub001Block062Part005

theorem surrogateDiagonalTailChunk001Sub001Block062Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block062Part005CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block062Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block062Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block062Part005CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block062Part005SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block062Part005] using hcert

def TailChunk001Sub001Block062Part006SupportExplicit : Finset ℕ :=
  ([27283] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block062Part006 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block062Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27283
    = surrogateDiagTailX0RatChunk001Sub001Block062Part006

theorem surrogateDiagonalTailChunk001Sub001Block062Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block062Part006CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block062Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block062Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block062Part006CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block062Part006SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block062Part006] using hcert

def TailChunk001Sub001Block062Part007SupportExplicit : Finset ℕ :=
  ([27285] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block062Part007 : ℚ :=
  (2028306208925 : ℚ) / 42370169645347897344

def SurrogateDiagonalTailChunk001Sub001Block062Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27285
    = surrogateDiagTailX0RatChunk001Sub001Block062Part007

theorem surrogateDiagonalTailChunk001Sub001Block062Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block062Part007CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block062Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block062Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block062Part007CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block062Part007SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block062Part007] using hcert

def TailChunk001Sub001Block062Part008SupportExplicit : Finset ℕ :=
  ([27286] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block062Part008 : ℚ :=
  (2253834154075 : ℚ) / 11666153306677473792

def SurrogateDiagonalTailChunk001Sub001Block062Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27286
    = surrogateDiagTailX0RatChunk001Sub001Block062Part008

theorem surrogateDiagonalTailChunk001Sub001Block062Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block062Part008CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block062Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block062Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block062Part008CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block062Part008SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block062Part008] using hcert

def TailChunk001Sub001Block062Part009SupportExplicit : Finset ℕ :=
  ([27287] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block062Part009 : ℚ :=
  (553843955725 : ℚ) / 1004555136195849996288

def SurrogateDiagonalTailChunk001Sub001Block062Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27287
    = surrogateDiagTailX0RatChunk001Sub001Block062Part009

theorem surrogateDiagonalTailChunk001Sub001Block062Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block062Part009CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block062Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block062Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block062Part009CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block062Part009SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block062Part009] using hcert

def TailChunk001Sub001Block062Part010SupportExplicit : Finset ℕ :=
  ([27289] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block062Part010 : ℚ :=
  (948787617 : ℚ) / 3999900093035929600

def SurrogateDiagonalTailChunk001Sub001Block062Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27289
    = surrogateDiagTailX0RatChunk001Sub001Block062Part010

theorem surrogateDiagonalTailChunk001Sub001Block062Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block062Part010CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block062Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block062Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block062Part010CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block062Part010SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block062Part010] using hcert

def TailChunk001Sub001Block062Part011SupportExplicit : Finset ℕ :=
  ([27290] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block062Part011 : ℚ :=
  (7909102590475 : ℚ) / 35452289588113440768

def SurrogateDiagonalTailChunk001Sub001Block062Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27290
    = surrogateDiagTailX0RatChunk001Sub001Block062Part011

theorem surrogateDiagonalTailChunk001Sub001Block062Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block062Part011CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block062Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block062Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block062Part011CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block062Part011SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block062Part011] using hcert

def TailChunk001Sub001Block062Part012SupportExplicit : Finset ℕ :=
  ([27291] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block062Part012 : ℚ :=
  (535531719 : ℚ) / 21043780351820800

def SurrogateDiagonalTailChunk001Sub001Block062Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27291
    = surrogateDiagTailX0RatChunk001Sub001Block062Part012

theorem surrogateDiagonalTailChunk001Sub001Block062Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block062Part012CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block062Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block062Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block062Part012CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block062Part012SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block062Part012] using hcert

def TailChunk001Sub001Block062Part013SupportExplicit : Finset ℕ :=
  ([27294] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block062Part013 : ℚ :=
  (3232752019475 : ℚ) / 8558520001016177664

def SurrogateDiagonalTailChunk001Sub001Block062Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27294
    = surrogateDiagTailX0RatChunk001Sub001Block062Part013

theorem surrogateDiagonalTailChunk001Sub001Block062Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block062Part013CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block062Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block062Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block062Part013CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block062Part013SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block062Part013] using hcert

def TailChunk001Sub001Block062Part014SupportExplicit : Finset ℕ :=
  ([27295] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block062Part014 : ℚ :=
  (216847881025 : ℚ) / 56290923844483940352

def SurrogateDiagonalTailChunk001Sub001Block062Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27295
    = surrogateDiagTailX0RatChunk001Sub001Block062Part014

theorem surrogateDiagonalTailChunk001Sub001Block062Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block062Part014CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block062Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block062Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block062Part014CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block062Part014SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block062Part014] using hcert

def TailChunk001Sub001Block062Part015SupportExplicit : Finset ℕ :=
  ([27298] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block062Part015 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block062Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27298
    = surrogateDiagTailX0RatChunk001Sub001Block062Part015

theorem surrogateDiagonalTailChunk001Sub001Block062Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block062Part015CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block062Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block062Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block062Part015CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block062Part015SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block062Part015] using hcert

def TailChunk001Sub001Block062Part016SupportExplicit : Finset ℕ :=
  ([27299] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block062Part016 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block062Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27299
    = surrogateDiagTailX0RatChunk001Sub001Block062Part016

theorem surrogateDiagonalTailChunk001Sub001Block062Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block062Part016CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block062Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block062Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block062Part016CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block062Part016SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block062Part016] using hcert

def TailChunk001Sub001Block062Part017SupportExplicit : Finset ℕ :=
  ([27301] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block062Part017 : ℚ :=
  (179151547175 : ℚ) / 579463843393748917824

def SurrogateDiagonalTailChunk001Sub001Block062Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27301
    = surrogateDiagTailX0RatChunk001Sub001Block062Part017

theorem surrogateDiagonalTailChunk001Sub001Block062Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block062Part017CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block062Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block062Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block062Part017CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block062Part017SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block062Part017] using hcert

def TailChunk001Sub001Block062Part018SupportExplicit : Finset ℕ :=
  ([27302] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block062Part018 : ℚ :=
  (11902010303 : ℚ) / 880778633910681600

def SurrogateDiagonalTailChunk001Sub001Block062Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27302
    = surrogateDiagTailX0RatChunk001Sub001Block062Part018

theorem surrogateDiagonalTailChunk001Sub001Block062Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block062Part018CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block062Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block062Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block062Part018CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block062Part018SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block062Part018] using hcert

def TailChunk001Sub001Block062Part019SupportExplicit : Finset ℕ :=
  ([27303] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block062Part019 : ℚ :=
  (2476023747125 : ℚ) / 109627233029630567424

def SurrogateDiagonalTailChunk001Sub001Block062Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27303
    = surrogateDiagTailX0RatChunk001Sub001Block062Part019

theorem surrogateDiagonalTailChunk001Sub001Block062Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block062Part019CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block062Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block062Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block062Part019CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block062Part019SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block062Part019] using hcert

def TailChunk001Sub001Block062Part020SupportExplicit : Finset ℕ :=
  ([27305] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block062Part020 : ℚ :=
  (979577989175 : ℚ) / 251024534615052140544

def SurrogateDiagonalTailChunk001Sub001Block062Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27305
    = surrogateDiagTailX0RatChunk001Sub001Block062Part020

theorem surrogateDiagonalTailChunk001Sub001Block062Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block062Part020CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block062Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block062Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block062Part020CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block062Part020SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block062Part020] using hcert

def TailChunk001Sub001Block062Part021SupportExplicit : Finset ℕ :=
  ([27307] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block062Part021 : ℚ :=
  (27599199875 : ℚ) / 16000543688399751168

def SurrogateDiagonalTailChunk001Sub001Block062Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27307
    = surrogateDiagTailX0RatChunk001Sub001Block062Part021

theorem surrogateDiagonalTailChunk001Sub001Block062Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block062Part021CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block062Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block062Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block062Part021CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block062Part021SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block062Part021] using hcert

def TailChunk001Sub001Block062Part022SupportExplicit : Finset ℕ :=
  ([27309] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block062Part022 : ℚ :=
  (2589262604975 : ℚ) / 137297987221247244864

def SurrogateDiagonalTailChunk001Sub001Block062Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27309
    = surrogateDiagTailX0RatChunk001Sub001Block062Part022

theorem surrogateDiagonalTailChunk001Sub001Block062Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block062Part022CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block062Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block062Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block062Part022CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block062Part022SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block062Part022] using hcert

def TailChunk001Sub001Block062Part023SupportExplicit : Finset ℕ :=
  ([27310] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block062Part023 : ℚ :=
  (3736456769 : ℚ) / 284450957074851840

def SurrogateDiagonalTailChunk001Sub001Block062Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27310
    = surrogateDiagTailX0RatChunk001Sub001Block062Part023

theorem surrogateDiagonalTailChunk001Sub001Block062Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block062Part023CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block062Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block062Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block062Part023CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block062Part023SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block062Part023] using hcert

def TailChunk001Sub001Block062Part024SupportExplicit : Finset ℕ :=
  ([27311] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block062Part024 : ℚ :=
  (11978814979 : ℚ) / 48585039224832000000

def SurrogateDiagonalTailChunk001Sub001Block062Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27311
    = surrogateDiagTailX0RatChunk001Sub001Block062Part024

theorem surrogateDiagonalTailChunk001Sub001Block062Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block062Part024CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block062Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block062Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block062Part024CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block062Part024SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block062Part024] using hcert

def surrogateDiagonalTailChunk001Sub001Block062HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub001Block062Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block062Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block062Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block062Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block062Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block062Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block062Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block062Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block062Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block062Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub001Block062Head : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block062Part000
    + surrogateDiagTailX0RatChunk001Sub001Block062Part001
    + surrogateDiagTailX0RatChunk001Sub001Block062Part002
    + surrogateDiagTailX0RatChunk001Sub001Block062Part003
    + surrogateDiagTailX0RatChunk001Sub001Block062Part004
    + surrogateDiagTailX0RatChunk001Sub001Block062Part005
    + surrogateDiagTailX0RatChunk001Sub001Block062Part006
    + surrogateDiagTailX0RatChunk001Sub001Block062Part007
    + surrogateDiagTailX0RatChunk001Sub001Block062Part008
    + surrogateDiagTailX0RatChunk001Sub001Block062Part009

def surrogateDiagonalTailChunk001Sub001Block062MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub001Block062Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block062Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block062Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block062Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block062Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block062Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block062Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block062Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block062Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block062Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub001Block062Mid : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block062Part010
    + surrogateDiagTailX0RatChunk001Sub001Block062Part011
    + surrogateDiagTailX0RatChunk001Sub001Block062Part012
    + surrogateDiagTailX0RatChunk001Sub001Block062Part013
    + surrogateDiagTailX0RatChunk001Sub001Block062Part014
    + surrogateDiagTailX0RatChunk001Sub001Block062Part015
    + surrogateDiagTailX0RatChunk001Sub001Block062Part016
    + surrogateDiagTailX0RatChunk001Sub001Block062Part017
    + surrogateDiagTailX0RatChunk001Sub001Block062Part018
    + surrogateDiagTailX0RatChunk001Sub001Block062Part019

def surrogateDiagonalTailChunk001Sub001Block062TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub001Block062Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block062Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block062Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block062Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block062Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub001Block062Tail : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block062Part020
    + surrogateDiagTailX0RatChunk001Sub001Block062Part021
    + surrogateDiagTailX0RatChunk001Sub001Block062Part022
    + surrogateDiagTailX0RatChunk001Sub001Block062Part023
    + surrogateDiagTailX0RatChunk001Sub001Block062Part024

def surrogateDiagonalTailChunk001Sub001Block062Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk001Sub001Block062HeadSum X0
    + surrogateDiagonalTailChunk001Sub001Block062MidSum X0
    + surrogateDiagonalTailChunk001Sub001Block062TailSum X0

def surrogateDiagTailX0RatChunk001Sub001Block062 : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block062Part000
    + surrogateDiagTailX0RatChunk001Sub001Block062Part001
    + surrogateDiagTailX0RatChunk001Sub001Block062Part002
    + surrogateDiagTailX0RatChunk001Sub001Block062Part003
    + surrogateDiagTailX0RatChunk001Sub001Block062Part004
    + surrogateDiagTailX0RatChunk001Sub001Block062Part005
    + surrogateDiagTailX0RatChunk001Sub001Block062Part006
    + surrogateDiagTailX0RatChunk001Sub001Block062Part007
    + surrogateDiagTailX0RatChunk001Sub001Block062Part008
    + surrogateDiagTailX0RatChunk001Sub001Block062Part009
    + surrogateDiagTailX0RatChunk001Sub001Block062Part010
    + surrogateDiagTailX0RatChunk001Sub001Block062Part011
    + surrogateDiagTailX0RatChunk001Sub001Block062Part012
    + surrogateDiagTailX0RatChunk001Sub001Block062Part013
    + surrogateDiagTailX0RatChunk001Sub001Block062Part014
    + surrogateDiagTailX0RatChunk001Sub001Block062Part015
    + surrogateDiagTailX0RatChunk001Sub001Block062Part016
    + surrogateDiagTailX0RatChunk001Sub001Block062Part017
    + surrogateDiagTailX0RatChunk001Sub001Block062Part018
    + surrogateDiagTailX0RatChunk001Sub001Block062Part019
    + surrogateDiagTailX0RatChunk001Sub001Block062Part020
    + surrogateDiagTailX0RatChunk001Sub001Block062Part021
    + surrogateDiagTailX0RatChunk001Sub001Block062Part022
    + surrogateDiagTailX0RatChunk001Sub001Block062Part023
    + surrogateDiagTailX0RatChunk001Sub001Block062Part024

theorem surrogateDiagTailX0RatChunk001Sub001Block062_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk001Sub001Block062Head + surrogateDiagTailX0RatChunk001Sub001Block062Mid + surrogateDiagTailX0RatChunk001Sub001Block062Tail =
      surrogateDiagTailX0RatChunk001Sub001Block062 := by
  unfold surrogateDiagTailX0RatChunk001Sub001Block062Head surrogateDiagTailX0RatChunk001Sub001Block062Mid surrogateDiagTailX0RatChunk001Sub001Block062Tail surrogateDiagTailX0RatChunk001Sub001Block062
  ring

def SurrogateDiagonalTailChunk001Sub001Block062HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub001Block062HeadSum X0 = surrogateDiagTailX0RatChunk001Sub001Block062Head

def SurrogateDiagonalTailChunk001Sub001Block062MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub001Block062MidSum X0 = surrogateDiagTailX0RatChunk001Sub001Block062Mid

def SurrogateDiagonalTailChunk001Sub001Block062TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub001Block062TailSum X0 = surrogateDiagTailX0RatChunk001Sub001Block062Tail

theorem surrogateDiagonalTailChunk001Sub001Block062_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk001Sub001Block062HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk001Sub001Block062MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk001Sub001Block062TailCertificateAt X0) :
    surrogateDiagonalTailChunk001Sub001Block062Sum X0 = surrogateDiagTailX0RatChunk001Sub001Block062 := by
  unfold SurrogateDiagonalTailChunk001Sub001Block062HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk001Sub001Block062MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk001Sub001Block062TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk001Sub001Block062Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk001Sub001Block062_eq_head_add_mid_add_tail

/-- Block 063 covers tail-support indices [16575,16600) and q from 27313 to 27354. -/

def TailChunk001Sub001Block063Part000SupportExplicit : Finset ℕ :=
  ([27313] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block063Part000 : ℚ :=
  (56453671243 : ℚ) / 27028767232512000000

def SurrogateDiagonalTailChunk001Sub001Block063Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27313
    = surrogateDiagTailX0RatChunk001Sub001Block063Part000

theorem surrogateDiagonalTailChunk001Sub001Block063Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block063Part000CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block063Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block063Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block063Part000CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block063Part000SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block063Part000] using hcert

def TailChunk001Sub001Block063Part001SupportExplicit : Finset ℕ :=
  ([27314] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block063Part001 : ℚ :=
  (9541844447 : ℚ) / 937130993721000000

def SurrogateDiagonalTailChunk001Sub001Block063Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27314
    = surrogateDiagTailX0RatChunk001Sub001Block063Part001

theorem surrogateDiagonalTailChunk001Sub001Block063Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block063Part001CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block063Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block063Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block063Part001CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block063Part001SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block063Part001] using hcert

def TailChunk001Sub001Block063Part002SupportExplicit : Finset ℕ :=
  ([27317] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block063Part002 : ℚ :=
  (41156882125 : ℚ) / 322289935868266182432

def SurrogateDiagonalTailChunk001Sub001Block063Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27317
    = surrogateDiagTailX0RatChunk001Sub001Block063Part002

theorem surrogateDiagonalTailChunk001Sub001Block063Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block063Part002CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block063Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block063Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block063Part002CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block063Part002SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block063Part002] using hcert

def TailChunk001Sub001Block063Part003SupportExplicit : Finset ℕ :=
  ([27318] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block063Part003 : ℚ :=
  (1307153223625 : ℚ) / 14563889002232414208

def SurrogateDiagonalTailChunk001Sub001Block063Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27318
    = surrogateDiagTailX0RatChunk001Sub001Block063Part003

theorem surrogateDiagonalTailChunk001Sub001Block063Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block063Part003CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block063Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block063Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block063Part003CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block063Part003SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block063Part003] using hcert

def TailChunk001Sub001Block063Part004SupportExplicit : Finset ℕ :=
  ([27319] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block063Part004 : ℚ :=
  (40701025575 : ℚ) / 90846396898846572544

def SurrogateDiagonalTailChunk001Sub001Block063Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27319
    = surrogateDiagTailX0RatChunk001Sub001Block063Part004

theorem surrogateDiagonalTailChunk001Sub001Block063Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block063Part004CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block063Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block063Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block063Part004CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block063Part004SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block063Part004] using hcert

def TailChunk001Sub001Block063Part005SupportExplicit : Finset ℕ :=
  ([27321] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block063Part005 : ℚ :=
  (411122461 : ℚ) / 13712021856000000

def SurrogateDiagonalTailChunk001Sub001Block063Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27321
    = surrogateDiagTailX0RatChunk001Sub001Block063Part005

theorem surrogateDiagonalTailChunk001Sub001Block063Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block063Part005CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block063Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block063Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block063Part005CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block063Part005SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block063Part005] using hcert

def TailChunk001Sub001Block063Part006SupportExplicit : Finset ℕ :=
  ([27322] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block063Part006 : ℚ :=
  (230893284625 : ℚ) / 69761314649560745088

def SurrogateDiagonalTailChunk001Sub001Block063Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27322
    = surrogateDiagTailX0RatChunk001Sub001Block063Part006

theorem surrogateDiagonalTailChunk001Sub001Block063Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block063Part006CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block063Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block063Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block063Part006CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block063Part006SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block063Part006] using hcert

def TailChunk001Sub001Block063Part007SupportExplicit : Finset ℕ :=
  ([27323] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block063Part007 : ℚ :=
  (1894465675 : ℚ) / 20542972246804541952

def SurrogateDiagonalTailChunk001Sub001Block063Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27323
    = surrogateDiagTailX0RatChunk001Sub001Block063Part007

theorem surrogateDiagonalTailChunk001Sub001Block063Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block063Part007CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block063Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block063Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block063Part007CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block063Part007SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block063Part007] using hcert

def TailChunk001Sub001Block063Part008SupportExplicit : Finset ℕ :=
  ([27326] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block063Part008 : ℚ :=
  (309340783 : ℚ) / 56021730105600000

def SurrogateDiagonalTailChunk001Sub001Block063Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27326
    = surrogateDiagTailX0RatChunk001Sub001Block063Part008

theorem surrogateDiagonalTailChunk001Sub001Block063Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block063Part008CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block063Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block063Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block063Part008CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block063Part008SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block063Part008] using hcert

def TailChunk001Sub001Block063Part009SupportExplicit : Finset ℕ :=
  ([27327] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block063Part009 : ℚ :=
  (648169244975 : ℚ) / 34415092590594160896

def SurrogateDiagonalTailChunk001Sub001Block063Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27327
    = surrogateDiagTailX0RatChunk001Sub001Block063Part009

theorem surrogateDiagonalTailChunk001Sub001Block063Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block063Part009CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block063Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block063Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block063Part009CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block063Part009SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block063Part009] using hcert

def TailChunk001Sub001Block063Part010SupportExplicit : Finset ℕ :=
  ([27329] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block063Part010 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block063Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27329
    = surrogateDiagTailX0RatChunk001Sub001Block063Part010

theorem surrogateDiagonalTailChunk001Sub001Block063Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block063Part010CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block063Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block063Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block063Part010CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block063Part010SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block063Part010] using hcert

def TailChunk001Sub001Block063Part011SupportExplicit : Finset ℕ :=
  ([27330] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block063Part011 : ℚ :=
  (746634111 : ℚ) / 3745856224854016

def SurrogateDiagonalTailChunk001Sub001Block063Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27330
    = surrogateDiagTailX0RatChunk001Sub001Block063Part011

theorem surrogateDiagonalTailChunk001Sub001Block063Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block063Part011CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block063Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block063Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block063Part011CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block063Part011SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block063Part011] using hcert

def TailChunk001Sub001Block063Part012SupportExplicit : Finset ℕ :=
  ([27331] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block063Part012 : ℚ :=
  (412467607 : ℚ) / 5315472882000000000

def SurrogateDiagonalTailChunk001Sub001Block063Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27331
    = surrogateDiagTailX0RatChunk001Sub001Block063Part012

theorem surrogateDiagonalTailChunk001Sub001Block063Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block063Part012CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block063Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block063Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block063Part012CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block063Part012SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block063Part012] using hcert

def TailChunk001Sub001Block063Part013SupportExplicit : Finset ℕ :=
  ([27334] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block063Part013 : ℚ :=
  (303076225 : ℚ) / 316431049724873928

def SurrogateDiagonalTailChunk001Sub001Block063Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27334
    = surrogateDiagTailX0RatChunk001Sub001Block063Part013

theorem surrogateDiagonalTailChunk001Sub001Block063Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block063Part013CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block063Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block063Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block063Part013CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block063Part013SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block063Part013] using hcert

def TailChunk001Sub001Block063Part014SupportExplicit : Finset ℕ :=
  ([27335] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block063Part014 : ℚ :=
  (317660323 : ℚ) / 27665051904000000

def SurrogateDiagonalTailChunk001Sub001Block063Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27335
    = surrogateDiagTailX0RatChunk001Sub001Block063Part014

theorem surrogateDiagonalTailChunk001Sub001Block063Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block063Part014CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block063Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block063Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block063Part014CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block063Part014SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block063Part014] using hcert

def TailChunk001Sub001Block063Part015SupportExplicit : Finset ℕ :=
  ([27337] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block063Part015 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block063Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27337
    = surrogateDiagTailX0RatChunk001Sub001Block063Part015

theorem surrogateDiagonalTailChunk001Sub001Block063Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block063Part015CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block063Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block063Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block063Part015CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block063Part015SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block063Part015] using hcert

def TailChunk001Sub001Block063Part016SupportExplicit : Finset ℕ :=
  ([27338] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block063Part016 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block063Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27338
    = surrogateDiagTailX0RatChunk001Sub001Block063Part016

theorem surrogateDiagonalTailChunk001Sub001Block063Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block063Part016CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block063Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block063Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block063Part016CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block063Part016SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block063Part016] using hcert

def TailChunk001Sub001Block063Part017SupportExplicit : Finset ℕ :=
  ([27339] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block063Part017 : ℚ :=
  (195058393903 : ℚ) / 7967534948352000000

def SurrogateDiagonalTailChunk001Sub001Block063Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27339
    = surrogateDiagTailX0RatChunk001Sub001Block063Part017

theorem surrogateDiagonalTailChunk001Sub001Block063Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block063Part017CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block063Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block063Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block063Part017CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block063Part017SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block063Part017] using hcert

def TailChunk001Sub001Block063Part018SupportExplicit : Finset ℕ :=
  ([27341] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block063Part018 : ℚ :=
  (393188581375 : ℚ) / 1122412316035391779968

def SurrogateDiagonalTailChunk001Sub001Block063Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27341
    = surrogateDiagTailX0RatChunk001Sub001Block063Part018

theorem surrogateDiagonalTailChunk001Sub001Block063Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block063Part018CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block063Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block063Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block063Part018CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block063Part018SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block063Part018] using hcert

def TailChunk001Sub001Block063Part019SupportExplicit : Finset ℕ :=
  ([27343] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block063Part019 : ℚ :=
  (249236617975 : ℚ) / 1245840110886471026688

def SurrogateDiagonalTailChunk001Sub001Block063Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27343
    = surrogateDiagTailX0RatChunk001Sub001Block063Part019

theorem surrogateDiagonalTailChunk001Sub001Block063Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block063Part019CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block063Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block063Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block063Part019CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block063Part019SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block063Part019] using hcert

def TailChunk001Sub001Block063Part020SupportExplicit : Finset ℕ :=
  ([27345] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block063Part020 : ℚ :=
  (363284976375 : ℚ) / 9405871718594535424

def SurrogateDiagonalTailChunk001Sub001Block063Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27345
    = surrogateDiagTailX0RatChunk001Sub001Block063Part020

theorem surrogateDiagonalTailChunk001Sub001Block063Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block063Part020CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block063Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block063Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block063Part020CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block063Part020SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block063Part020] using hcert

def TailChunk001Sub001Block063Part021SupportExplicit : Finset ℕ :=
  ([27347] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block063Part021 : ℚ :=
  (1468159281 : ℚ) / 1755619392697139200

def SurrogateDiagonalTailChunk001Sub001Block063Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27347
    = surrogateDiagTailX0RatChunk001Sub001Block063Part021

theorem surrogateDiagonalTailChunk001Sub001Block063Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block063Part021CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block063Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block063Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block063Part021CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block063Part021SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block063Part021] using hcert

def TailChunk001Sub001Block063Part022SupportExplicit : Finset ℕ :=
  ([27349] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block063Part022 : ℚ :=
  (954298980875 : ℚ) / 377164510282544330304

def SurrogateDiagonalTailChunk001Sub001Block063Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27349
    = surrogateDiagTailX0RatChunk001Sub001Block063Part022

theorem surrogateDiagonalTailChunk001Sub001Block063Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block063Part022CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block063Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block063Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block063Part022CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block063Part022SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block063Part022] using hcert

def TailChunk001Sub001Block063Part023SupportExplicit : Finset ℕ :=
  ([27353] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block063Part023 : ℚ :=
  (3400118575 : ℚ) / 7608314826024026112

def SurrogateDiagonalTailChunk001Sub001Block063Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27353
    = surrogateDiagTailX0RatChunk001Sub001Block063Part023

theorem surrogateDiagonalTailChunk001Sub001Block063Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block063Part023CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block063Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block063Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block063Part023CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block063Part023SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block063Part023] using hcert

def TailChunk001Sub001Block063Part024SupportExplicit : Finset ℕ :=
  ([27354] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block063Part024 : ℚ :=
  (326490899725 : ℚ) / 3803672433521590272

def SurrogateDiagonalTailChunk001Sub001Block063Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27354
    = surrogateDiagTailX0RatChunk001Sub001Block063Part024

theorem surrogateDiagonalTailChunk001Sub001Block063Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block063Part024CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block063Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block063Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block063Part024CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block063Part024SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block063Part024] using hcert

def surrogateDiagonalTailChunk001Sub001Block063HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub001Block063Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block063Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block063Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block063Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block063Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block063Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block063Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block063Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block063Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block063Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub001Block063Head : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block063Part000
    + surrogateDiagTailX0RatChunk001Sub001Block063Part001
    + surrogateDiagTailX0RatChunk001Sub001Block063Part002
    + surrogateDiagTailX0RatChunk001Sub001Block063Part003
    + surrogateDiagTailX0RatChunk001Sub001Block063Part004
    + surrogateDiagTailX0RatChunk001Sub001Block063Part005
    + surrogateDiagTailX0RatChunk001Sub001Block063Part006
    + surrogateDiagTailX0RatChunk001Sub001Block063Part007
    + surrogateDiagTailX0RatChunk001Sub001Block063Part008
    + surrogateDiagTailX0RatChunk001Sub001Block063Part009

def surrogateDiagonalTailChunk001Sub001Block063MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub001Block063Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block063Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block063Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block063Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block063Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block063Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block063Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block063Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block063Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block063Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub001Block063Mid : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block063Part010
    + surrogateDiagTailX0RatChunk001Sub001Block063Part011
    + surrogateDiagTailX0RatChunk001Sub001Block063Part012
    + surrogateDiagTailX0RatChunk001Sub001Block063Part013
    + surrogateDiagTailX0RatChunk001Sub001Block063Part014
    + surrogateDiagTailX0RatChunk001Sub001Block063Part015
    + surrogateDiagTailX0RatChunk001Sub001Block063Part016
    + surrogateDiagTailX0RatChunk001Sub001Block063Part017
    + surrogateDiagTailX0RatChunk001Sub001Block063Part018
    + surrogateDiagTailX0RatChunk001Sub001Block063Part019

def surrogateDiagonalTailChunk001Sub001Block063TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub001Block063Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block063Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block063Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block063Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block063Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub001Block063Tail : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block063Part020
    + surrogateDiagTailX0RatChunk001Sub001Block063Part021
    + surrogateDiagTailX0RatChunk001Sub001Block063Part022
    + surrogateDiagTailX0RatChunk001Sub001Block063Part023
    + surrogateDiagTailX0RatChunk001Sub001Block063Part024

def surrogateDiagonalTailChunk001Sub001Block063Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk001Sub001Block063HeadSum X0
    + surrogateDiagonalTailChunk001Sub001Block063MidSum X0
    + surrogateDiagonalTailChunk001Sub001Block063TailSum X0

def surrogateDiagTailX0RatChunk001Sub001Block063 : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block063Part000
    + surrogateDiagTailX0RatChunk001Sub001Block063Part001
    + surrogateDiagTailX0RatChunk001Sub001Block063Part002
    + surrogateDiagTailX0RatChunk001Sub001Block063Part003
    + surrogateDiagTailX0RatChunk001Sub001Block063Part004
    + surrogateDiagTailX0RatChunk001Sub001Block063Part005
    + surrogateDiagTailX0RatChunk001Sub001Block063Part006
    + surrogateDiagTailX0RatChunk001Sub001Block063Part007
    + surrogateDiagTailX0RatChunk001Sub001Block063Part008
    + surrogateDiagTailX0RatChunk001Sub001Block063Part009
    + surrogateDiagTailX0RatChunk001Sub001Block063Part010
    + surrogateDiagTailX0RatChunk001Sub001Block063Part011
    + surrogateDiagTailX0RatChunk001Sub001Block063Part012
    + surrogateDiagTailX0RatChunk001Sub001Block063Part013
    + surrogateDiagTailX0RatChunk001Sub001Block063Part014
    + surrogateDiagTailX0RatChunk001Sub001Block063Part015
    + surrogateDiagTailX0RatChunk001Sub001Block063Part016
    + surrogateDiagTailX0RatChunk001Sub001Block063Part017
    + surrogateDiagTailX0RatChunk001Sub001Block063Part018
    + surrogateDiagTailX0RatChunk001Sub001Block063Part019
    + surrogateDiagTailX0RatChunk001Sub001Block063Part020
    + surrogateDiagTailX0RatChunk001Sub001Block063Part021
    + surrogateDiagTailX0RatChunk001Sub001Block063Part022
    + surrogateDiagTailX0RatChunk001Sub001Block063Part023
    + surrogateDiagTailX0RatChunk001Sub001Block063Part024

theorem surrogateDiagTailX0RatChunk001Sub001Block063_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk001Sub001Block063Head + surrogateDiagTailX0RatChunk001Sub001Block063Mid + surrogateDiagTailX0RatChunk001Sub001Block063Tail =
      surrogateDiagTailX0RatChunk001Sub001Block063 := by
  unfold surrogateDiagTailX0RatChunk001Sub001Block063Head surrogateDiagTailX0RatChunk001Sub001Block063Mid surrogateDiagTailX0RatChunk001Sub001Block063Tail surrogateDiagTailX0RatChunk001Sub001Block063
  ring

def SurrogateDiagonalTailChunk001Sub001Block063HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub001Block063HeadSum X0 = surrogateDiagTailX0RatChunk001Sub001Block063Head

def SurrogateDiagonalTailChunk001Sub001Block063MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub001Block063MidSum X0 = surrogateDiagTailX0RatChunk001Sub001Block063Mid

def SurrogateDiagonalTailChunk001Sub001Block063TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub001Block063TailSum X0 = surrogateDiagTailX0RatChunk001Sub001Block063Tail

theorem surrogateDiagonalTailChunk001Sub001Block063_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk001Sub001Block063HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk001Sub001Block063MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk001Sub001Block063TailCertificateAt X0) :
    surrogateDiagonalTailChunk001Sub001Block063Sum X0 = surrogateDiagTailX0RatChunk001Sub001Block063 := by
  unfold SurrogateDiagonalTailChunk001Sub001Block063HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk001Sub001Block063MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk001Sub001Block063TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk001Sub001Block063Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk001Sub001Block063_eq_head_add_mid_add_tail

/-- Block 064 covers tail-support indices [16600,16625) and q from 27355 to 27394. -/

def TailChunk001Sub001Block064Part000SupportExplicit : Finset ℕ :=
  ([27355] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block064Part000 : ℚ :=
  (4990151343 : ℚ) / 1528216420456724480

def SurrogateDiagonalTailChunk001Sub001Block064Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27355
    = surrogateDiagTailX0RatChunk001Sub001Block064Part000

theorem surrogateDiagonalTailChunk001Sub001Block064Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block064Part000CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block064Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block064Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block064Part000CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block064Part000SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block064Part000] using hcert

def TailChunk001Sub001Block064Part001SupportExplicit : Finset ℕ :=
  ([27357] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block064Part001 : ℚ :=
  (4141221337 : ℚ) / 163519800396595200

def SurrogateDiagonalTailChunk001Sub001Block064Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27357
    = surrogateDiagTailX0RatChunk001Sub001Block064Part001

theorem surrogateDiagonalTailChunk001Sub001Block064Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block064Part001CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block064Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block064Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block064Part001CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block064Part001SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block064Part001] using hcert

def TailChunk001Sub001Block064Part002SupportExplicit : Finset ℕ :=
  ([27358] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block064Part002 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block064Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27358
    = surrogateDiagTailX0RatChunk001Sub001Block064Part002

theorem surrogateDiagonalTailChunk001Sub001Block064Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block064Part002CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block064Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block064Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block064Part002CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block064Part002SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block064Part002] using hcert

def TailChunk001Sub001Block064Part003SupportExplicit : Finset ℕ :=
  ([27359] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block064Part003 : ℚ :=
  (179661697 : ℚ) / 2214780367500000000

def SurrogateDiagonalTailChunk001Sub001Block064Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27359
    = surrogateDiagTailX0RatChunk001Sub001Block064Part003

theorem surrogateDiagonalTailChunk001Sub001Block064Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block064Part003CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block064Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block064Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block064Part003CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block064Part003SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block064Part003] using hcert

def TailChunk001Sub001Block064Part004SupportExplicit : Finset ℕ :=
  ([27361] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block064Part004 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block064Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27361
    = surrogateDiagTailX0RatChunk001Sub001Block064Part004

theorem surrogateDiagonalTailChunk001Sub001Block064Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block064Part004CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block064Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block064Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block064Part004CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block064Part004SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block064Part004] using hcert

def TailChunk001Sub001Block064Part005SupportExplicit : Finset ℕ :=
  ([27362] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block064Part005 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block064Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27362
    = surrogateDiagTailX0RatChunk001Sub001Block064Part005

theorem surrogateDiagonalTailChunk001Sub001Block064Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block064Part005CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block064Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block064Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block064Part005CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block064Part005SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block064Part005] using hcert

def TailChunk001Sub001Block064Part006SupportExplicit : Finset ℕ :=
  ([27363] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block064Part006 : ℚ :=
  (265041254575 : ℚ) / 8277959073416610816

def SurrogateDiagonalTailChunk001Sub001Block064Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27363
    = surrogateDiagTailX0RatChunk001Sub001Block064Part006

theorem surrogateDiagonalTailChunk001Sub001Block064Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block064Part006CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block064Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block064Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block064Part006CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block064Part006SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block064Part006] using hcert

def TailChunk001Sub001Block064Part007SupportExplicit : Finset ℕ :=
  ([27365] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block064Part007 : ℚ :=
  (1677364489 : ℚ) / 337173070793932800

def SurrogateDiagonalTailChunk001Sub001Block064Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27365
    = surrogateDiagTailX0RatChunk001Sub001Block064Part007

theorem surrogateDiagonalTailChunk001Sub001Block064Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block064Part007CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block064Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block064Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block064Part007CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block064Part007SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block064Part007] using hcert

def TailChunk001Sub001Block064Part008SupportExplicit : Finset ℕ :=
  ([27366] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block064Part008 : ℚ :=
  (2600450147 : ℚ) / 34596822057615360

def SurrogateDiagonalTailChunk001Sub001Block064Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27366
    = surrogateDiagTailX0RatChunk001Sub001Block064Part008

theorem surrogateDiagonalTailChunk001Sub001Block064Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block064Part008CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block064Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block064Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block064Part008CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block064Part008SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block064Part008] using hcert

def TailChunk001Sub001Block064Part009SupportExplicit : Finset ℕ :=
  ([27367] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block064Part009 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block064Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27367
    = surrogateDiagTailX0RatChunk001Sub001Block064Part009

theorem surrogateDiagonalTailChunk001Sub001Block064Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block064Part009CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block064Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block064Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block064Part009CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block064Part009SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block064Part009] using hcert

def TailChunk001Sub001Block064Part010SupportExplicit : Finset ℕ :=
  ([27370] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block064Part010 : ℚ :=
  (314033721775 : ℚ) / 3184069130638589952

def SurrogateDiagonalTailChunk001Sub001Block064Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27370
    = surrogateDiagTailX0RatChunk001Sub001Block064Part010

theorem surrogateDiagonalTailChunk001Sub001Block064Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block064Part010CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block064Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block064Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block064Part010CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block064Part010SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block064Part010] using hcert

def TailChunk001Sub001Block064Part011SupportExplicit : Finset ℕ :=
  ([27371] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block064Part011 : ℚ :=
  (2265801701 : ℚ) / 26577364410000000000

def SurrogateDiagonalTailChunk001Sub001Block064Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27371
    = surrogateDiagTailX0RatChunk001Sub001Block064Part011

theorem surrogateDiagonalTailChunk001Sub001Block064Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block064Part011CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block064Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block064Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block064Part011CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block064Part011SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block064Part011] using hcert

def TailChunk001Sub001Block064Part012SupportExplicit : Finset ℕ :=
  ([27373] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block064Part012 : ℚ :=
  (2018141033 : ℚ) / 9805645883400474240

def SurrogateDiagonalTailChunk001Sub001Block064Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27373
    = surrogateDiagTailX0RatChunk001Sub001Block064Part012

theorem surrogateDiagonalTailChunk001Sub001Block064Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block064Part012CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block064Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block064Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block064Part012CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block064Part012SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block064Part012] using hcert

def TailChunk001Sub001Block064Part013SupportExplicit : Finset ℕ :=
  ([27374] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block064Part013 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block064Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27374
    = surrogateDiagTailX0RatChunk001Sub001Block064Part013

theorem surrogateDiagonalTailChunk001Sub001Block064Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block064Part013CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block064Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block064Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block064Part013CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block064Part013SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block064Part013] using hcert

def TailChunk001Sub001Block064Part014SupportExplicit : Finset ℕ :=
  ([27377] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block064Part014 : ℚ :=
  (38250103607 : ℚ) / 15148473993308865600

def SurrogateDiagonalTailChunk001Sub001Block064Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27377
    = surrogateDiagTailX0RatChunk001Sub001Block064Part014

theorem surrogateDiagonalTailChunk001Sub001Block064Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block064Part014CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block064Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block064Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block064Part014CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block064Part014SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block064Part014] using hcert

def TailChunk001Sub001Block064Part015SupportExplicit : Finset ℕ :=
  ([27379] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block064Part015 : ℚ :=
  (47876285761 : ℚ) / 29988191799072000000

def SurrogateDiagonalTailChunk001Sub001Block064Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27379
    = surrogateDiagTailX0RatChunk001Sub001Block064Part015

theorem surrogateDiagonalTailChunk001Sub001Block064Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block064Part015CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block064Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block064Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block064Part015CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block064Part015SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block064Part015] using hcert

def TailChunk001Sub001Block064Part016SupportExplicit : Finset ℕ :=
  ([27381] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block064Part016 : ℚ :=
  (2602933604675 : ℚ) / 138751824847673853504

def SurrogateDiagonalTailChunk001Sub001Block064Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27381
    = surrogateDiagTailX0RatChunk001Sub001Block064Part016

theorem surrogateDiagonalTailChunk001Sub001Block064Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block064Part016CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block064Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block064Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block064Part016CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block064Part016SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block064Part016] using hcert

def TailChunk001Sub001Block064Part017SupportExplicit : Finset ℕ :=
  ([27382] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block064Part017 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block064Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27382
    = surrogateDiagTailX0RatChunk001Sub001Block064Part017

theorem surrogateDiagonalTailChunk001Sub001Block064Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block064Part017CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block064Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block064Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block064Part017CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block064Part017SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block064Part017] using hcert

def TailChunk001Sub001Block064Part018SupportExplicit : Finset ℕ :=
  ([27383] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block064Part018 : ℚ :=
  (51449910875 : ℚ) / 669171589612966831104

def SurrogateDiagonalTailChunk001Sub001Block064Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27383
    = surrogateDiagTailX0RatChunk001Sub001Block064Part018

theorem surrogateDiagonalTailChunk001Sub001Block064Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block064Part018CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block064Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block064Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block064Part018CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block064Part018SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block064Part018] using hcert

def TailChunk001Sub001Block064Part019SupportExplicit : Finset ℕ :=
  ([27385] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block064Part019 : ℚ :=
  (16895599125 : ℚ) / 5185583159073538048

def SurrogateDiagonalTailChunk001Sub001Block064Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27385
    = surrogateDiagTailX0RatChunk001Sub001Block064Part019

theorem surrogateDiagonalTailChunk001Sub001Block064Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block064Part019CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block064Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block064Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block064Part019CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block064Part019SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block064Part019] using hcert

def TailChunk001Sub001Block064Part020SupportExplicit : Finset ℕ :=
  ([27386] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block064Part020 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block064Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27386
    = surrogateDiagTailX0RatChunk001Sub001Block064Part020

theorem surrogateDiagonalTailChunk001Sub001Block064Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block064Part020CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block064Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block064Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block064Part020CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block064Part020SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block064Part020] using hcert

def TailChunk001Sub001Block064Part021SupportExplicit : Finset ℕ :=
  ([27389] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block064Part021 : ℚ :=
  (3129341063 : ℚ) / 26108018518759833600

def SurrogateDiagonalTailChunk001Sub001Block064Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27389
    = surrogateDiagTailX0RatChunk001Sub001Block064Part021

theorem surrogateDiagonalTailChunk001Sub001Block064Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block064Part021CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block064Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block064Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block064Part021CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block064Part021SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block064Part021] using hcert

def TailChunk001Sub001Block064Part022SupportExplicit : Finset ℕ :=
  ([27390] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block064Part022 : ℚ :=
  (17997373419 : ℚ) / 61742036903526400

def SurrogateDiagonalTailChunk001Sub001Block064Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27390
    = surrogateDiagTailX0RatChunk001Sub001Block064Part022

theorem surrogateDiagonalTailChunk001Sub001Block064Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block064Part022CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block064Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block064Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block064Part022CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block064Part022SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block064Part022] using hcert

def TailChunk001Sub001Block064Part023SupportExplicit : Finset ℕ :=
  ([27393] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block064Part023 : ℚ :=
  (5021754150025 : ℚ) / 230472073210207961088

def SurrogateDiagonalTailChunk001Sub001Block064Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27393
    = surrogateDiagTailX0RatChunk001Sub001Block064Part023

theorem surrogateDiagonalTailChunk001Sub001Block064Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block064Part023CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block064Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block064Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block064Part023CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block064Part023SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block064Part023] using hcert

def TailChunk001Sub001Block064Part024SupportExplicit : Finset ℕ :=
  ([27394] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block064Part024 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block064Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27394
    = surrogateDiagTailX0RatChunk001Sub001Block064Part024

theorem surrogateDiagonalTailChunk001Sub001Block064Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block064Part024CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block064Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block064Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block064Part024CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block064Part024SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block064Part024] using hcert

def surrogateDiagonalTailChunk001Sub001Block064HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub001Block064Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block064Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block064Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block064Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block064Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block064Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block064Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block064Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block064Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block064Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub001Block064Head : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block064Part000
    + surrogateDiagTailX0RatChunk001Sub001Block064Part001
    + surrogateDiagTailX0RatChunk001Sub001Block064Part002
    + surrogateDiagTailX0RatChunk001Sub001Block064Part003
    + surrogateDiagTailX0RatChunk001Sub001Block064Part004
    + surrogateDiagTailX0RatChunk001Sub001Block064Part005
    + surrogateDiagTailX0RatChunk001Sub001Block064Part006
    + surrogateDiagTailX0RatChunk001Sub001Block064Part007
    + surrogateDiagTailX0RatChunk001Sub001Block064Part008
    + surrogateDiagTailX0RatChunk001Sub001Block064Part009

def surrogateDiagonalTailChunk001Sub001Block064MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub001Block064Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block064Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block064Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block064Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block064Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block064Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block064Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block064Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block064Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block064Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub001Block064Mid : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block064Part010
    + surrogateDiagTailX0RatChunk001Sub001Block064Part011
    + surrogateDiagTailX0RatChunk001Sub001Block064Part012
    + surrogateDiagTailX0RatChunk001Sub001Block064Part013
    + surrogateDiagTailX0RatChunk001Sub001Block064Part014
    + surrogateDiagTailX0RatChunk001Sub001Block064Part015
    + surrogateDiagTailX0RatChunk001Sub001Block064Part016
    + surrogateDiagTailX0RatChunk001Sub001Block064Part017
    + surrogateDiagTailX0RatChunk001Sub001Block064Part018
    + surrogateDiagTailX0RatChunk001Sub001Block064Part019

def surrogateDiagonalTailChunk001Sub001Block064TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub001Block064Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block064Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block064Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block064Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block064Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub001Block064Tail : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block064Part020
    + surrogateDiagTailX0RatChunk001Sub001Block064Part021
    + surrogateDiagTailX0RatChunk001Sub001Block064Part022
    + surrogateDiagTailX0RatChunk001Sub001Block064Part023
    + surrogateDiagTailX0RatChunk001Sub001Block064Part024

def surrogateDiagonalTailChunk001Sub001Block064Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk001Sub001Block064HeadSum X0
    + surrogateDiagonalTailChunk001Sub001Block064MidSum X0
    + surrogateDiagonalTailChunk001Sub001Block064TailSum X0

def surrogateDiagTailX0RatChunk001Sub001Block064 : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block064Part000
    + surrogateDiagTailX0RatChunk001Sub001Block064Part001
    + surrogateDiagTailX0RatChunk001Sub001Block064Part002
    + surrogateDiagTailX0RatChunk001Sub001Block064Part003
    + surrogateDiagTailX0RatChunk001Sub001Block064Part004
    + surrogateDiagTailX0RatChunk001Sub001Block064Part005
    + surrogateDiagTailX0RatChunk001Sub001Block064Part006
    + surrogateDiagTailX0RatChunk001Sub001Block064Part007
    + surrogateDiagTailX0RatChunk001Sub001Block064Part008
    + surrogateDiagTailX0RatChunk001Sub001Block064Part009
    + surrogateDiagTailX0RatChunk001Sub001Block064Part010
    + surrogateDiagTailX0RatChunk001Sub001Block064Part011
    + surrogateDiagTailX0RatChunk001Sub001Block064Part012
    + surrogateDiagTailX0RatChunk001Sub001Block064Part013
    + surrogateDiagTailX0RatChunk001Sub001Block064Part014
    + surrogateDiagTailX0RatChunk001Sub001Block064Part015
    + surrogateDiagTailX0RatChunk001Sub001Block064Part016
    + surrogateDiagTailX0RatChunk001Sub001Block064Part017
    + surrogateDiagTailX0RatChunk001Sub001Block064Part018
    + surrogateDiagTailX0RatChunk001Sub001Block064Part019
    + surrogateDiagTailX0RatChunk001Sub001Block064Part020
    + surrogateDiagTailX0RatChunk001Sub001Block064Part021
    + surrogateDiagTailX0RatChunk001Sub001Block064Part022
    + surrogateDiagTailX0RatChunk001Sub001Block064Part023
    + surrogateDiagTailX0RatChunk001Sub001Block064Part024

theorem surrogateDiagTailX0RatChunk001Sub001Block064_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk001Sub001Block064Head + surrogateDiagTailX0RatChunk001Sub001Block064Mid + surrogateDiagTailX0RatChunk001Sub001Block064Tail =
      surrogateDiagTailX0RatChunk001Sub001Block064 := by
  unfold surrogateDiagTailX0RatChunk001Sub001Block064Head surrogateDiagTailX0RatChunk001Sub001Block064Mid surrogateDiagTailX0RatChunk001Sub001Block064Tail surrogateDiagTailX0RatChunk001Sub001Block064
  ring

def SurrogateDiagonalTailChunk001Sub001Block064HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub001Block064HeadSum X0 = surrogateDiagTailX0RatChunk001Sub001Block064Head

def SurrogateDiagonalTailChunk001Sub001Block064MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub001Block064MidSum X0 = surrogateDiagTailX0RatChunk001Sub001Block064Mid

def SurrogateDiagonalTailChunk001Sub001Block064TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub001Block064TailSum X0 = surrogateDiagTailX0RatChunk001Sub001Block064Tail

theorem surrogateDiagonalTailChunk001Sub001Block064_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk001Sub001Block064HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk001Sub001Block064MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk001Sub001Block064TailCertificateAt X0) :
    surrogateDiagonalTailChunk001Sub001Block064Sum X0 = surrogateDiagTailX0RatChunk001Sub001Block064 := by
  unfold SurrogateDiagonalTailChunk001Sub001Block064HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk001Sub001Block064MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk001Sub001Block064TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk001Sub001Block064Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk001Sub001Block064_eq_head_add_mid_add_tail

/-- Block 065 covers tail-support indices [16625,16650) and q from 27395 to 27433. -/

def TailChunk001Sub001Block065Part000SupportExplicit : Finset ℕ :=
  ([27395] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block065Part000 : ℚ :=
  (1876780752625 : ℚ) / 576441096832417056768

def SurrogateDiagonalTailChunk001Sub001Block065Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27395
    = surrogateDiagTailX0RatChunk001Sub001Block065Part000

theorem surrogateDiagonalTailChunk001Sub001Block065Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block065Part000CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block065Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block065Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block065Part000CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block065Part000SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block065Part000] using hcert

def TailChunk001Sub001Block065Part001SupportExplicit : Finset ℕ :=
  ([27397] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block065Part001 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block065Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27397
    = surrogateDiagTailX0RatChunk001Sub001Block065Part001

theorem surrogateDiagonalTailChunk001Sub001Block065Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block065Part001CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block065Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block065Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block065Part001CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block065Part001SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block065Part001] using hcert

def TailChunk001Sub001Block065Part002SupportExplicit : Finset ℕ :=
  ([27398] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block065Part002 : ℚ :=
  (94844298625 : ℚ) / 4091476475082442752

def SurrogateDiagonalTailChunk001Sub001Block065Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27398
    = surrogateDiagTailX0RatChunk001Sub001Block065Part002

theorem surrogateDiagonalTailChunk001Sub001Block065Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block065Part002CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block065Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block065Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block065Part002CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block065Part002SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block065Part002] using hcert

def TailChunk001Sub001Block065Part003SupportExplicit : Finset ℕ :=
  ([27399] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block065Part003 : ℚ :=
  (162897311225 : ℚ) / 8694817573846330944

def SurrogateDiagonalTailChunk001Sub001Block065Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27399
    = surrogateDiagTailX0RatChunk001Sub001Block065Part003

theorem surrogateDiagonalTailChunk001Sub001Block065Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block065Part003CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block065Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block065Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block065Part003CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block065Part003SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block065Part003] using hcert

def TailChunk001Sub001Block065Part004SupportExplicit : Finset ℕ :=
  ([27401] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block065Part004 : ℚ :=
  (20320093307 : ℚ) / 16371993208340889600

def SurrogateDiagonalTailChunk001Sub001Block065Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27401
    = surrogateDiagTailX0RatChunk001Sub001Block065Part004

theorem surrogateDiagonalTailChunk001Sub001Block065Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block065Part004CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block065Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block065Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block065Part004CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block065Part004SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block065Part004] using hcert

def TailChunk001Sub001Block065Part005SupportExplicit : Finset ℕ :=
  ([27402] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block065Part005 : ℚ :=
  (651823661675 : ℚ) / 8694817573846330944

def SurrogateDiagonalTailChunk001Sub001Block065Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27402
    = surrogateDiagTailX0RatChunk001Sub001Block065Part005

theorem surrogateDiagonalTailChunk001Sub001Block065Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block065Part005CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block065Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block065Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block065Part005CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block065Part005SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block065Part005] using hcert

def TailChunk001Sub001Block065Part006SupportExplicit : Finset ℕ :=
  ([27403] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block065Part006 : ℚ :=
  (1793813975 : ℚ) / 16231484244388773888

def SurrogateDiagonalTailChunk001Sub001Block065Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27403
    = surrogateDiagTailX0RatChunk001Sub001Block065Part006

theorem surrogateDiagonalTailChunk001Sub001Block065Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block065Part006CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block065Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block065Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block065Part006CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block065Part006SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block065Part006] using hcert

def TailChunk001Sub001Block065Part007SupportExplicit : Finset ℕ :=
  ([27406] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block065Part007 : ℚ :=
  (16270703 : ℚ) / 16317511574224896

def SurrogateDiagonalTailChunk001Sub001Block065Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27406
    = surrogateDiagTailX0RatChunk001Sub001Block065Part007

theorem surrogateDiagonalTailChunk001Sub001Block065Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block065Part007CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block065Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block065Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block065Part007CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block065Part007SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block065Part007] using hcert

def TailChunk001Sub001Block065Part008SupportExplicit : Finset ℕ :=
  ([27407] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block065Part008 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block065Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27407
    = surrogateDiagTailX0RatChunk001Sub001Block065Part008

theorem surrogateDiagonalTailChunk001Sub001Block065Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block065Part008CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block065Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block065Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block065Part008CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block065Part008SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block065Part008] using hcert

def TailChunk001Sub001Block065Part009SupportExplicit : Finset ℕ :=
  ([27409] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block065Part009 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block065Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27409
    = surrogateDiagTailX0RatChunk001Sub001Block065Part009

theorem surrogateDiagonalTailChunk001Sub001Block065Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block065Part009CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block065Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block065Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block065Part009CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block065Part009SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block065Part009] using hcert

def TailChunk001Sub001Block065Part010SupportExplicit : Finset ℕ :=
  ([27410] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block065Part010 : ℚ :=
  (37580504509 : ℚ) / 1443208462631731200

def SurrogateDiagonalTailChunk001Sub001Block065Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27410
    = surrogateDiagTailX0RatChunk001Sub001Block065Part010

theorem surrogateDiagonalTailChunk001Sub001Block065Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block065Part010CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block065Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block065Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block065Part010CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block065Part010SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block065Part010] using hcert

def TailChunk001Sub001Block065Part011SupportExplicit : Finset ℕ :=
  ([27411] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block065Part011 : ℚ :=
  (1304320239775 : ℚ) / 69680492857089196032

def SurrogateDiagonalTailChunk001Sub001Block065Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27411
    = surrogateDiagTailX0RatChunk001Sub001Block065Part011

theorem surrogateDiagonalTailChunk001Sub001Block065Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block065Part011CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block065Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block065Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block065Part011CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block065Part011SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block065Part011] using hcert

def TailChunk001Sub001Block065Part012SupportExplicit : Finset ℕ :=
  ([27413] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block065Part012 : ℚ :=
  (5044035275 : ℚ) / 49129902318382464384

def SurrogateDiagonalTailChunk001Sub001Block065Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27413
    = surrogateDiagTailX0RatChunk001Sub001Block065Part012

theorem surrogateDiagonalTailChunk001Sub001Block065Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block065Part012CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block065Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block065Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block065Part012CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block065Part012SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block065Part012] using hcert

def TailChunk001Sub001Block065Part013SupportExplicit : Finset ℕ :=
  ([27415] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block065Part013 : ℚ :=
  (626506917375 : ℚ) / 192708865330461054976

def SurrogateDiagonalTailChunk001Sub001Block065Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27415
    = surrogateDiagTailX0RatChunk001Sub001Block065Part013

theorem surrogateDiagonalTailChunk001Sub001Block065Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block065Part013CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block065Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block065Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block065Part013CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block065Part013SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block065Part013] using hcert

def TailChunk001Sub001Block065Part014SupportExplicit : Finset ℕ :=
  ([27417] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block065Part014 : ℚ :=
  (247588159825 : ℚ) / 8126421492779974656

def SurrogateDiagonalTailChunk001Sub001Block065Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27417
    = surrogateDiagTailX0RatChunk001Sub001Block065Part014

theorem surrogateDiagonalTailChunk001Sub001Block065Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block065Part014CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block065Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block065Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block065Part014CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block065Part014SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block065Part014] using hcert

def TailChunk001Sub001Block065Part015SupportExplicit : Finset ℕ :=
  ([27418] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block065Part015 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block065Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27418
    = surrogateDiagTailX0RatChunk001Sub001Block065Part015

theorem surrogateDiagonalTailChunk001Sub001Block065Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block065Part015CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block065Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block065Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block065Part015CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block065Part015SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block065Part015] using hcert

def TailChunk001Sub001Block065Part016SupportExplicit : Finset ℕ :=
  ([27419] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block065Part016 : ℚ :=
  (960315945625 : ℚ) / 762083560009715632128

def SurrogateDiagonalTailChunk001Sub001Block065Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27419
    = surrogateDiagTailX0RatChunk001Sub001Block065Part016

theorem surrogateDiagonalTailChunk001Sub001Block065Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block065Part016CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block065Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block065Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block065Part016CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block065Part016SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block065Part016] using hcert

def TailChunk001Sub001Block065Part017SupportExplicit : Finset ℕ :=
  ([27421] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block065Part017 : ℚ :=
  (654244994275 : ℚ) / 1106539545578698702848

def SurrogateDiagonalTailChunk001Sub001Block065Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27421
    = surrogateDiagTailX0RatChunk001Sub001Block065Part017

theorem surrogateDiagonalTailChunk001Sub001Block065Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block065Part017CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block065Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block065Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block065Part017CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block065Part017SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block065Part017] using hcert

def TailChunk001Sub001Block065Part018SupportExplicit : Finset ℕ :=
  ([27422] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block065Part018 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block065Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27422
    = surrogateDiagTailX0RatChunk001Sub001Block065Part018

theorem surrogateDiagonalTailChunk001Sub001Block065Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block065Part018CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block065Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block065Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block065Part018CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block065Part018SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block065Part018] using hcert

def TailChunk001Sub001Block065Part019SupportExplicit : Finset ℕ :=
  ([27426] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block065Part019 : ℚ :=
  (652877342525 : ℚ) / 4685028426672390144

def SurrogateDiagonalTailChunk001Sub001Block065Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27426
    = surrogateDiagTailX0RatChunk001Sub001Block065Part019

theorem surrogateDiagonalTailChunk001Sub001Block065Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block065Part019CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block065Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block065Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block065Part019CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block065Part019SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block065Part019] using hcert

def TailChunk001Sub001Block065Part020SupportExplicit : Finset ℕ :=
  ([27427] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block065Part020 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block065Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27427
    = surrogateDiagTailX0RatChunk001Sub001Block065Part020

theorem surrogateDiagonalTailChunk001Sub001Block065Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block065Part020CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block065Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block065Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block065Part020CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block065Part020SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block065Part020] using hcert

def TailChunk001Sub001Block065Part021SupportExplicit : Finset ℕ :=
  ([27429] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block065Part021 : ℚ :=
  (67766906567 : ℚ) / 3316938668074598400

def SurrogateDiagonalTailChunk001Sub001Block065Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27429
    = surrogateDiagTailX0RatChunk001Sub001Block065Part021

theorem surrogateDiagonalTailChunk001Sub001Block065Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block065Part021CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block065Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block065Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block065Part021CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block065Part021SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block065Part021] using hcert

def TailChunk001Sub001Block065Part022SupportExplicit : Finset ℕ :=
  ([27430] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block065Part022 : ℚ :=
  (43038281551 : ℚ) / 1032592529306419200

def SurrogateDiagonalTailChunk001Sub001Block065Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27430
    = surrogateDiagTailX0RatChunk001Sub001Block065Part022

theorem surrogateDiagonalTailChunk001Sub001Block065Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block065Part022CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block065Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block065Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block065Part022CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block065Part022SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block065Part022] using hcert

def TailChunk001Sub001Block065Part023SupportExplicit : Finset ℕ :=
  ([27431] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block065Part023 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block065Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27431
    = surrogateDiagTailX0RatChunk001Sub001Block065Part023

theorem surrogateDiagonalTailChunk001Sub001Block065Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block065Part023CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block065Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block065Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block065Part023CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block065Part023SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block065Part023] using hcert

def TailChunk001Sub001Block065Part024SupportExplicit : Finset ℕ :=
  ([27433] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block065Part024 : ℚ :=
  (961295195725 : ℚ) / 763641614313636306048

def SurrogateDiagonalTailChunk001Sub001Block065Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27433
    = surrogateDiagTailX0RatChunk001Sub001Block065Part024

theorem surrogateDiagonalTailChunk001Sub001Block065Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block065Part024CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block065Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block065Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block065Part024CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block065Part024SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block065Part024] using hcert

def surrogateDiagonalTailChunk001Sub001Block065HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub001Block065Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block065Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block065Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block065Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block065Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block065Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block065Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block065Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block065Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block065Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub001Block065Head : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block065Part000
    + surrogateDiagTailX0RatChunk001Sub001Block065Part001
    + surrogateDiagTailX0RatChunk001Sub001Block065Part002
    + surrogateDiagTailX0RatChunk001Sub001Block065Part003
    + surrogateDiagTailX0RatChunk001Sub001Block065Part004
    + surrogateDiagTailX0RatChunk001Sub001Block065Part005
    + surrogateDiagTailX0RatChunk001Sub001Block065Part006
    + surrogateDiagTailX0RatChunk001Sub001Block065Part007
    + surrogateDiagTailX0RatChunk001Sub001Block065Part008
    + surrogateDiagTailX0RatChunk001Sub001Block065Part009

def surrogateDiagonalTailChunk001Sub001Block065MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub001Block065Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block065Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block065Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block065Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block065Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block065Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block065Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block065Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block065Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block065Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub001Block065Mid : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block065Part010
    + surrogateDiagTailX0RatChunk001Sub001Block065Part011
    + surrogateDiagTailX0RatChunk001Sub001Block065Part012
    + surrogateDiagTailX0RatChunk001Sub001Block065Part013
    + surrogateDiagTailX0RatChunk001Sub001Block065Part014
    + surrogateDiagTailX0RatChunk001Sub001Block065Part015
    + surrogateDiagTailX0RatChunk001Sub001Block065Part016
    + surrogateDiagTailX0RatChunk001Sub001Block065Part017
    + surrogateDiagTailX0RatChunk001Sub001Block065Part018
    + surrogateDiagTailX0RatChunk001Sub001Block065Part019

def surrogateDiagonalTailChunk001Sub001Block065TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub001Block065Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block065Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block065Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block065Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block065Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub001Block065Tail : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block065Part020
    + surrogateDiagTailX0RatChunk001Sub001Block065Part021
    + surrogateDiagTailX0RatChunk001Sub001Block065Part022
    + surrogateDiagTailX0RatChunk001Sub001Block065Part023
    + surrogateDiagTailX0RatChunk001Sub001Block065Part024

def surrogateDiagonalTailChunk001Sub001Block065Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk001Sub001Block065HeadSum X0
    + surrogateDiagonalTailChunk001Sub001Block065MidSum X0
    + surrogateDiagonalTailChunk001Sub001Block065TailSum X0

def surrogateDiagTailX0RatChunk001Sub001Block065 : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block065Part000
    + surrogateDiagTailX0RatChunk001Sub001Block065Part001
    + surrogateDiagTailX0RatChunk001Sub001Block065Part002
    + surrogateDiagTailX0RatChunk001Sub001Block065Part003
    + surrogateDiagTailX0RatChunk001Sub001Block065Part004
    + surrogateDiagTailX0RatChunk001Sub001Block065Part005
    + surrogateDiagTailX0RatChunk001Sub001Block065Part006
    + surrogateDiagTailX0RatChunk001Sub001Block065Part007
    + surrogateDiagTailX0RatChunk001Sub001Block065Part008
    + surrogateDiagTailX0RatChunk001Sub001Block065Part009
    + surrogateDiagTailX0RatChunk001Sub001Block065Part010
    + surrogateDiagTailX0RatChunk001Sub001Block065Part011
    + surrogateDiagTailX0RatChunk001Sub001Block065Part012
    + surrogateDiagTailX0RatChunk001Sub001Block065Part013
    + surrogateDiagTailX0RatChunk001Sub001Block065Part014
    + surrogateDiagTailX0RatChunk001Sub001Block065Part015
    + surrogateDiagTailX0RatChunk001Sub001Block065Part016
    + surrogateDiagTailX0RatChunk001Sub001Block065Part017
    + surrogateDiagTailX0RatChunk001Sub001Block065Part018
    + surrogateDiagTailX0RatChunk001Sub001Block065Part019
    + surrogateDiagTailX0RatChunk001Sub001Block065Part020
    + surrogateDiagTailX0RatChunk001Sub001Block065Part021
    + surrogateDiagTailX0RatChunk001Sub001Block065Part022
    + surrogateDiagTailX0RatChunk001Sub001Block065Part023
    + surrogateDiagTailX0RatChunk001Sub001Block065Part024

theorem surrogateDiagTailX0RatChunk001Sub001Block065_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk001Sub001Block065Head + surrogateDiagTailX0RatChunk001Sub001Block065Mid + surrogateDiagTailX0RatChunk001Sub001Block065Tail =
      surrogateDiagTailX0RatChunk001Sub001Block065 := by
  unfold surrogateDiagTailX0RatChunk001Sub001Block065Head surrogateDiagTailX0RatChunk001Sub001Block065Mid surrogateDiagTailX0RatChunk001Sub001Block065Tail surrogateDiagTailX0RatChunk001Sub001Block065
  ring

def SurrogateDiagonalTailChunk001Sub001Block065HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub001Block065HeadSum X0 = surrogateDiagTailX0RatChunk001Sub001Block065Head

def SurrogateDiagonalTailChunk001Sub001Block065MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub001Block065MidSum X0 = surrogateDiagTailX0RatChunk001Sub001Block065Mid

def SurrogateDiagonalTailChunk001Sub001Block065TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub001Block065TailSum X0 = surrogateDiagTailX0RatChunk001Sub001Block065Tail

theorem surrogateDiagonalTailChunk001Sub001Block065_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk001Sub001Block065HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk001Sub001Block065MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk001Sub001Block065TailCertificateAt X0) :
    surrogateDiagonalTailChunk001Sub001Block065Sum X0 = surrogateDiagTailX0RatChunk001Sub001Block065 := by
  unfold SurrogateDiagonalTailChunk001Sub001Block065HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk001Sub001Block065MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk001Sub001Block065TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk001Sub001Block065Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk001Sub001Block065_eq_head_add_mid_add_tail

/-- Block 066 covers tail-support indices [16650,16675) and q from 27434 to 27473. -/

def TailChunk001Sub001Block066Part000SupportExplicit : Finset ℕ :=
  ([27434] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block066Part000 : ℚ :=
  (889552459 : ℚ) / 76520205643972608

def SurrogateDiagonalTailChunk001Sub001Block066Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27434
    = surrogateDiagTailX0RatChunk001Sub001Block066Part000

theorem surrogateDiagonalTailChunk001Sub001Block066Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block066Part000CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block066Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block066Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block066Part000CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block066Part000SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block066Part000] using hcert

def TailChunk001Sub001Block066Part001SupportExplicit : Finset ℕ :=
  ([27435] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block066Part001 : ℚ :=
  (83813232719 : ℚ) / 1877646342625689600

def SurrogateDiagonalTailChunk001Sub001Block066Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27435
    = surrogateDiagTailX0RatChunk001Sub001Block066Part001

theorem surrogateDiagonalTailChunk001Sub001Block066Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block066Part001CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block066Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block066Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block066Part001CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block066Part001SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block066Part001] using hcert

def TailChunk001Sub001Block066Part002SupportExplicit : Finset ℕ :=
  ([27437] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block066Part002 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block066Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27437
    = surrogateDiagTailX0RatChunk001Sub001Block066Part002

theorem surrogateDiagonalTailChunk001Sub001Block066Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block066Part002CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block066Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block066Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block066Part002CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block066Part002SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block066Part002] using hcert

def TailChunk001Sub001Block066Part003SupportExplicit : Finset ℕ :=
  ([27438] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block066Part003 : ℚ :=
  (1320798723025 : ℚ) / 13525893024042713088

def SurrogateDiagonalTailChunk001Sub001Block066Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27438
    = surrogateDiagTailX0RatChunk001Sub001Block066Part003

theorem surrogateDiagonalTailChunk001Sub001Block066Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block066Part003CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block066Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block066Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block066Part003CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block066Part003SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block066Part003] using hcert

def TailChunk001Sub001Block066Part004SupportExplicit : Finset ℕ :=
  ([27439] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block066Part004 : ℚ :=
  (180933978875 : ℚ) / 591279208787477151744

def SurrogateDiagonalTailChunk001Sub001Block066Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27439
    = surrogateDiagTailX0RatChunk001Sub001Block066Part004

theorem surrogateDiagonalTailChunk001Sub001Block066Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block066Part004CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block066Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block066Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block066Part004CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block066Part004SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block066Part004] using hcert

def TailChunk001Sub001Block066Part005SupportExplicit : Finset ℕ :=
  ([27442] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block066Part005 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block066Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27442
    = surrogateDiagTailX0RatChunk001Sub001Block066Part005

theorem surrogateDiagonalTailChunk001Sub001Block066Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block066Part005CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block066Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block066Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block066Part005CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block066Part005SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block066Part005] using hcert

def TailChunk001Sub001Block066Part006SupportExplicit : Finset ℕ :=
  ([27443] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block066Part006 : ℚ :=
  (8381877973 : ℚ) / 10277362243580428800

def SurrogateDiagonalTailChunk001Sub001Block066Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27443
    = surrogateDiagTailX0RatChunk001Sub001Block066Part006

theorem surrogateDiagonalTailChunk001Sub001Block066Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block066Part006CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block066Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block066Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block066Part006CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block066Part006SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block066Part006] using hcert

def TailChunk001Sub001Block066Part007SupportExplicit : Finset ℕ :=
  ([27445] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block066Part007 : ℚ :=
  (43341913097 : ℚ) / 7874340507238809600

def SurrogateDiagonalTailChunk001Sub001Block066Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27445
    = surrogateDiagTailX0RatChunk001Sub001Block066Part007

theorem surrogateDiagonalTailChunk001Sub001Block066Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block066Part007CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block066Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block066Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block066Part007CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block066Part007SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block066Part007] using hcert

def TailChunk001Sub001Block066Part008SupportExplicit : Finset ℕ :=
  ([27446] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block066Part008 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block066Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27446
    = surrogateDiagTailX0RatChunk001Sub001Block066Part008

theorem surrogateDiagonalTailChunk001Sub001Block066Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block066Part008CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block066Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block066Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block066Part008CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block066Part008SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block066Part008] using hcert

def TailChunk001Sub001Block066Part009SupportExplicit : Finset ℕ :=
  ([27447] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block066Part009 : ℚ :=
  (41492298575 : ℚ) / 1396692481597871616

def SurrogateDiagonalTailChunk001Sub001Block066Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27447
    = surrogateDiagTailX0RatChunk001Sub001Block066Part009

theorem surrogateDiagonalTailChunk001Sub001Block066Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block066Part009CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block066Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block066Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block066Part009CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block066Part009SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block066Part009] using hcert

def TailChunk001Sub001Block066Part010SupportExplicit : Finset ℕ :=
  ([27449] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block066Part010 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block066Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27449
    = surrogateDiagTailX0RatChunk001Sub001Block066Part010

theorem surrogateDiagonalTailChunk001Sub001Block066Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block066Part010CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block066Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block066Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block066Part010CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block066Part010SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block066Part010] using hcert

def TailChunk001Sub001Block066Part011SupportExplicit : Finset ℕ :=
  ([27451] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block066Part011 : ℚ :=
  (119418772825 : ℚ) / 1343099614093721468928

def SurrogateDiagonalTailChunk001Sub001Block066Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27451
    = surrogateDiagTailX0RatChunk001Sub001Block066Part011

theorem surrogateDiagonalTailChunk001Sub001Block066Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block066Part011CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block066Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block066Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block066Part011CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block066Part011SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block066Part011] using hcert

def TailChunk001Sub001Block066Part012SupportExplicit : Finset ℕ :=
  ([27453] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block066Part012 : ℚ :=
  (4186624967 : ℚ) / 224347484724840000

def SurrogateDiagonalTailChunk001Sub001Block066Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27453
    = surrogateDiagTailX0RatChunk001Sub001Block066Part012

theorem surrogateDiagonalTailChunk001Sub001Block066Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block066Part012CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block066Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block066Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block066Part012CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block066Part012SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block066Part012] using hcert

def TailChunk001Sub001Block066Part013SupportExplicit : Finset ℕ :=
  ([27454] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block066Part013 : ℚ :=
  (102686719625 : ℚ) / 4974681161164455936

def SurrogateDiagonalTailChunk001Sub001Block066Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27454
    = surrogateDiagTailX0RatChunk001Sub001Block066Part013

theorem surrogateDiagonalTailChunk001Sub001Block066Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block066Part013CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block066Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block066Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block066Part013CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block066Part013SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block066Part013] using hcert

def TailChunk001Sub001Block066Part014SupportExplicit : Finset ℕ :=
  ([27457] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block066Part014 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block066Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27457
    = surrogateDiagTailX0RatChunk001Sub001Block066Part014

theorem surrogateDiagonalTailChunk001Sub001Block066Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block066Part014CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block066Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block066Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block066Part014CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block066Part014SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block066Part014] using hcert

def TailChunk001Sub001Block066Part015SupportExplicit : Finset ℕ :=
  ([27458] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block066Part015 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block066Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27458
    = surrogateDiagTailX0RatChunk001Sub001Block066Part015

theorem surrogateDiagonalTailChunk001Sub001Block066Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block066Part015CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block066Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block066Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block066Part015CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block066Part015SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block066Part015] using hcert

def TailChunk001Sub001Block066Part016SupportExplicit : Finset ℕ :=
  ([27461] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block066Part016 : ℚ :=
  (963255195925 : ℚ) / 766764888826404060288

def SurrogateDiagonalTailChunk001Sub001Block066Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27461
    = surrogateDiagTailX0RatChunk001Sub001Block066Part016

theorem surrogateDiagonalTailChunk001Sub001Block066Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block066Part016CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block066Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block066Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block066Part016CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block066Part016SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block066Part016] using hcert

def TailChunk001Sub001Block066Part017SupportExplicit : Finset ℕ :=
  ([27462] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block066Part017 : ℚ :=
  (41163200825 : ℚ) / 450140767988687424

def SurrogateDiagonalTailChunk001Sub001Block066Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27462
    = surrogateDiagTailX0RatChunk001Sub001Block066Part017

theorem surrogateDiagonalTailChunk001Sub001Block066Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block066Part017CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block066Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block066Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block066Part017CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block066Part017SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block066Part017] using hcert

def TailChunk001Sub001Block066Part018SupportExplicit : Finset ℕ :=
  ([27463] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block066Part018 : ℚ :=
  (343990082575 : ℚ) / 1230902148855662266368

def SurrogateDiagonalTailChunk001Sub001Block066Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27463
    = surrogateDiagTailX0RatChunk001Sub001Block066Part018

theorem surrogateDiagonalTailChunk001Sub001Block066Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block066Part018CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block066Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block066Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block066Part018CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block066Part018SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block066Part018] using hcert

def TailChunk001Sub001Block066Part019SupportExplicit : Finset ℕ :=
  ([27465] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block066Part019 : ℚ :=
  (71220833249 : ℚ) / 2297318243582361600

def SurrogateDiagonalTailChunk001Sub001Block066Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27465
    = surrogateDiagTailX0RatChunk001Sub001Block066Part019

theorem surrogateDiagonalTailChunk001Sub001Block066Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block066Part019CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block066Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block066Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block066Part019CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block066Part019SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block066Part019] using hcert

def TailChunk001Sub001Block066Part020SupportExplicit : Finset ℕ :=
  ([27466] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block066Part020 : ℚ :=
  (956026247 : ℚ) / 515358799845739200

def SurrogateDiagonalTailChunk001Sub001Block066Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27466
    = surrogateDiagTailX0RatChunk001Sub001Block066Part020

theorem surrogateDiagonalTailChunk001Sub001Block066Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block066Part020CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block066Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block066Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block066Part020CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block066Part020SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block066Part020] using hcert

def TailChunk001Sub001Block066Part021SupportExplicit : Finset ℕ :=
  ([27469] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block066Part021 : ℚ :=
  (62356664225 : ℚ) / 114626488702989238272

def SurrogateDiagonalTailChunk001Sub001Block066Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27469
    = surrogateDiagTailX0RatChunk001Sub001Block066Part021

theorem surrogateDiagonalTailChunk001Sub001Block066Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block066Part021CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block066Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block066Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block066Part021CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block066Part021SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block066Part021] using hcert

def TailChunk001Sub001Block066Part022SupportExplicit : Finset ℕ :=
  ([27470] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block066Part022 : ℚ :=
  (2517020831 : ℚ) / 138197444906188800

def SurrogateDiagonalTailChunk001Sub001Block066Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27470
    = surrogateDiagTailX0RatChunk001Sub001Block066Part022

theorem surrogateDiagonalTailChunk001Sub001Block066Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block066Part022CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block066Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block066Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block066Part022CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block066Part022SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block066Part022] using hcert

def TailChunk001Sub001Block066Part023SupportExplicit : Finset ℕ :=
  ([27471] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block066Part023 : ℚ :=
  (93574034975 : ℚ) / 5020904379520528128

def SurrogateDiagonalTailChunk001Sub001Block066Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27471
    = surrogateDiagTailX0RatChunk001Sub001Block066Part023

theorem surrogateDiagonalTailChunk001Sub001Block066Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block066Part023CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block066Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block066Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block066Part023CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block066Part023SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block066Part023] using hcert

def TailChunk001Sub001Block066Part024SupportExplicit : Finset ℕ :=
  ([27473] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block066Part024 : ℚ :=
  (10289827 : ℚ) / 108340995127052160

def SurrogateDiagonalTailChunk001Sub001Block066Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27473
    = surrogateDiagTailX0RatChunk001Sub001Block066Part024

theorem surrogateDiagonalTailChunk001Sub001Block066Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block066Part024CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block066Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block066Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block066Part024CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block066Part024SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block066Part024] using hcert

def surrogateDiagonalTailChunk001Sub001Block066HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub001Block066Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block066Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block066Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block066Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block066Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block066Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block066Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block066Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block066Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block066Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub001Block066Head : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block066Part000
    + surrogateDiagTailX0RatChunk001Sub001Block066Part001
    + surrogateDiagTailX0RatChunk001Sub001Block066Part002
    + surrogateDiagTailX0RatChunk001Sub001Block066Part003
    + surrogateDiagTailX0RatChunk001Sub001Block066Part004
    + surrogateDiagTailX0RatChunk001Sub001Block066Part005
    + surrogateDiagTailX0RatChunk001Sub001Block066Part006
    + surrogateDiagTailX0RatChunk001Sub001Block066Part007
    + surrogateDiagTailX0RatChunk001Sub001Block066Part008
    + surrogateDiagTailX0RatChunk001Sub001Block066Part009

def surrogateDiagonalTailChunk001Sub001Block066MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub001Block066Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block066Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block066Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block066Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block066Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block066Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block066Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block066Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block066Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block066Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub001Block066Mid : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block066Part010
    + surrogateDiagTailX0RatChunk001Sub001Block066Part011
    + surrogateDiagTailX0RatChunk001Sub001Block066Part012
    + surrogateDiagTailX0RatChunk001Sub001Block066Part013
    + surrogateDiagTailX0RatChunk001Sub001Block066Part014
    + surrogateDiagTailX0RatChunk001Sub001Block066Part015
    + surrogateDiagTailX0RatChunk001Sub001Block066Part016
    + surrogateDiagTailX0RatChunk001Sub001Block066Part017
    + surrogateDiagTailX0RatChunk001Sub001Block066Part018
    + surrogateDiagTailX0RatChunk001Sub001Block066Part019

def surrogateDiagonalTailChunk001Sub001Block066TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub001Block066Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block066Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block066Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block066Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block066Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub001Block066Tail : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block066Part020
    + surrogateDiagTailX0RatChunk001Sub001Block066Part021
    + surrogateDiagTailX0RatChunk001Sub001Block066Part022
    + surrogateDiagTailX0RatChunk001Sub001Block066Part023
    + surrogateDiagTailX0RatChunk001Sub001Block066Part024

def surrogateDiagonalTailChunk001Sub001Block066Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk001Sub001Block066HeadSum X0
    + surrogateDiagonalTailChunk001Sub001Block066MidSum X0
    + surrogateDiagonalTailChunk001Sub001Block066TailSum X0

def surrogateDiagTailX0RatChunk001Sub001Block066 : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block066Part000
    + surrogateDiagTailX0RatChunk001Sub001Block066Part001
    + surrogateDiagTailX0RatChunk001Sub001Block066Part002
    + surrogateDiagTailX0RatChunk001Sub001Block066Part003
    + surrogateDiagTailX0RatChunk001Sub001Block066Part004
    + surrogateDiagTailX0RatChunk001Sub001Block066Part005
    + surrogateDiagTailX0RatChunk001Sub001Block066Part006
    + surrogateDiagTailX0RatChunk001Sub001Block066Part007
    + surrogateDiagTailX0RatChunk001Sub001Block066Part008
    + surrogateDiagTailX0RatChunk001Sub001Block066Part009
    + surrogateDiagTailX0RatChunk001Sub001Block066Part010
    + surrogateDiagTailX0RatChunk001Sub001Block066Part011
    + surrogateDiagTailX0RatChunk001Sub001Block066Part012
    + surrogateDiagTailX0RatChunk001Sub001Block066Part013
    + surrogateDiagTailX0RatChunk001Sub001Block066Part014
    + surrogateDiagTailX0RatChunk001Sub001Block066Part015
    + surrogateDiagTailX0RatChunk001Sub001Block066Part016
    + surrogateDiagTailX0RatChunk001Sub001Block066Part017
    + surrogateDiagTailX0RatChunk001Sub001Block066Part018
    + surrogateDiagTailX0RatChunk001Sub001Block066Part019
    + surrogateDiagTailX0RatChunk001Sub001Block066Part020
    + surrogateDiagTailX0RatChunk001Sub001Block066Part021
    + surrogateDiagTailX0RatChunk001Sub001Block066Part022
    + surrogateDiagTailX0RatChunk001Sub001Block066Part023
    + surrogateDiagTailX0RatChunk001Sub001Block066Part024

theorem surrogateDiagTailX0RatChunk001Sub001Block066_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk001Sub001Block066Head + surrogateDiagTailX0RatChunk001Sub001Block066Mid + surrogateDiagTailX0RatChunk001Sub001Block066Tail =
      surrogateDiagTailX0RatChunk001Sub001Block066 := by
  unfold surrogateDiagTailX0RatChunk001Sub001Block066Head surrogateDiagTailX0RatChunk001Sub001Block066Mid surrogateDiagTailX0RatChunk001Sub001Block066Tail surrogateDiagTailX0RatChunk001Sub001Block066
  ring

def SurrogateDiagonalTailChunk001Sub001Block066HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub001Block066HeadSum X0 = surrogateDiagTailX0RatChunk001Sub001Block066Head

def SurrogateDiagonalTailChunk001Sub001Block066MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub001Block066MidSum X0 = surrogateDiagTailX0RatChunk001Sub001Block066Mid

def SurrogateDiagonalTailChunk001Sub001Block066TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub001Block066TailSum X0 = surrogateDiagTailX0RatChunk001Sub001Block066Tail

theorem surrogateDiagonalTailChunk001Sub001Block066_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk001Sub001Block066HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk001Sub001Block066MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk001Sub001Block066TailCertificateAt X0) :
    surrogateDiagonalTailChunk001Sub001Block066Sum X0 = surrogateDiagTailX0RatChunk001Sub001Block066 := by
  unfold SurrogateDiagonalTailChunk001Sub001Block066HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk001Sub001Block066MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk001Sub001Block066TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk001Sub001Block066Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk001Sub001Block066_eq_head_add_mid_add_tail

/-- Block 067 covers tail-support indices [16675,16700) and q from 27474 to 27514. -/

def TailChunk001Sub001Block067Part000SupportExplicit : Finset ℕ :=
  ([27474] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block067Part000 : ℚ :=
  (53009676127 : ℚ) / 557367729271603200

def SurrogateDiagonalTailChunk001Sub001Block067Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27474
    = surrogateDiagTailX0RatChunk001Sub001Block067Part000

theorem surrogateDiagonalTailChunk001Sub001Block067Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block067Part000CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block067Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block067Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block067Part000CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block067Part000SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block067Part000] using hcert

def TailChunk001Sub001Block067Part001SupportExplicit : Finset ℕ :=
  ([27478] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block067Part001 : ℚ :=
  (15690785029 : ℚ) / 2426303873758003200

def SurrogateDiagonalTailChunk001Sub001Block067Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27478
    = surrogateDiagTailX0RatChunk001Sub001Block067Part001

theorem surrogateDiagonalTailChunk001Sub001Block067Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block067Part001CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block067Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block067Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block067Part001CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block067Part001SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block067Part001] using hcert

def TailChunk001Sub001Block067Part002SupportExplicit : Finset ℕ :=
  ([27479] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block067Part002 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block067Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27479
    = surrogateDiagTailX0RatChunk001Sub001Block067Part002

theorem surrogateDiagonalTailChunk001Sub001Block067Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block067Part002CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block067Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block067Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block067Part002CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block067Part002SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block067Part002] using hcert

def TailChunk001Sub001Block067Part003SupportExplicit : Finset ℕ :=
  ([27481] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block067Part003 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block067Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27481
    = surrogateDiagTailX0RatChunk001Sub001Block067Part003

theorem surrogateDiagonalTailChunk001Sub001Block067Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block067Part003CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block067Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block067Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block067Part003CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block067Part003SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block067Part003] using hcert

def TailChunk001Sub001Block067Part004SupportExplicit : Finset ℕ :=
  ([27482] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block067Part004 : ℚ :=
  (1390222219 : ℚ) / 54430442311680000

def SurrogateDiagonalTailChunk001Sub001Block067Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27482
    = surrogateDiagTailX0RatChunk001Sub001Block067Part004

theorem surrogateDiagonalTailChunk001Sub001Block067Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block067Part004CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block067Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block067Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block067Part004CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block067Part004SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block067Part004] using hcert

def TailChunk001Sub001Block067Part005SupportExplicit : Finset ℕ :=
  ([27483] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block067Part005 : ℚ :=
  (10489449917 : ℚ) / 563324619304181760

def SurrogateDiagonalTailChunk001Sub001Block067Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27483
    = surrogateDiagTailX0RatChunk001Sub001Block067Part005

theorem surrogateDiagonalTailChunk001Sub001Block067Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block067Part005CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block067Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block067Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block067Part005CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block067Part005SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block067Part005] using hcert

def TailChunk001Sub001Block067Part006SupportExplicit : Finset ℕ :=
  ([27485] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block067Part006 : ℚ :=
  (30619219275 : ℚ) / 7289897805981564928

def SurrogateDiagonalTailChunk001Sub001Block067Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27485
    = surrogateDiagTailX0RatChunk001Sub001Block067Part006

theorem surrogateDiagonalTailChunk001Sub001Block067Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block067Part006CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block067Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block067Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block067Part006CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block067Part006SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block067Part006] using hcert

def TailChunk001Sub001Block067Part007SupportExplicit : Finset ℕ :=
  ([27487] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block067Part007 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block067Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27487
    = surrogateDiagTailX0RatChunk001Sub001Block067Part007

theorem surrogateDiagonalTailChunk001Sub001Block067Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block067Part007CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block067Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block067Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block067Part007CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block067Part007SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block067Part007] using hcert

def TailChunk001Sub001Block067Part008SupportExplicit : Finset ℕ :=
  ([27490] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block067Part008 : ℚ :=
  (314999837575 : ℚ) / 12167811776970326016

def SurrogateDiagonalTailChunk001Sub001Block067Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27490
    = surrogateDiagTailX0RatChunk001Sub001Block067Part008

theorem surrogateDiagonalTailChunk001Sub001Block067Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block067Part008CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block067Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block067Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block067Part008CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block067Part008SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block067Part008] using hcert

def TailChunk001Sub001Block067Part009SupportExplicit : Finset ℕ :=
  ([27491] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block067Part009 : ℚ :=
  (251823509275 : ℚ) / 1273070583317850605568

def SurrogateDiagonalTailChunk001Sub001Block067Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27491
    = surrogateDiagTailX0RatChunk001Sub001Block067Part009

theorem surrogateDiagonalTailChunk001Sub001Block067Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block067Part009CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block067Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block067Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block067Part009CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block067Part009SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block067Part009] using hcert

def TailChunk001Sub001Block067Part010SupportExplicit : Finset ℕ :=
  ([27493] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block067Part010 : ℚ :=
  (397512851575 : ℚ) / 1147598709316150451328

def SurrogateDiagonalTailChunk001Sub001Block067Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27493
    = surrogateDiagTailX0RatChunk001Sub001Block067Part010

theorem surrogateDiagonalTailChunk001Sub001Block067Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block067Part010CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block067Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block067Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block067Part010CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block067Part010SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block067Part010] using hcert

def TailChunk001Sub001Block067Part011SupportExplicit : Finset ℕ :=
  ([27494] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block067Part011 : ℚ :=
  (91873317025 : ℚ) / 81976764373990146048

def SurrogateDiagonalTailChunk001Sub001Block067Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27494
    = surrogateDiagTailX0RatChunk001Sub001Block067Part011

theorem surrogateDiagonalTailChunk001Sub001Block067Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block067Part011CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block067Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block067Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block067Part011CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block067Part011SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block067Part011] using hcert

def TailChunk001Sub001Block067Part012SupportExplicit : Finset ℕ :=
  ([27497] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block067Part012 : ℚ :=
  (12137596183 : ℚ) / 49923699064560259200

def SurrogateDiagonalTailChunk001Sub001Block067Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27497
    = surrogateDiagTailX0RatChunk001Sub001Block067Part012

theorem surrogateDiagonalTailChunk001Sub001Block067Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block067Part012CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block067Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block067Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block067Part012CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block067Part012SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block067Part012] using hcert

def TailChunk001Sub001Block067Part013SupportExplicit : Finset ℕ :=
  ([27498] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block067Part013 : ℚ :=
  (656397661475 : ℚ) / 8817331830466864704

def SurrogateDiagonalTailChunk001Sub001Block067Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27498
    = surrogateDiagTailX0RatChunk001Sub001Block067Part013

theorem surrogateDiagonalTailChunk001Sub001Block067Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block067Part013CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block067Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block067Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block067Part013CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block067Part013SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block067Part013] using hcert

def TailChunk001Sub001Block067Part014SupportExplicit : Finset ℕ :=
  ([27499] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block067Part014 : ℚ :=
  (36952980375 : ℚ) / 451948476217044238336

def SurrogateDiagonalTailChunk001Sub001Block067Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27499
    = surrogateDiagTailX0RatChunk001Sub001Block067Part014

theorem surrogateDiagonalTailChunk001Sub001Block067Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block067Part014CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block067Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block067Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block067Part014CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block067Part014SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block067Part014] using hcert

def TailChunk001Sub001Block067Part015SupportExplicit : Finset ℕ :=
  ([27501] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block067Part015 : ℚ :=
  (2576296955825 : ℚ) / 129851873955110191104

def SurrogateDiagonalTailChunk001Sub001Block067Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27501
    = surrogateDiagTailX0RatChunk001Sub001Block067Part015

theorem surrogateDiagonalTailChunk001Sub001Block067Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block067Part015CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block067Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block067Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block067Part015CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block067Part015SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block067Part015] using hcert

def TailChunk001Sub001Block067Part016SupportExplicit : Finset ℕ :=
  ([27502] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block067Part016 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block067Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27502
    = surrogateDiagTailX0RatChunk001Sub001Block067Part016

theorem surrogateDiagonalTailChunk001Sub001Block067Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block067Part016CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block067Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block067Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block067Part016CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block067Part016SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block067Part016] using hcert

def TailChunk001Sub001Block067Part017SupportExplicit : Finset ℕ :=
  ([27503] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block067Part017 : ℚ :=
  (966198946225 : ℚ) / 771467751952824434688

def SurrogateDiagonalTailChunk001Sub001Block067Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27503
    = surrogateDiagTailX0RatChunk001Sub001Block067Part017

theorem surrogateDiagonalTailChunk001Sub001Block067Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block067Part017CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block067Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block067Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block067Part017CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block067Part017SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block067Part017] using hcert

def TailChunk001Sub001Block067Part018SupportExplicit : Finset ℕ :=
  ([27505] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block067Part018 : ℚ :=
  (5045001333 : ℚ) / 1562019008000000000

def SurrogateDiagonalTailChunk001Sub001Block067Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27505
    = surrogateDiagTailX0RatChunk001Sub001Block067Part018

theorem surrogateDiagonalTailChunk001Sub001Block067Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block067Part018CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block067Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block067Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block067Part018CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block067Part018SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block067Part018] using hcert

def TailChunk001Sub001Block067Part019SupportExplicit : Finset ℕ :=
  ([27506] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block067Part019 : ℚ :=
  (41596270725 : ℚ) / 11641286622590271488

def SurrogateDiagonalTailChunk001Sub001Block067Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27506
    = surrogateDiagTailX0RatChunk001Sub001Block067Part019

theorem surrogateDiagonalTailChunk001Sub001Block067Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block067Part019CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block067Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block067Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block067Part019CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block067Part019SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block067Part019] using hcert

def TailChunk001Sub001Block067Part020SupportExplicit : Finset ℕ :=
  ([27507] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block067Part020 : ℚ :=
  (1284895542175 : ℚ) / 64005016280152276992

def SurrogateDiagonalTailChunk001Sub001Block067Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27507
    = surrogateDiagTailX0RatChunk001Sub001Block067Part020

theorem surrogateDiagonalTailChunk001Sub001Block067Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block067Part020CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block067Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block067Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block067Part020CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block067Part020SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block067Part020] using hcert

def TailChunk001Sub001Block067Part021SupportExplicit : Finset ℕ :=
  ([27509] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block067Part021 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block067Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27509
    = surrogateDiagTailX0RatChunk001Sub001Block067Part021

theorem surrogateDiagonalTailChunk001Sub001Block067Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block067Part021CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block067Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block067Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block067Part021CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block067Part021SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block067Part021] using hcert

def TailChunk001Sub001Block067Part022SupportExplicit : Finset ℕ :=
  ([27510] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block067Part022 : ℚ :=
  (1866972053 : ℚ) / 5616444152217600

def SurrogateDiagonalTailChunk001Sub001Block067Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27510
    = surrogateDiagTailX0RatChunk001Sub001Block067Part022

theorem surrogateDiagonalTailChunk001Sub001Block067Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block067Part022CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block067Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block067Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block067Part022CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block067Part022SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block067Part022] using hcert

def TailChunk001Sub001Block067Part023SupportExplicit : Finset ℕ :=
  ([27511] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block067Part023 : ℚ :=
  (40710477079 : ℚ) / 33184235520000000000

def SurrogateDiagonalTailChunk001Sub001Block067Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27511
    = surrogateDiagTailX0RatChunk001Sub001Block067Part023

theorem surrogateDiagonalTailChunk001Sub001Block067Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block067Part023CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block067Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block067Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block067Part023CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block067Part023SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block067Part023] using hcert

def TailChunk001Sub001Block067Part024SupportExplicit : Finset ℕ :=
  ([27514] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block067Part024 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block067Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27514
    = surrogateDiagTailX0RatChunk001Sub001Block067Part024

theorem surrogateDiagonalTailChunk001Sub001Block067Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block067Part024CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block067Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block067Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block067Part024CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block067Part024SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block067Part024] using hcert

def surrogateDiagonalTailChunk001Sub001Block067HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub001Block067Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block067Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block067Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block067Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block067Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block067Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block067Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block067Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block067Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block067Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub001Block067Head : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block067Part000
    + surrogateDiagTailX0RatChunk001Sub001Block067Part001
    + surrogateDiagTailX0RatChunk001Sub001Block067Part002
    + surrogateDiagTailX0RatChunk001Sub001Block067Part003
    + surrogateDiagTailX0RatChunk001Sub001Block067Part004
    + surrogateDiagTailX0RatChunk001Sub001Block067Part005
    + surrogateDiagTailX0RatChunk001Sub001Block067Part006
    + surrogateDiagTailX0RatChunk001Sub001Block067Part007
    + surrogateDiagTailX0RatChunk001Sub001Block067Part008
    + surrogateDiagTailX0RatChunk001Sub001Block067Part009

def surrogateDiagonalTailChunk001Sub001Block067MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub001Block067Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block067Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block067Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block067Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block067Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block067Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block067Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block067Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block067Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block067Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub001Block067Mid : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block067Part010
    + surrogateDiagTailX0RatChunk001Sub001Block067Part011
    + surrogateDiagTailX0RatChunk001Sub001Block067Part012
    + surrogateDiagTailX0RatChunk001Sub001Block067Part013
    + surrogateDiagTailX0RatChunk001Sub001Block067Part014
    + surrogateDiagTailX0RatChunk001Sub001Block067Part015
    + surrogateDiagTailX0RatChunk001Sub001Block067Part016
    + surrogateDiagTailX0RatChunk001Sub001Block067Part017
    + surrogateDiagTailX0RatChunk001Sub001Block067Part018
    + surrogateDiagTailX0RatChunk001Sub001Block067Part019

def surrogateDiagonalTailChunk001Sub001Block067TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub001Block067Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block067Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block067Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block067Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block067Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub001Block067Tail : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block067Part020
    + surrogateDiagTailX0RatChunk001Sub001Block067Part021
    + surrogateDiagTailX0RatChunk001Sub001Block067Part022
    + surrogateDiagTailX0RatChunk001Sub001Block067Part023
    + surrogateDiagTailX0RatChunk001Sub001Block067Part024

def surrogateDiagonalTailChunk001Sub001Block067Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk001Sub001Block067HeadSum X0
    + surrogateDiagonalTailChunk001Sub001Block067MidSum X0
    + surrogateDiagonalTailChunk001Sub001Block067TailSum X0

def surrogateDiagTailX0RatChunk001Sub001Block067 : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block067Part000
    + surrogateDiagTailX0RatChunk001Sub001Block067Part001
    + surrogateDiagTailX0RatChunk001Sub001Block067Part002
    + surrogateDiagTailX0RatChunk001Sub001Block067Part003
    + surrogateDiagTailX0RatChunk001Sub001Block067Part004
    + surrogateDiagTailX0RatChunk001Sub001Block067Part005
    + surrogateDiagTailX0RatChunk001Sub001Block067Part006
    + surrogateDiagTailX0RatChunk001Sub001Block067Part007
    + surrogateDiagTailX0RatChunk001Sub001Block067Part008
    + surrogateDiagTailX0RatChunk001Sub001Block067Part009
    + surrogateDiagTailX0RatChunk001Sub001Block067Part010
    + surrogateDiagTailX0RatChunk001Sub001Block067Part011
    + surrogateDiagTailX0RatChunk001Sub001Block067Part012
    + surrogateDiagTailX0RatChunk001Sub001Block067Part013
    + surrogateDiagTailX0RatChunk001Sub001Block067Part014
    + surrogateDiagTailX0RatChunk001Sub001Block067Part015
    + surrogateDiagTailX0RatChunk001Sub001Block067Part016
    + surrogateDiagTailX0RatChunk001Sub001Block067Part017
    + surrogateDiagTailX0RatChunk001Sub001Block067Part018
    + surrogateDiagTailX0RatChunk001Sub001Block067Part019
    + surrogateDiagTailX0RatChunk001Sub001Block067Part020
    + surrogateDiagTailX0RatChunk001Sub001Block067Part021
    + surrogateDiagTailX0RatChunk001Sub001Block067Part022
    + surrogateDiagTailX0RatChunk001Sub001Block067Part023
    + surrogateDiagTailX0RatChunk001Sub001Block067Part024

theorem surrogateDiagTailX0RatChunk001Sub001Block067_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk001Sub001Block067Head + surrogateDiagTailX0RatChunk001Sub001Block067Mid + surrogateDiagTailX0RatChunk001Sub001Block067Tail =
      surrogateDiagTailX0RatChunk001Sub001Block067 := by
  unfold surrogateDiagTailX0RatChunk001Sub001Block067Head surrogateDiagTailX0RatChunk001Sub001Block067Mid surrogateDiagTailX0RatChunk001Sub001Block067Tail surrogateDiagTailX0RatChunk001Sub001Block067
  ring

def SurrogateDiagonalTailChunk001Sub001Block067HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub001Block067HeadSum X0 = surrogateDiagTailX0RatChunk001Sub001Block067Head

def SurrogateDiagonalTailChunk001Sub001Block067MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub001Block067MidSum X0 = surrogateDiagTailX0RatChunk001Sub001Block067Mid

def SurrogateDiagonalTailChunk001Sub001Block067TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub001Block067TailSum X0 = surrogateDiagTailX0RatChunk001Sub001Block067Tail

theorem surrogateDiagonalTailChunk001Sub001Block067_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk001Sub001Block067HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk001Sub001Block067MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk001Sub001Block067TailCertificateAt X0) :
    surrogateDiagonalTailChunk001Sub001Block067Sum X0 = surrogateDiagTailX0RatChunk001Sub001Block067 := by
  unfold SurrogateDiagonalTailChunk001Sub001Block067HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk001Sub001Block067MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk001Sub001Block067TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk001Sub001Block067Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk001Sub001Block067_eq_head_add_mid_add_tail

/-- Block 068 covers tail-support indices [16700,16725) and q from 27515 to 27557. -/

def TailChunk001Sub001Block068Part000SupportExplicit : Finset ℕ :=
  ([27515] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block068Part000 : ℚ :=
  (1893250749625 : ℚ) / 586609603213600770048

def SurrogateDiagonalTailChunk001Sub001Block068Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27515
    = surrogateDiagTailX0RatChunk001Sub001Block068Part000

theorem surrogateDiagonalTailChunk001Sub001Block068Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block068Part000CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block068Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block068Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block068Part000CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block068Part000SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block068Part000] using hcert

def TailChunk001Sub001Block068Part001SupportExplicit : Finset ℕ :=
  ([27517] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block068Part001 : ℚ :=
  (38687247853 : ℚ) / 30921606791637379200

def SurrogateDiagonalTailChunk001Sub001Block068Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27517
    = surrogateDiagTailX0RatChunk001Sub001Block068Part001

theorem surrogateDiagonalTailChunk001Sub001Block068Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block068Part001CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block068Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block068Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block068Part001CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block068Part001SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block068Part001] using hcert

def TailChunk001Sub001Block068Part002SupportExplicit : Finset ℕ :=
  ([27518] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block068Part002 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block068Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27518
    = surrogateDiagTailX0RatChunk001Sub001Block068Part002

theorem surrogateDiagonalTailChunk001Sub001Block068Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block068Part002CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block068Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block068Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block068Part002CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block068Part002SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block068Part002] using hcert

def TailChunk001Sub001Block068Part003SupportExplicit : Finset ℕ :=
  ([27519] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block068Part003 : ℚ :=
  (657309244775 : ℚ) / 35392646530588621056

def SurrogateDiagonalTailChunk001Sub001Block068Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27519
    = surrogateDiagTailX0RatChunk001Sub001Block068Part003

theorem surrogateDiagonalTailChunk001Sub001Block068Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block068Part003CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block068Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block068Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block068Part003CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block068Part003SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block068Part003] using hcert

def TailChunk001Sub001Block068Part004SupportExplicit : Finset ℕ :=
  ([27521] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block068Part004 : ℚ :=
  (455141532725 : ℚ) / 428236773753958170624

def SurrogateDiagonalTailChunk001Sub001Block068Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27521
    = surrogateDiagTailX0RatChunk001Sub001Block068Part004

theorem surrogateDiagonalTailChunk001Sub001Block068Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block068Part004CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block068Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block068Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block068Part004CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block068Part004SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block068Part004] using hcert

def TailChunk001Sub001Block068Part005SupportExplicit : Finset ℕ :=
  ([27523] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block068Part005 : ℚ :=
  (41305283775 : ℚ) / 93592190634529521664

def SurrogateDiagonalTailChunk001Sub001Block068Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27523
    = surrogateDiagTailX0RatChunk001Sub001Block068Part005

theorem surrogateDiagonalTailChunk001Sub001Block068Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block068Part005CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block068Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block068Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block068Part005CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block068Part005SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block068Part005] using hcert

def TailChunk001Sub001Block068Part006SupportExplicit : Finset ℕ :=
  ([27526] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block068Part006 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block068Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27526
    = surrogateDiagTailX0RatChunk001Sub001Block068Part006

theorem surrogateDiagonalTailChunk001Sub001Block068Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block068Part006CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block068Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block068Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block068Part006CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block068Part006SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block068Part006] using hcert

def TailChunk001Sub001Block068Part007SupportExplicit : Finset ℕ :=
  ([27527] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block068Part007 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block068Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27527
    = surrogateDiagTailX0RatChunk001Sub001Block068Part007

theorem surrogateDiagonalTailChunk001Sub001Block068Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block068Part007CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block068Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block068Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block068Part007CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block068Part007SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block068Part007] using hcert

def TailChunk001Sub001Block068Part008SupportExplicit : Finset ℕ :=
  ([27529] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block068Part008 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block068Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27529
    = surrogateDiagTailX0RatChunk001Sub001Block068Part008

theorem surrogateDiagonalTailChunk001Sub001Block068Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block068Part008CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block068Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block068Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block068Part008CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block068Part008SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block068Part008] using hcert

def TailChunk001Sub001Block068Part009SupportExplicit : Finset ℕ :=
  ([27530] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block068Part009 : ℚ :=
  (947748961525 : ℚ) / 36716438035573506048

def SurrogateDiagonalTailChunk001Sub001Block068Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27530
    = surrogateDiagTailX0RatChunk001Sub001Block068Part009

theorem surrogateDiagonalTailChunk001Sub001Block068Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block068Part009CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block068Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block068Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block068Part009CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block068Part009SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block068Part009] using hcert

def TailChunk001Sub001Block068Part010SupportExplicit : Finset ℕ :=
  ([27533] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block068Part010 : ℚ :=
  (654559687 : ℚ) / 816572658542333400

def SurrogateDiagonalTailChunk001Sub001Block068Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27533
    = surrogateDiagTailX0RatChunk001Sub001Block068Part010

theorem surrogateDiagonalTailChunk001Sub001Block068Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block068Part010CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block068Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block068Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block068Part010CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block068Part010SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block068Part010] using hcert

def TailChunk001Sub001Block068Part011SupportExplicit : Finset ℕ :=
  ([27534] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block068Part011 : ℚ :=
  (605799212575 : ℚ) / 3184069130638589952

def SurrogateDiagonalTailChunk001Sub001Block068Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27534
    = surrogateDiagTailX0RatChunk001Sub001Block068Part011

theorem surrogateDiagonalTailChunk001Sub001Block068Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block068Part011CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block068Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block068Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block068Part011CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block068Part011SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block068Part011] using hcert

def TailChunk001Sub001Block068Part012SupportExplicit : Finset ℕ :=
  ([27535] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block068Part012 : ℚ :=
  (632000916375 : ℚ) / 196105781581023287296

def SurrogateDiagonalTailChunk001Sub001Block068Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27535
    = surrogateDiagTailX0RatChunk001Sub001Block068Part012

theorem surrogateDiagonalTailChunk001Sub001Block068Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block068Part012CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block068Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block068Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block068Part012CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block068Part012SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block068Part012] using hcert

def TailChunk001Sub001Block068Part013SupportExplicit : Finset ℕ :=
  ([27537] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block068Part013 : ℚ :=
  (95554713275 : ℚ) / 4809328665004081152

def SurrogateDiagonalTailChunk001Sub001Block068Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27537
    = surrogateDiagTailX0RatChunk001Sub001Block068Part013

theorem surrogateDiagonalTailChunk001Sub001Block068Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block068Part013CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block068Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block068Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block068Part013CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block068Part013SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block068Part013] using hcert

def TailChunk001Sub001Block068Part014SupportExplicit : Finset ℕ :=
  ([27539] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block068Part014 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block068Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27539
    = surrogateDiagTailX0RatChunk001Sub001Block068Part014

theorem surrogateDiagonalTailChunk001Sub001Block068Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block068Part014CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block068Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block068Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block068Part014CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block068Part014SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block068Part014] using hcert

def TailChunk001Sub001Block068Part015SupportExplicit : Finset ℕ :=
  ([27541] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block068Part015 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block068Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27541
    = surrogateDiagTailX0RatChunk001Sub001Block068Part015

theorem surrogateDiagonalTailChunk001Sub001Block068Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block068Part015CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block068Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block068Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block068Part015CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block068Part015SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block068Part015] using hcert

def TailChunk001Sub001Block068Part016SupportExplicit : Finset ℕ :=
  ([27542] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block068Part016 : ℚ :=
  (34876530075 : ℚ) / 27131158385025488896

def SurrogateDiagonalTailChunk001Sub001Block068Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27542
    = surrogateDiagTailX0RatChunk001Sub001Block068Part016

theorem surrogateDiagonalTailChunk001Sub001Block068Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block068Part016CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block068Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block068Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block068Part016CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block068Part016SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block068Part016] using hcert

def TailChunk001Sub001Block068Part017SupportExplicit : Finset ℕ :=
  ([27543] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block068Part017 : ℚ :=
  (2633824979 : ℚ) / 142065155384807040

def SurrogateDiagonalTailChunk001Sub001Block068Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27543
    = surrogateDiagTailX0RatChunk001Sub001Block068Part017

theorem surrogateDiagonalTailChunk001Sub001Block068Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block068Part017CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block068Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block068Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block068Part017CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block068Part017SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block068Part017] using hcert

def TailChunk001Sub001Block068Part018SupportExplicit : Finset ℕ :=
  ([27545] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block068Part018 : ℚ :=
  (180828537475 : ℚ) / 26386437795530563584

def SurrogateDiagonalTailChunk001Sub001Block068Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27545
    = surrogateDiagTailX0RatChunk001Sub001Block068Part018

theorem surrogateDiagonalTailChunk001Sub001Block068Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block068Part018CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block068Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block068Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block068Part018CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block068Part018SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block068Part018] using hcert

def TailChunk001Sub001Block068Part019SupportExplicit : Finset ℕ :=
  ([27546] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block068Part019 : ℚ :=
  (5269525291 : ℚ) / 71032577692403520

def SurrogateDiagonalTailChunk001Sub001Block068Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27546
    = surrogateDiagTailX0RatChunk001Sub001Block068Part019

theorem surrogateDiagonalTailChunk001Sub001Block068Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block068Part019CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block068Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block068Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block068Part019CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block068Part019SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block068Part019] using hcert

def TailChunk001Sub001Block068Part020SupportExplicit : Finset ℕ :=
  ([27551] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block068Part020 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block068Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27551
    = surrogateDiagTailX0RatChunk001Sub001Block068Part020

theorem surrogateDiagonalTailChunk001Sub001Block068Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block068Part020CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block068Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block068Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block068Part020CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block068Part020SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block068Part020] using hcert

def TailChunk001Sub001Block068Part021SupportExplicit : Finset ℕ :=
  ([27553] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block068Part021 : ℚ :=
  (6965599875 : ℚ) / 55599547643015431472

def SurrogateDiagonalTailChunk001Sub001Block068Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27553
    = surrogateDiagTailX0RatChunk001Sub001Block068Part021

theorem surrogateDiagonalTailChunk001Sub001Block068Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block068Part021CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block068Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block068Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block068Part021CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block068Part021SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block068Part021] using hcert

def TailChunk001Sub001Block068Part022SupportExplicit : Finset ℕ :=
  ([27554] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block068Part022 : ℚ :=
  (207694600975 : ℚ) / 74906985176037176448

def SurrogateDiagonalTailChunk001Sub001Block068Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27554
    = surrogateDiagTailX0RatChunk001Sub001Block068Part022

theorem surrogateDiagonalTailChunk001Sub001Block068Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block068Part022CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block068Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block068Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block068Part022CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block068Part022SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block068Part022] using hcert

def TailChunk001Sub001Block068Part023SupportExplicit : Finset ℕ :=
  ([27555] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block068Part023 : ℚ :=
  (2140093197 : ℚ) / 129618773781708800

def SurrogateDiagonalTailChunk001Sub001Block068Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27555
    = surrogateDiagTailX0RatChunk001Sub001Block068Part023

theorem surrogateDiagonalTailChunk001Sub001Block068Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block068Part023CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block068Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block068Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block068Part023CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block068Part023SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block068Part023] using hcert

def TailChunk001Sub001Block068Part024SupportExplicit : Finset ℕ :=
  ([27557] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block068Part024 : ℚ :=
  (34505359 : ℚ) / 78379836928819200

def SurrogateDiagonalTailChunk001Sub001Block068Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27557
    = surrogateDiagTailX0RatChunk001Sub001Block068Part024

theorem surrogateDiagonalTailChunk001Sub001Block068Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block068Part024CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block068Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block068Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block068Part024CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block068Part024SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block068Part024] using hcert

def surrogateDiagonalTailChunk001Sub001Block068HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub001Block068Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block068Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block068Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block068Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block068Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block068Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block068Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block068Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block068Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block068Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub001Block068Head : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block068Part000
    + surrogateDiagTailX0RatChunk001Sub001Block068Part001
    + surrogateDiagTailX0RatChunk001Sub001Block068Part002
    + surrogateDiagTailX0RatChunk001Sub001Block068Part003
    + surrogateDiagTailX0RatChunk001Sub001Block068Part004
    + surrogateDiagTailX0RatChunk001Sub001Block068Part005
    + surrogateDiagTailX0RatChunk001Sub001Block068Part006
    + surrogateDiagTailX0RatChunk001Sub001Block068Part007
    + surrogateDiagTailX0RatChunk001Sub001Block068Part008
    + surrogateDiagTailX0RatChunk001Sub001Block068Part009

def surrogateDiagonalTailChunk001Sub001Block068MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub001Block068Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block068Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block068Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block068Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block068Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block068Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block068Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block068Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block068Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block068Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub001Block068Mid : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block068Part010
    + surrogateDiagTailX0RatChunk001Sub001Block068Part011
    + surrogateDiagTailX0RatChunk001Sub001Block068Part012
    + surrogateDiagTailX0RatChunk001Sub001Block068Part013
    + surrogateDiagTailX0RatChunk001Sub001Block068Part014
    + surrogateDiagTailX0RatChunk001Sub001Block068Part015
    + surrogateDiagTailX0RatChunk001Sub001Block068Part016
    + surrogateDiagTailX0RatChunk001Sub001Block068Part017
    + surrogateDiagTailX0RatChunk001Sub001Block068Part018
    + surrogateDiagTailX0RatChunk001Sub001Block068Part019

def surrogateDiagonalTailChunk001Sub001Block068TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub001Block068Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block068Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block068Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block068Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block068Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub001Block068Tail : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block068Part020
    + surrogateDiagTailX0RatChunk001Sub001Block068Part021
    + surrogateDiagTailX0RatChunk001Sub001Block068Part022
    + surrogateDiagTailX0RatChunk001Sub001Block068Part023
    + surrogateDiagTailX0RatChunk001Sub001Block068Part024

def surrogateDiagonalTailChunk001Sub001Block068Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk001Sub001Block068HeadSum X0
    + surrogateDiagonalTailChunk001Sub001Block068MidSum X0
    + surrogateDiagonalTailChunk001Sub001Block068TailSum X0

def surrogateDiagTailX0RatChunk001Sub001Block068 : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block068Part000
    + surrogateDiagTailX0RatChunk001Sub001Block068Part001
    + surrogateDiagTailX0RatChunk001Sub001Block068Part002
    + surrogateDiagTailX0RatChunk001Sub001Block068Part003
    + surrogateDiagTailX0RatChunk001Sub001Block068Part004
    + surrogateDiagTailX0RatChunk001Sub001Block068Part005
    + surrogateDiagTailX0RatChunk001Sub001Block068Part006
    + surrogateDiagTailX0RatChunk001Sub001Block068Part007
    + surrogateDiagTailX0RatChunk001Sub001Block068Part008
    + surrogateDiagTailX0RatChunk001Sub001Block068Part009
    + surrogateDiagTailX0RatChunk001Sub001Block068Part010
    + surrogateDiagTailX0RatChunk001Sub001Block068Part011
    + surrogateDiagTailX0RatChunk001Sub001Block068Part012
    + surrogateDiagTailX0RatChunk001Sub001Block068Part013
    + surrogateDiagTailX0RatChunk001Sub001Block068Part014
    + surrogateDiagTailX0RatChunk001Sub001Block068Part015
    + surrogateDiagTailX0RatChunk001Sub001Block068Part016
    + surrogateDiagTailX0RatChunk001Sub001Block068Part017
    + surrogateDiagTailX0RatChunk001Sub001Block068Part018
    + surrogateDiagTailX0RatChunk001Sub001Block068Part019
    + surrogateDiagTailX0RatChunk001Sub001Block068Part020
    + surrogateDiagTailX0RatChunk001Sub001Block068Part021
    + surrogateDiagTailX0RatChunk001Sub001Block068Part022
    + surrogateDiagTailX0RatChunk001Sub001Block068Part023
    + surrogateDiagTailX0RatChunk001Sub001Block068Part024

theorem surrogateDiagTailX0RatChunk001Sub001Block068_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk001Sub001Block068Head + surrogateDiagTailX0RatChunk001Sub001Block068Mid + surrogateDiagTailX0RatChunk001Sub001Block068Tail =
      surrogateDiagTailX0RatChunk001Sub001Block068 := by
  unfold surrogateDiagTailX0RatChunk001Sub001Block068Head surrogateDiagTailX0RatChunk001Sub001Block068Mid surrogateDiagTailX0RatChunk001Sub001Block068Tail surrogateDiagTailX0RatChunk001Sub001Block068
  ring

def SurrogateDiagonalTailChunk001Sub001Block068HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub001Block068HeadSum X0 = surrogateDiagTailX0RatChunk001Sub001Block068Head

def SurrogateDiagonalTailChunk001Sub001Block068MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub001Block068MidSum X0 = surrogateDiagTailX0RatChunk001Sub001Block068Mid

def SurrogateDiagonalTailChunk001Sub001Block068TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub001Block068TailSum X0 = surrogateDiagTailX0RatChunk001Sub001Block068Tail

theorem surrogateDiagonalTailChunk001Sub001Block068_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk001Sub001Block068HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk001Sub001Block068MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk001Sub001Block068TailCertificateAt X0) :
    surrogateDiagonalTailChunk001Sub001Block068Sum X0 = surrogateDiagTailX0RatChunk001Sub001Block068 := by
  unfold SurrogateDiagonalTailChunk001Sub001Block068HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk001Sub001Block068MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk001Sub001Block068TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk001Sub001Block068Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk001Sub001Block068_eq_head_add_mid_add_tail

/-- Block 069 covers tail-support indices [16725,16750) and q from 27559 to 27598. -/

def TailChunk001Sub001Block069Part000SupportExplicit : Finset ℕ :=
  ([27559] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block069Part000 : ℚ :=
  (23903769221 : ℚ) / 13232108564022297600

def SurrogateDiagonalTailChunk001Sub001Block069Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27559
    = surrogateDiagTailX0RatChunk001Sub001Block069Part000

theorem surrogateDiagonalTailChunk001Sub001Block069Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block069Part000CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block069Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block069Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block069Part000CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block069Part000SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block069Part000] using hcert

def TailChunk001Sub001Block069Part001SupportExplicit : Finset ℕ :=
  ([27561] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block069Part001 : ℚ :=
  (41675 : ℚ) / 18987793353864576

def SurrogateDiagonalTailChunk001Sub001Block069Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27561
    = surrogateDiagTailX0RatChunk001Sub001Block069Part001

theorem surrogateDiagonalTailChunk001Sub001Block069Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block069Part001CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block069Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block069Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block069Part001CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block069Part001SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block069Part001] using hcert

def TailChunk001Sub001Block069Part002SupportExplicit : Finset ℕ :=
  ([27562] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block069Part002 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block069Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27562
    = surrogateDiagTailX0RatChunk001Sub001Block069Part002

theorem surrogateDiagonalTailChunk001Sub001Block069Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block069Part002CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block069Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block069Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block069Part002CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block069Part002SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block069Part002] using hcert

def TailChunk001Sub001Block069Part003SupportExplicit : Finset ℕ :=
  ([27563] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block069Part003 : ℚ :=
  (960937511 : ℚ) / 6527004629689958400

def SurrogateDiagonalTailChunk001Sub001Block069Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27563
    = surrogateDiagTailX0RatChunk001Sub001Block069Part003

theorem surrogateDiagonalTailChunk001Sub001Block069Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block069Part003CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block069Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block069Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block069Part003CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block069Part003SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block069Part003] using hcert

def TailChunk001Sub001Block069Part004SupportExplicit : Finset ℕ :=
  ([27565] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block069Part004 : ℚ :=
  (3357390775 : ℚ) / 871368752802299904

def SurrogateDiagonalTailChunk001Sub001Block069Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27565
    = surrogateDiagTailX0RatChunk001Sub001Block069Part004

theorem surrogateDiagonalTailChunk001Sub001Block069Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block069Part004CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block069Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block069Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block069Part004CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block069Part004SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block069Part004] using hcert

def TailChunk001Sub001Block069Part005SupportExplicit : Finset ℕ :=
  ([27566] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block069Part005 : ℚ :=
  (2087344021 : ℚ) / 72293517444326400

def SurrogateDiagonalTailChunk001Sub001Block069Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27566
    = surrogateDiagTailX0RatChunk001Sub001Block069Part005

theorem surrogateDiagonalTailChunk001Sub001Block069Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block069Part005CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block069Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block069Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block069Part005CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block069Part005SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block069Part005] using hcert

def TailChunk001Sub001Block069Part006SupportExplicit : Finset ℕ :=
  ([27569] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block069Part006 : ℚ :=
  (21237294973 : ℚ) / 46413987351282000000

def SurrogateDiagonalTailChunk001Sub001Block069Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27569
    = surrogateDiagTailX0RatChunk001Sub001Block069Part006

theorem surrogateDiagonalTailChunk001Sub001Block069Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block069Part006CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block069Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block069Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block069Part006CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block069Part006SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block069Part006] using hcert

def TailChunk001Sub001Block069Part007SupportExplicit : Finset ℕ :=
  ([27570] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block069Part007 : ℚ :=
  (171477588725 : ℚ) / 909216994462765056

def SurrogateDiagonalTailChunk001Sub001Block069Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27570
    = surrogateDiagTailX0RatChunk001Sub001Block069Part007

theorem surrogateDiagonalTailChunk001Sub001Block069Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block069Part007CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block069Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block069Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block069Part007CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block069Part007SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block069Part007] using hcert

def TailChunk001Sub001Block069Part008SupportExplicit : Finset ℕ :=
  ([27571] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block069Part008 : ℚ :=
  (64980028925 : ℚ) / 678722505082862183424

def SurrogateDiagonalTailChunk001Sub001Block069Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27571
    = surrogateDiagTailX0RatChunk001Sub001Block069Part008

theorem surrogateDiagonalTailChunk001Sub001Block069Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block069Part008CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block069Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block069Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block069Part008CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block069Part008SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block069Part008] using hcert

def TailChunk001Sub001Block069Part009SupportExplicit : Finset ℕ :=
  ([27573] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block069Part009 : ℚ :=
  (1199680939 : ℚ) / 95570598297600000

def SurrogateDiagonalTailChunk001Sub001Block069Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27573
    = surrogateDiagTailX0RatChunk001Sub001Block069Part009

theorem surrogateDiagonalTailChunk001Sub001Block069Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block069Part009CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block069Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block069Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block069Part009CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block069Part009SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block069Part009] using hcert

def TailChunk001Sub001Block069Part010SupportExplicit : Finset ℕ :=
  ([27574] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block069Part010 : ℚ :=
  (557310911 : ℚ) / 156759673857638400

def SurrogateDiagonalTailChunk001Sub001Block069Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27574
    = surrogateDiagTailX0RatChunk001Sub001Block069Part010

theorem surrogateDiagonalTailChunk001Sub001Block069Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block069Part010CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block069Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block069Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block069Part010CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block069Part010SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block069Part010] using hcert

def TailChunk001Sub001Block069Part011SupportExplicit : Finset ℕ :=
  ([27577] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block069Part011 : ℚ :=
  (4382870419 : ℚ) / 3187664423541227520

def SurrogateDiagonalTailChunk001Sub001Block069Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27577
    = surrogateDiagTailX0RatChunk001Sub001Block069Part011

theorem surrogateDiagonalTailChunk001Sub001Block069Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block069Part011CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block069Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block069Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block069Part011CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block069Part011SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block069Part011] using hcert

def TailChunk001Sub001Block069Part012SupportExplicit : Finset ℕ :=
  ([27578] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block069Part012 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block069Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27578
    = surrogateDiagTailX0RatChunk001Sub001Block069Part012

theorem surrogateDiagonalTailChunk001Sub001Block069Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block069Part012CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block069Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block069Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block069Part012CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block069Part012SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block069Part012] using hcert

def TailChunk001Sub001Block069Part013SupportExplicit : Finset ℕ :=
  ([27579] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block069Part013 : ℚ :=
  (57410976925 : ℚ) / 61300964268373573632

def SurrogateDiagonalTailChunk001Sub001Block069Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27579
    = surrogateDiagTailX0RatChunk001Sub001Block069Part013

theorem surrogateDiagonalTailChunk001Sub001Block069Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block069Part013CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block069Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block069Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block069Part013CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block069Part013SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block069Part013] using hcert

def TailChunk001Sub001Block069Part014SupportExplicit : Finset ℕ :=
  ([27581] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block069Part014 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block069Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27581
    = surrogateDiagTailX0RatChunk001Sub001Block069Part014

theorem surrogateDiagonalTailChunk001Sub001Block069Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block069Part014CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block069Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block069Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block069Part014CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block069Part014SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block069Part014] using hcert

def TailChunk001Sub001Block069Part015SupportExplicit : Finset ℕ :=
  ([27582] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block069Part015 : ℚ :=
  (165103259075 : ℚ) / 2231397461167462656

def SurrogateDiagonalTailChunk001Sub001Block069Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27582
    = surrogateDiagTailX0RatChunk001Sub001Block069Part015

theorem surrogateDiagonalTailChunk001Sub001Block069Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block069Part015CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block069Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block069Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block069Part015CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block069Part015SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block069Part015] using hcert

def TailChunk001Sub001Block069Part016SupportExplicit : Finset ℕ :=
  ([27583] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block069Part016 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block069Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27583
    = surrogateDiagTailX0RatChunk001Sub001Block069Part016

theorem surrogateDiagonalTailChunk001Sub001Block069Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block069Part016CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block069Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block069Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block069Part016CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block069Part016SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block069Part016] using hcert

def TailChunk001Sub001Block069Part017SupportExplicit : Finset ℕ :=
  ([27586] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block069Part017 : ℚ :=
  (1896564079 : ℚ) / 436399299783475200

def SurrogateDiagonalTailChunk001Sub001Block069Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27586
    = surrogateDiagTailX0RatChunk001Sub001Block069Part017

theorem surrogateDiagonalTailChunk001Sub001Block069Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block069Part017CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block069Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block069Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block069Part017CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block069Part017SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block069Part017] using hcert

def TailChunk001Sub001Block069Part018SupportExplicit : Finset ℕ :=
  ([27589] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block069Part018 : ℚ :=
  (207179250625 : ℚ) / 1320227119795124178048

def SurrogateDiagonalTailChunk001Sub001Block069Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27589
    = surrogateDiagTailX0RatChunk001Sub001Block069Part018

theorem surrogateDiagonalTailChunk001Sub001Block069Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block069Part018CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block069Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block069Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block069Part018CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block069Part018SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block069Part018] using hcert

def TailChunk001Sub001Block069Part019SupportExplicit : Finset ℕ :=
  ([27590] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block069Part019 : ℚ :=
  (1353992317 : ℚ) / 41459233471856640

def SurrogateDiagonalTailChunk001Sub001Block069Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27590
    = surrogateDiagTailX0RatChunk001Sub001Block069Part019

theorem surrogateDiagonalTailChunk001Sub001Block069Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block069Part019CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block069Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block069Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block069Part019CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block069Part019SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block069Part019] using hcert

def TailChunk001Sub001Block069Part020SupportExplicit : Finset ℕ :=
  ([27591] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block069Part020 : ℚ :=
  (450727 : ℚ) / 297203348275200

def SurrogateDiagonalTailChunk001Sub001Block069Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27591
    = surrogateDiagTailX0RatChunk001Sub001Block069Part020

theorem surrogateDiagonalTailChunk001Sub001Block069Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block069Part020CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block069Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block069Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block069Part020CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block069Part020SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block069Part020] using hcert

def TailChunk001Sub001Block069Part021SupportExplicit : Finset ℕ :=
  ([27593] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block069Part021 : ℚ :=
  (3173088253 : ℚ) / 17405345679173222400

def SurrogateDiagonalTailChunk001Sub001Block069Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27593
    = surrogateDiagTailX0RatChunk001Sub001Block069Part021

theorem surrogateDiagonalTailChunk001Sub001Block069Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block069Part021CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block069Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block069Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block069Part021CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block069Part021SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block069Part021] using hcert

def TailChunk001Sub001Block069Part022SupportExplicit : Finset ℕ :=
  ([27595] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block069Part022 : ℚ :=
  (634756915875 : ℚ) / 197820982292449662976

def SurrogateDiagonalTailChunk001Sub001Block069Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27595
    = surrogateDiagTailX0RatChunk001Sub001Block069Part022

theorem surrogateDiagonalTailChunk001Sub001Block069Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block069Part022CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block069Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block069Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block069Part022CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block069Part022SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block069Part022] using hcert

def TailChunk001Sub001Block069Part023SupportExplicit : Finset ℕ :=
  ([27597] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block069Part023 : ℚ :=
  (41675 : ℚ) / 19087205672174976

def SurrogateDiagonalTailChunk001Sub001Block069Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27597
    = surrogateDiagTailX0RatChunk001Sub001Block069Part023

theorem surrogateDiagonalTailChunk001Sub001Block069Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block069Part023CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block069Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block069Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block069Part023CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block069Part023SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block069Part023] using hcert

def TailChunk001Sub001Block069Part024SupportExplicit : Finset ℕ :=
  ([27598] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block069Part024 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block069Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27598
    = surrogateDiagTailX0RatChunk001Sub001Block069Part024

theorem surrogateDiagonalTailChunk001Sub001Block069Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block069Part024CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block069Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block069Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block069Part024CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block069Part024SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block069Part024] using hcert

def surrogateDiagonalTailChunk001Sub001Block069HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub001Block069Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block069Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block069Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block069Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block069Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block069Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block069Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block069Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block069Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block069Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub001Block069Head : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block069Part000
    + surrogateDiagTailX0RatChunk001Sub001Block069Part001
    + surrogateDiagTailX0RatChunk001Sub001Block069Part002
    + surrogateDiagTailX0RatChunk001Sub001Block069Part003
    + surrogateDiagTailX0RatChunk001Sub001Block069Part004
    + surrogateDiagTailX0RatChunk001Sub001Block069Part005
    + surrogateDiagTailX0RatChunk001Sub001Block069Part006
    + surrogateDiagTailX0RatChunk001Sub001Block069Part007
    + surrogateDiagTailX0RatChunk001Sub001Block069Part008
    + surrogateDiagTailX0RatChunk001Sub001Block069Part009

def surrogateDiagonalTailChunk001Sub001Block069MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub001Block069Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block069Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block069Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block069Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block069Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block069Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block069Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block069Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block069Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block069Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub001Block069Mid : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block069Part010
    + surrogateDiagTailX0RatChunk001Sub001Block069Part011
    + surrogateDiagTailX0RatChunk001Sub001Block069Part012
    + surrogateDiagTailX0RatChunk001Sub001Block069Part013
    + surrogateDiagTailX0RatChunk001Sub001Block069Part014
    + surrogateDiagTailX0RatChunk001Sub001Block069Part015
    + surrogateDiagTailX0RatChunk001Sub001Block069Part016
    + surrogateDiagTailX0RatChunk001Sub001Block069Part017
    + surrogateDiagTailX0RatChunk001Sub001Block069Part018
    + surrogateDiagTailX0RatChunk001Sub001Block069Part019

def surrogateDiagonalTailChunk001Sub001Block069TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub001Block069Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block069Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block069Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block069Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block069Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub001Block069Tail : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block069Part020
    + surrogateDiagTailX0RatChunk001Sub001Block069Part021
    + surrogateDiagTailX0RatChunk001Sub001Block069Part022
    + surrogateDiagTailX0RatChunk001Sub001Block069Part023
    + surrogateDiagTailX0RatChunk001Sub001Block069Part024

def surrogateDiagonalTailChunk001Sub001Block069Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk001Sub001Block069HeadSum X0
    + surrogateDiagonalTailChunk001Sub001Block069MidSum X0
    + surrogateDiagonalTailChunk001Sub001Block069TailSum X0

def surrogateDiagTailX0RatChunk001Sub001Block069 : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block069Part000
    + surrogateDiagTailX0RatChunk001Sub001Block069Part001
    + surrogateDiagTailX0RatChunk001Sub001Block069Part002
    + surrogateDiagTailX0RatChunk001Sub001Block069Part003
    + surrogateDiagTailX0RatChunk001Sub001Block069Part004
    + surrogateDiagTailX0RatChunk001Sub001Block069Part005
    + surrogateDiagTailX0RatChunk001Sub001Block069Part006
    + surrogateDiagTailX0RatChunk001Sub001Block069Part007
    + surrogateDiagTailX0RatChunk001Sub001Block069Part008
    + surrogateDiagTailX0RatChunk001Sub001Block069Part009
    + surrogateDiagTailX0RatChunk001Sub001Block069Part010
    + surrogateDiagTailX0RatChunk001Sub001Block069Part011
    + surrogateDiagTailX0RatChunk001Sub001Block069Part012
    + surrogateDiagTailX0RatChunk001Sub001Block069Part013
    + surrogateDiagTailX0RatChunk001Sub001Block069Part014
    + surrogateDiagTailX0RatChunk001Sub001Block069Part015
    + surrogateDiagTailX0RatChunk001Sub001Block069Part016
    + surrogateDiagTailX0RatChunk001Sub001Block069Part017
    + surrogateDiagTailX0RatChunk001Sub001Block069Part018
    + surrogateDiagTailX0RatChunk001Sub001Block069Part019
    + surrogateDiagTailX0RatChunk001Sub001Block069Part020
    + surrogateDiagTailX0RatChunk001Sub001Block069Part021
    + surrogateDiagTailX0RatChunk001Sub001Block069Part022
    + surrogateDiagTailX0RatChunk001Sub001Block069Part023
    + surrogateDiagTailX0RatChunk001Sub001Block069Part024

theorem surrogateDiagTailX0RatChunk001Sub001Block069_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk001Sub001Block069Head + surrogateDiagTailX0RatChunk001Sub001Block069Mid + surrogateDiagTailX0RatChunk001Sub001Block069Tail =
      surrogateDiagTailX0RatChunk001Sub001Block069 := by
  unfold surrogateDiagTailX0RatChunk001Sub001Block069Head surrogateDiagTailX0RatChunk001Sub001Block069Mid surrogateDiagTailX0RatChunk001Sub001Block069Tail surrogateDiagTailX0RatChunk001Sub001Block069
  ring

def SurrogateDiagonalTailChunk001Sub001Block069HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub001Block069HeadSum X0 = surrogateDiagTailX0RatChunk001Sub001Block069Head

def SurrogateDiagonalTailChunk001Sub001Block069MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub001Block069MidSum X0 = surrogateDiagTailX0RatChunk001Sub001Block069Mid

def SurrogateDiagonalTailChunk001Sub001Block069TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub001Block069TailSum X0 = surrogateDiagTailX0RatChunk001Sub001Block069Tail

theorem surrogateDiagonalTailChunk001Sub001Block069_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk001Sub001Block069HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk001Sub001Block069MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk001Sub001Block069TailCertificateAt X0) :
    surrogateDiagonalTailChunk001Sub001Block069Sum X0 = surrogateDiagTailX0RatChunk001Sub001Block069 := by
  unfold SurrogateDiagonalTailChunk001Sub001Block069HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk001Sub001Block069MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk001Sub001Block069TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk001Sub001Block069Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk001Sub001Block069_eq_head_add_mid_add_tail

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

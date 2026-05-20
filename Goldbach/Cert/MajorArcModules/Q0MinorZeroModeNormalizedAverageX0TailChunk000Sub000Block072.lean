import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0TailPilot25

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

open scoped BigOperators

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

/- Generated direct-term certificate blocks for tail chunk 000, subchunk 000, blocks [72,73). -/

/- Block 072 covers tail-support indices [1800,1825) and q from 3011 to 3053. -/

def TailChunk000Sub000Block072Part000SupportExplicit : Finset ℕ :=
  ([3011] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block072Part000 : ℚ :=
  (226653025 : ℚ) / 82101829092402

def SurrogateDiagonalTailChunk000Sub000Block072Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3011
    = surrogateDiagTailX0RatChunk000Sub000Block072Part000

theorem surrogateDiagonalTailChunk000Sub000Block072Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block072Part000CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block072Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block072Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block072Part000CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block072Part000SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block072Part000] using hcert

def TailChunk000Sub000Block072Part001SupportExplicit : Finset ℕ :=
  ([3013] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block072Part001 : ℚ :=
  (21349499261 : ℚ) / 3345961866561600

def SurrogateDiagonalTailChunk000Sub000Block072Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3013
    = surrogateDiagTailX0RatChunk000Sub000Block072Part001

theorem surrogateDiagonalTailChunk000Sub000Block072Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block072Part001CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block072Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block072Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block072Part001CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block072Part001SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block072Part001] using hcert

def TailChunk000Sub000Block072Part002SupportExplicit : Finset ℕ :=
  ([3014] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block072Part002 : ℚ :=
  (10074762839 : ℚ) / 171085218201600

def SurrogateDiagonalTailChunk000Sub000Block072Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3014
    = surrogateDiagTailX0RatChunk000Sub000Block072Part002

theorem surrogateDiagonalTailChunk000Sub000Block072Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block072Part002CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block072Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block072Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block072Part002CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block072Part002SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block072Part002] using hcert

def TailChunk000Sub000Block072Part003SupportExplicit : Finset ℕ :=
  ([3017] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block072Part003 : ℚ :=
  (4169298733 : ℚ) / 492405805468800

def SurrogateDiagonalTailChunk000Sub000Block072Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3017
    = surrogateDiagTailX0RatChunk000Sub000Block072Part003

theorem surrogateDiagonalTailChunk000Sub000Block072Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block072Part003CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block072Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block072Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block072Part003CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block072Part003SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block072Part003] using hcert

def TailChunk000Sub000Block072Part004SupportExplicit : Finset ℕ :=
  ([3018] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block072Part004 : ℚ :=
  (14206425 : ℚ) / 127012032032

def SurrogateDiagonalTailChunk000Sub000Block072Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3018
    = surrogateDiagTailX0RatChunk000Sub000Block072Part004

theorem surrogateDiagonalTailChunk000Sub000Block072Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block072Part004CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block072Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block072Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block072Part004CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block072Part004SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block072Part004] using hcert

def TailChunk000Sub000Block072Part005SupportExplicit : Finset ℕ :=
  ([3019] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block072Part005 : ℚ :=
  (1139067265975 : ℚ) / 207445396005484488

def SurrogateDiagonalTailChunk000Sub000Block072Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3019
    = surrogateDiagTailX0RatChunk000Sub000Block072Part005

theorem surrogateDiagonalTailChunk000Sub000Block072Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block072Part005CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block072Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block072Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block072Part005CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block072Part005SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block072Part005] using hcert

def TailChunk000Sub000Block072Part006SupportExplicit : Finset ℕ :=
  ([3021] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block072Part006 : ℚ :=
  (643883762875 : ℚ) / 30707908402249728

def SurrogateDiagonalTailChunk000Sub000Block072Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3021
    = surrogateDiagTailX0RatChunk000Sub000Block072Part006

theorem surrogateDiagonalTailChunk000Sub000Block072Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block072Part006CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block072Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block072Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block072Part006CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block072Part006SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block072Part006] using hcert

def TailChunk000Sub000Block072Part007SupportExplicit : Finset ℕ :=
  ([3022] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block072Part007 : ℚ :=
  (11408755637 : ℚ) / 259994789060100

def SurrogateDiagonalTailChunk000Sub000Block072Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3022
    = surrogateDiagTailX0RatChunk000Sub000Block072Part007

theorem surrogateDiagonalTailChunk000Sub000Block072Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block072Part007CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block072Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block072Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block072Part007CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block072Part007SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block072Part007] using hcert

def TailChunk000Sub000Block072Part008SupportExplicit : Finset ℕ :=
  ([3023] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block072Part008 : ℚ :=
  (1142087661775 : ℚ) / 208547361157645128

def SurrogateDiagonalTailChunk000Sub000Block072Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3023
    = surrogateDiagTailX0RatChunk000Sub000Block072Part008

theorem surrogateDiagonalTailChunk000Sub000Block072Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block072Part008CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block072Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block072Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block072Part008CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block072Part008SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block072Part008] using hcert

def TailChunk000Sub000Block072Part009SupportExplicit : Finset ℕ :=
  ([3026] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block072Part009 : ℚ :=
  (67145307825 : ℚ) / 1637895643332608

def SurrogateDiagonalTailChunk000Sub000Block072Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3026
    = surrogateDiagTailX0RatChunk000Sub000Block072Part009

theorem surrogateDiagonalTailChunk000Sub000Block072Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block072Part009CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block072Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block072Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block072Part009CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block072Part009SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block072Part009] using hcert

def TailChunk000Sub000Block072Part010SupportExplicit : Finset ℕ :=
  ([3027] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block072Part010 : ℚ :=
  (508707452275 : ℚ) / 41303701172256768

def SurrogateDiagonalTailChunk000Sub000Block072Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3027
    = surrogateDiagTailX0RatChunk000Sub000Block072Part010

theorem surrogateDiagonalTailChunk000Sub000Block072Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block072Part010CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block072Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block072Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block072Part010CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block072Part010SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block072Part010] using hcert

def TailChunk000Sub000Block072Part011SupportExplicit : Finset ℕ :=
  ([3029] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block072Part011 : ℚ :=
  (558859770625 : ℚ) / 150211707410055168

def SurrogateDiagonalTailChunk000Sub000Block072Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3029
    = surrogateDiagTailX0RatChunk000Sub000Block072Part011

theorem surrogateDiagonalTailChunk000Sub000Block072Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block072Part011CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block072Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block072Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block072Part011CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block072Part011SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block072Part011] using hcert

def TailChunk000Sub000Block072Part012SupportExplicit : Finset ℕ :=
  ([3030] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block072Part012 : ℚ :=
  (1935187877 : ℚ) / 8193638400000

def SurrogateDiagonalTailChunk000Sub000Block072Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3030
    = surrogateDiagTailX0RatChunk000Sub000Block072Part012

theorem surrogateDiagonalTailChunk000Sub000Block072Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block072Part012CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block072Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block072Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block072Part012CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block072Part012SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block072Part012] using hcert

def TailChunk000Sub000Block072Part013SupportExplicit : Finset ℕ :=
  ([3031] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block072Part013 : ℚ :=
  (479249768225 : ℚ) / 56433482588749824

def SurrogateDiagonalTailChunk000Sub000Block072Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3031
    = surrogateDiagTailX0RatChunk000Sub000Block072Part013

theorem surrogateDiagonalTailChunk000Sub000Block072Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block072Part013CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block072Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block072Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block072Part013CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block072Part013SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block072Part013] using hcert

def TailChunk000Sub000Block072Part014SupportExplicit : Finset ℕ :=
  ([3034] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block072Part014 : ℚ :=
  (16470741997 : ℚ) / 430067692339200

def SurrogateDiagonalTailChunk000Sub000Block072Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3034
    = surrogateDiagTailX0RatChunk000Sub000Block072Part014

theorem surrogateDiagonalTailChunk000Sub000Block072Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block072Part014CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block072Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block072Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block072Part014CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block072Part014SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block072Part014] using hcert

def TailChunk000Sub000Block072Part015SupportExplicit : Finset ℕ :=
  ([3035] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block072Part015 : ℚ :=
  (873590510575 : ℚ) / 86329121377241088

def SurrogateDiagonalTailChunk000Sub000Block072Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3035
    = surrogateDiagTailX0RatChunk000Sub000Block072Part015

theorem surrogateDiagonalTailChunk000Sub000Block072Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block072Part015CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block072Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block072Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block072Part015CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block072Part015SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block072Part015] using hcert

def TailChunk000Sub000Block072Part016SupportExplicit : Finset ℕ :=
  ([3037] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block072Part016 : ℚ :=
  (1152690540775 : ℚ) / 212438843151815808

def SurrogateDiagonalTailChunk000Sub000Block072Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3037
    = surrogateDiagTailX0RatChunk000Sub000Block072Part016

theorem surrogateDiagonalTailChunk000Sub000Block072Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block072Part016CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block072Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block072Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block072Part016CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block072Part016SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block072Part016] using hcert

def TailChunk000Sub000Block072Part017SupportExplicit : Finset ℕ :=
  ([3039] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block072Part017 : ℚ :=
  (704851555075 : ℚ) / 41963228276901888

def SurrogateDiagonalTailChunk000Sub000Block072Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3039
    = surrogateDiagTailX0RatChunk000Sub000Block072Part017

theorem surrogateDiagonalTailChunk000Sub000Block072Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block072Part017CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block072Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block072Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block072Part017CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block072Part017SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block072Part017] using hcert

def TailChunk000Sub000Block072Part018SupportExplicit : Finset ℕ :=
  ([3041] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block072Part018 : ℚ :=
  (46229157319 : ℚ) / 8542425199411200

def SurrogateDiagonalTailChunk000Sub000Block072Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3041
    = surrogateDiagTailX0RatChunk000Sub000Block072Part018

theorem surrogateDiagonalTailChunk000Sub000Block072Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block072Part018CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block072Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block072Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block072Part018CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block072Part018SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block072Part018] using hcert

def TailChunk000Sub000Block072Part019SupportExplicit : Finset ℕ :=
  ([3043] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block072Part019 : ℚ :=
  (70682001725 : ℚ) / 20563489406386176

def SurrogateDiagonalTailChunk000Sub000Block072Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3043
    = surrogateDiagTailX0RatChunk000Sub000Block072Part019

theorem surrogateDiagonalTailChunk000Sub000Block072Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block072Part019CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block072Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block072Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block072Part019CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block072Part019SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block072Part019] using hcert

def TailChunk000Sub000Block072Part020SupportExplicit : Finset ℕ :=
  ([3045] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block072Part020 : ℚ :=
  (6829390625 : ℚ) / 151088070131712

def SurrogateDiagonalTailChunk000Sub000Block072Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3045
    = surrogateDiagTailX0RatChunk000Sub000Block072Part020

theorem surrogateDiagonalTailChunk000Sub000Block072Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block072Part020CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block072Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block072Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block072Part020CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block072Part020SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block072Part020] using hcert

def TailChunk000Sub000Block072Part021SupportExplicit : Finset ℕ :=
  ([3046] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block072Part021 : ℚ :=
  (144912574275 : ℚ) / 4472642784900376

def SurrogateDiagonalTailChunk000Sub000Block072Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3046
    = surrogateDiagTailX0RatChunk000Sub000Block072Part021

theorem surrogateDiagonalTailChunk000Sub000Block072Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block072Part021CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block072Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block072Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block072Part021CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block072Part021SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block072Part021] using hcert

def TailChunk000Sub000Block072Part022SupportExplicit : Finset ℕ :=
  ([3047] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block072Part022 : ℚ :=
  (121787479 : ℚ) / 31543171372800

def SurrogateDiagonalTailChunk000Sub000Block072Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3047
    = surrogateDiagTailX0RatChunk000Sub000Block072Part022

theorem surrogateDiagonalTailChunk000Sub000Block072Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block072Part022CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block072Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block072Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block072Part022CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block072Part022SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block072Part022] using hcert

def TailChunk000Sub000Block072Part023SupportExplicit : Finset ℕ :=
  ([3049] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block072Part023 : ℚ :=
  (1161817714975 : ℚ) / 215817525905246208

def SurrogateDiagonalTailChunk000Sub000Block072Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3049
    = surrogateDiagTailX0RatChunk000Sub000Block072Part023

theorem surrogateDiagonalTailChunk000Sub000Block072Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block072Part023CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block072Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block072Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block072Part023CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block072Part023SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block072Part023] using hcert

def TailChunk000Sub000Block072Part024SupportExplicit : Finset ℕ :=
  ([3053] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block072Part024 : ℚ :=
  (318417803 : ℚ) / 53376259517280

def SurrogateDiagonalTailChunk000Sub000Block072Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3053
    = surrogateDiagTailX0RatChunk000Sub000Block072Part024

theorem surrogateDiagonalTailChunk000Sub000Block072Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block072Part024CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block072Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block072Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block072Part024CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block072Part024SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block072Part024] using hcert

def surrogateDiagonalTailChunk000Sub000Block072HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block072Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block072Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block072Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block072Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block072Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block072Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block072Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block072Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block072Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block072Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block072Head : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block072Part000
    + surrogateDiagTailX0RatChunk000Sub000Block072Part001
    + surrogateDiagTailX0RatChunk000Sub000Block072Part002
    + surrogateDiagTailX0RatChunk000Sub000Block072Part003
    + surrogateDiagTailX0RatChunk000Sub000Block072Part004
    + surrogateDiagTailX0RatChunk000Sub000Block072Part005
    + surrogateDiagTailX0RatChunk000Sub000Block072Part006
    + surrogateDiagTailX0RatChunk000Sub000Block072Part007
    + surrogateDiagTailX0RatChunk000Sub000Block072Part008
    + surrogateDiagTailX0RatChunk000Sub000Block072Part009

def surrogateDiagonalTailChunk000Sub000Block072MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block072Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block072Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block072Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block072Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block072Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block072Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block072Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block072Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block072Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block072Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block072Mid : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block072Part010
    + surrogateDiagTailX0RatChunk000Sub000Block072Part011
    + surrogateDiagTailX0RatChunk000Sub000Block072Part012
    + surrogateDiagTailX0RatChunk000Sub000Block072Part013
    + surrogateDiagTailX0RatChunk000Sub000Block072Part014
    + surrogateDiagTailX0RatChunk000Sub000Block072Part015
    + surrogateDiagTailX0RatChunk000Sub000Block072Part016
    + surrogateDiagTailX0RatChunk000Sub000Block072Part017
    + surrogateDiagTailX0RatChunk000Sub000Block072Part018
    + surrogateDiagTailX0RatChunk000Sub000Block072Part019

def surrogateDiagonalTailChunk000Sub000Block072TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block072Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block072Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block072Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block072Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block072Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block072Tail : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block072Part020
    + surrogateDiagTailX0RatChunk000Sub000Block072Part021
    + surrogateDiagTailX0RatChunk000Sub000Block072Part022
    + surrogateDiagTailX0RatChunk000Sub000Block072Part023
    + surrogateDiagTailX0RatChunk000Sub000Block072Part024

def surrogateDiagonalTailChunk000Sub000Block072Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub000Block072HeadSum X0
    + surrogateDiagonalTailChunk000Sub000Block072MidSum X0
    + surrogateDiagonalTailChunk000Sub000Block072TailSum X0

def surrogateDiagTailX0RatChunk000Sub000Block072 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block072Part000
    + surrogateDiagTailX0RatChunk000Sub000Block072Part001
    + surrogateDiagTailX0RatChunk000Sub000Block072Part002
    + surrogateDiagTailX0RatChunk000Sub000Block072Part003
    + surrogateDiagTailX0RatChunk000Sub000Block072Part004
    + surrogateDiagTailX0RatChunk000Sub000Block072Part005
    + surrogateDiagTailX0RatChunk000Sub000Block072Part006
    + surrogateDiagTailX0RatChunk000Sub000Block072Part007
    + surrogateDiagTailX0RatChunk000Sub000Block072Part008
    + surrogateDiagTailX0RatChunk000Sub000Block072Part009
    + surrogateDiagTailX0RatChunk000Sub000Block072Part010
    + surrogateDiagTailX0RatChunk000Sub000Block072Part011
    + surrogateDiagTailX0RatChunk000Sub000Block072Part012
    + surrogateDiagTailX0RatChunk000Sub000Block072Part013
    + surrogateDiagTailX0RatChunk000Sub000Block072Part014
    + surrogateDiagTailX0RatChunk000Sub000Block072Part015
    + surrogateDiagTailX0RatChunk000Sub000Block072Part016
    + surrogateDiagTailX0RatChunk000Sub000Block072Part017
    + surrogateDiagTailX0RatChunk000Sub000Block072Part018
    + surrogateDiagTailX0RatChunk000Sub000Block072Part019
    + surrogateDiagTailX0RatChunk000Sub000Block072Part020
    + surrogateDiagTailX0RatChunk000Sub000Block072Part021
    + surrogateDiagTailX0RatChunk000Sub000Block072Part022
    + surrogateDiagTailX0RatChunk000Sub000Block072Part023
    + surrogateDiagTailX0RatChunk000Sub000Block072Part024

theorem surrogateDiagTailX0RatChunk000Sub000Block072_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk000Sub000Block072Head + surrogateDiagTailX0RatChunk000Sub000Block072Mid + surrogateDiagTailX0RatChunk000Sub000Block072Tail =
      surrogateDiagTailX0RatChunk000Sub000Block072 := by
  unfold surrogateDiagTailX0RatChunk000Sub000Block072Head surrogateDiagTailX0RatChunk000Sub000Block072Mid surrogateDiagTailX0RatChunk000Sub000Block072Tail surrogateDiagTailX0RatChunk000Sub000Block072
  ring

def SurrogateDiagonalTailChunk000Sub000Block072HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block072HeadSum X0 = surrogateDiagTailX0RatChunk000Sub000Block072Head

def SurrogateDiagonalTailChunk000Sub000Block072MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block072MidSum X0 = surrogateDiagTailX0RatChunk000Sub000Block072Mid

def SurrogateDiagonalTailChunk000Sub000Block072TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block072TailSum X0 = surrogateDiagTailX0RatChunk000Sub000Block072Tail

theorem surrogateDiagonalTailChunk000Sub000Block072_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk000Sub000Block072HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk000Sub000Block072MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk000Sub000Block072TailCertificateAt X0) :
    surrogateDiagonalTailChunk000Sub000Block072Sum X0 = surrogateDiagTailX0RatChunk000Sub000Block072 := by
  unfold SurrogateDiagonalTailChunk000Sub000Block072HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk000Sub000Block072MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk000Sub000Block072TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk000Sub000Block072Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk000Sub000Block072_eq_head_add_mid_add_tail

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

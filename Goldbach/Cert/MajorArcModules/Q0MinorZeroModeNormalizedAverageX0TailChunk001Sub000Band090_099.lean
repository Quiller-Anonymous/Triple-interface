import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0TailPilot25

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

open scoped BigOperators

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

/- Generated direct-term certificate blocks for tail chunk 001, subchunk 000, blocks [90,100). -/

/-- Block 090 covers tail-support indices [12250,12275) and q from 20199 to 20242. -/

def TailChunk001Sub000Block090Part000SupportExplicit : Finset ℕ :=
  ([20199] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block090Part000 : ℚ :=
  (93641159725 : ℚ) / 679106520555522048

def SurrogateDiagonalTailChunk001Sub000Block090Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20199
    = surrogateDiagTailX0RatChunk001Sub000Block090Part000

theorem surrogateDiagonalTailChunk001Sub000Block090Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block090Part000CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block090Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block090Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block090Part000CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block090Part000SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block090Part000] using hcert

def TailChunk001Sub000Block090Part001SupportExplicit : Finset ℕ :=
  ([20201] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block090Part001 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block090Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20201
    = surrogateDiagTailX0RatChunk001Sub000Block090Part001

theorem surrogateDiagonalTailChunk001Sub000Block090Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block090Part001CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block090Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block090Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block090Part001CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block090Part001SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block090Part001] using hcert

def TailChunk001Sub000Block090Part002SupportExplicit : Finset ℕ :=
  ([20202] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block090Part002 : ℚ :=
  (796462996975 : ℚ) / 1805871442839994368

def SurrogateDiagonalTailChunk001Sub000Block090Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20202
    = surrogateDiagTailX0RatChunk001Sub000Block090Part002

theorem surrogateDiagonalTailChunk001Sub000Block090Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block090Part002CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block090Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block090Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block090Part002CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block090Part002SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block090Part002] using hcert

def TailChunk001Sub000Block090Part003SupportExplicit : Finset ℕ :=
  ([20203] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block090Part003 : ℚ :=
  (97823945575 : ℚ) / 391193206404461395968

def SurrogateDiagonalTailChunk001Sub000Block090Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20203
    = surrogateDiagTailX0RatChunk001Sub000Block090Part003

theorem surrogateDiagonalTailChunk001Sub000Block090Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block090Part003CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block090Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block090Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block090Part003CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block090Part003SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block090Part003] using hcert

def TailChunk001Sub000Block090Part004SupportExplicit : Finset ℕ :=
  ([20206] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block090Part004 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block090Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20206
    = surrogateDiagTailX0RatChunk001Sub000Block090Part004

theorem surrogateDiagonalTailChunk001Sub000Block090Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block090Part004CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block090Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block090Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block090Part004CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block090Part004SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block090Part004] using hcert

def TailChunk001Sub000Block090Part005SupportExplicit : Finset ℕ :=
  ([20209] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block090Part005 : ℚ :=
  (40187472625 : ℚ) / 17293138317027870336

def SurrogateDiagonalTailChunk001Sub000Block090Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20209
    = surrogateDiagTailX0RatChunk001Sub000Block090Part005

theorem surrogateDiagonalTailChunk001Sub000Block090Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block090Part005CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block090Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block090Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block090Part005CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block090Part005SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block090Part005] using hcert

def TailChunk001Sub000Block090Part006SupportExplicit : Finset ℕ :=
  ([20210] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block090Part006 : ℚ :=
  (573825855025 : ℚ) / 8918571789927088128

def SurrogateDiagonalTailChunk001Sub000Block090Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20210
    = surrogateDiagTailX0RatChunk001Sub000Block090Part006

theorem surrogateDiagonalTailChunk001Sub000Block090Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block090Part006CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block090Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block090Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block090Part006CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block090Part006SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block090Part006] using hcert

def TailChunk001Sub000Block090Part007SupportExplicit : Finset ℕ :=
  ([20211] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block090Part007 : ℚ :=
  (125025 : ℚ) / 16470178309603328

def SurrogateDiagonalTailChunk001Sub000Block090Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20211
    = surrogateDiagTailX0RatChunk001Sub000Block090Part007

theorem surrogateDiagonalTailChunk001Sub000Block090Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block090Part007CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block090Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block090Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block090Part007CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block090Part007SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block090Part007] using hcert

def TailChunk001Sub000Block090Part008SupportExplicit : Finset ℕ :=
  ([20213] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block090Part008 : ℚ :=
  (8555433429 : ℚ) / 3438092973663846400

def SurrogateDiagonalTailChunk001Sub000Block090Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20213
    = surrogateDiagTailX0RatChunk001Sub000Block090Part008

theorem surrogateDiagonalTailChunk001Sub000Block090Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block090Part008CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block090Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block090Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block090Part008CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block090Part008SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block090Part008] using hcert

def TailChunk001Sub000Block090Part009SupportExplicit : Finset ℕ :=
  ([20215] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block090Part009 : ℚ :=
  (6201756653 : ℚ) / 612926767433318400

def SurrogateDiagonalTailChunk001Sub000Block090Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20215
    = surrogateDiagTailX0RatChunk001Sub000Block090Part009

theorem surrogateDiagonalTailChunk001Sub000Block090Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block090Part009CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block090Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block090Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block090Part009CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block090Part009SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block090Part009] using hcert

def TailChunk001Sub000Block090Part010SupportExplicit : Finset ℕ :=
  ([20217] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block090Part010 : ℚ :=
  (66749418525 : ℚ) / 22711599224711643136

def SurrogateDiagonalTailChunk001Sub000Block090Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20217
    = surrogateDiagTailX0RatChunk001Sub000Block090Part010

theorem surrogateDiagonalTailChunk001Sub000Block090Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block090Part010CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block090Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block090Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block090Part010CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block090Part010SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block090Part010] using hcert

def TailChunk001Sub000Block090Part011SupportExplicit : Finset ℕ :=
  ([20218] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block090Part011 : ℚ :=
  (20883743 : ℚ) / 1392795641027520

def SurrogateDiagonalTailChunk001Sub000Block090Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20218
    = surrogateDiagTailX0RatChunk001Sub000Block090Part011

theorem surrogateDiagonalTailChunk001Sub000Block090Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block090Part011CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block090Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block090Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block090Part011CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block090Part011SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block090Part011] using hcert

def TailChunk001Sub000Block090Part012SupportExplicit : Finset ℕ :=
  ([20219] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block090Part012 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block090Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20219
    = surrogateDiagTailX0RatChunk001Sub000Block090Part012

theorem surrogateDiagonalTailChunk001Sub000Block090Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block090Part012CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block090Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block090Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block090Part012CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block090Part012SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block090Part012] using hcert

def TailChunk001Sub000Block090Part013SupportExplicit : Finset ℕ :=
  ([20221] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block090Part013 : ℚ :=
  (107752637425 : ℚ) / 389935856817736777728

def SurrogateDiagonalTailChunk001Sub000Block090Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20221
    = surrogateDiagTailX0RatChunk001Sub000Block090Part013

theorem surrogateDiagonalTailChunk001Sub000Block090Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block090Part013CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block090Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block090Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block090Part013CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block090Part013SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block090Part013] using hcert

def TailChunk001Sub000Block090Part014SupportExplicit : Finset ℕ :=
  ([20222] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block090Part014 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block090Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20222
    = surrogateDiagTailX0RatChunk001Sub000Block090Part014

theorem surrogateDiagonalTailChunk001Sub000Block090Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block090Part014CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block090Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block090Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block090Part014CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block090Part014SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block090Part014] using hcert

def TailChunk001Sub000Block090Part015SupportExplicit : Finset ℕ :=
  ([20226] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block090Part015 : ℚ :=
  (2841725413 : ℚ) / 20640795751283520

def SurrogateDiagonalTailChunk001Sub000Block090Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20226
    = surrogateDiagTailX0RatChunk001Sub000Block090Part015

theorem surrogateDiagonalTailChunk001Sub000Block090Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block090Part015CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block090Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block090Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block090Part015CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block090Part015SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block090Part015] using hcert

def TailChunk001Sub000Block090Part016SupportExplicit : Finset ℕ :=
  ([20227] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block090Part016 : ℚ :=
  (1620153425 : ℚ) / 7053276866390458368

def SurrogateDiagonalTailChunk001Sub000Block090Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20227
    = surrogateDiagTailX0RatChunk001Sub000Block090Part016

theorem surrogateDiagonalTailChunk001Sub000Block090Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block090Part016CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block090Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block090Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block090Part016CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block090Part016SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block090Part016] using hcert

def TailChunk001Sub000Block090Part017SupportExplicit : Finset ℕ :=
  ([20229] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block090Part017 : ℚ :=
  (5390531341 : ℚ) / 748326744413798400

def SurrogateDiagonalTailChunk001Sub000Block090Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20229
    = surrogateDiagTailX0RatChunk001Sub000Block090Part017

theorem surrogateDiagonalTailChunk001Sub000Block090Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block090Part017CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block090Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block090Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block090Part017CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block090Part017SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block090Part017] using hcert

def TailChunk001Sub000Block090Part018SupportExplicit : Finset ℕ :=
  ([20231] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block090Part018 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block090Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20231
    = surrogateDiagTailX0RatChunk001Sub000Block090Part018

theorem surrogateDiagonalTailChunk001Sub000Block090Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block090Part018CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block090Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block090Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block090Part018CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block090Part018SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block090Part018] using hcert

def TailChunk001Sub000Block090Part019SupportExplicit : Finset ℕ :=
  ([20233] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block090Part019 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block090Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20233
    = surrogateDiagTailX0RatChunk001Sub000Block090Part019

theorem surrogateDiagonalTailChunk001Sub000Block090Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block090Part019CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block090Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block090Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block090Part019CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block090Part019SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block090Part019] using hcert

def TailChunk001Sub000Block090Part020SupportExplicit : Finset ℕ :=
  ([20234] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block090Part020 : ℚ :=
  (49504343 : ℚ) / 17792372763000000

def SurrogateDiagonalTailChunk001Sub000Block090Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20234
    = surrogateDiagTailX0RatChunk001Sub000Block090Part020

theorem surrogateDiagonalTailChunk001Sub000Block090Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block090Part020CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block090Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block090Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block090Part020CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block090Part020SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block090Part020] using hcert

def TailChunk001Sub000Block090Part021SupportExplicit : Finset ℕ :=
  ([20235] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block090Part021 : ℚ :=
  (36501579097 : ℚ) / 1032592529306419200

def SurrogateDiagonalTailChunk001Sub000Block090Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20235
    = surrogateDiagTailX0RatChunk001Sub000Block090Part021

theorem surrogateDiagonalTailChunk001Sub000Block090Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block090Part021CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block090Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block090Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block090Part021CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block090Part021SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block090Part021] using hcert

def TailChunk001Sub000Block090Part022SupportExplicit : Finset ℕ :=
  ([20238] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block090Part022 : ℚ :=
  (22227315725 : ℚ) / 161639361792396864

def SurrogateDiagonalTailChunk001Sub000Block090Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20238
    = surrogateDiagTailX0RatChunk001Sub000Block090Part022

theorem surrogateDiagonalTailChunk001Sub000Block090Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block090Part022CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block090Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block090Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block090Part022CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block090Part022SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block090Part022] using hcert

def TailChunk001Sub000Block090Part023SupportExplicit : Finset ℕ :=
  ([20239] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block090Part023 : ℚ :=
  (254504825 : ℚ) / 531704481301453824

def SurrogateDiagonalTailChunk001Sub000Block090Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20239
    = surrogateDiagTailX0RatChunk001Sub000Block090Part023

theorem surrogateDiagonalTailChunk001Sub000Block090Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block090Part023CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block090Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block090Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block090Part023CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block090Part023SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block090Part023] using hcert

def TailChunk001Sub000Block090Part024SupportExplicit : Finset ℕ :=
  ([20242] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block090Part024 : ℚ :=
  (114421049875 : ℚ) / 22541144343221403648

def SurrogateDiagonalTailChunk001Sub000Block090Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20242
    = surrogateDiagTailX0RatChunk001Sub000Block090Part024

theorem surrogateDiagonalTailChunk001Sub000Block090Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block090Part024CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block090Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block090Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block090Part024CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block090Part024SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block090Part024] using hcert

def surrogateDiagonalTailChunk001Sub000Block090HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block090Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block090Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block090Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block090Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block090Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block090Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block090Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block090Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block090Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block090Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block090Head : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block090Part000
    + surrogateDiagTailX0RatChunk001Sub000Block090Part001
    + surrogateDiagTailX0RatChunk001Sub000Block090Part002
    + surrogateDiagTailX0RatChunk001Sub000Block090Part003
    + surrogateDiagTailX0RatChunk001Sub000Block090Part004
    + surrogateDiagTailX0RatChunk001Sub000Block090Part005
    + surrogateDiagTailX0RatChunk001Sub000Block090Part006
    + surrogateDiagTailX0RatChunk001Sub000Block090Part007
    + surrogateDiagTailX0RatChunk001Sub000Block090Part008
    + surrogateDiagTailX0RatChunk001Sub000Block090Part009

def surrogateDiagonalTailChunk001Sub000Block090MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block090Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block090Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block090Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block090Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block090Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block090Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block090Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block090Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block090Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block090Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block090Mid : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block090Part010
    + surrogateDiagTailX0RatChunk001Sub000Block090Part011
    + surrogateDiagTailX0RatChunk001Sub000Block090Part012
    + surrogateDiagTailX0RatChunk001Sub000Block090Part013
    + surrogateDiagTailX0RatChunk001Sub000Block090Part014
    + surrogateDiagTailX0RatChunk001Sub000Block090Part015
    + surrogateDiagTailX0RatChunk001Sub000Block090Part016
    + surrogateDiagTailX0RatChunk001Sub000Block090Part017
    + surrogateDiagTailX0RatChunk001Sub000Block090Part018
    + surrogateDiagTailX0RatChunk001Sub000Block090Part019

def surrogateDiagonalTailChunk001Sub000Block090TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block090Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block090Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block090Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block090Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block090Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block090Tail : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block090Part020
    + surrogateDiagTailX0RatChunk001Sub000Block090Part021
    + surrogateDiagTailX0RatChunk001Sub000Block090Part022
    + surrogateDiagTailX0RatChunk001Sub000Block090Part023
    + surrogateDiagTailX0RatChunk001Sub000Block090Part024

def surrogateDiagonalTailChunk001Sub000Block090Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk001Sub000Block090HeadSum X0
    + surrogateDiagonalTailChunk001Sub000Block090MidSum X0
    + surrogateDiagonalTailChunk001Sub000Block090TailSum X0

def surrogateDiagTailX0RatChunk001Sub000Block090 : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block090Part000
    + surrogateDiagTailX0RatChunk001Sub000Block090Part001
    + surrogateDiagTailX0RatChunk001Sub000Block090Part002
    + surrogateDiagTailX0RatChunk001Sub000Block090Part003
    + surrogateDiagTailX0RatChunk001Sub000Block090Part004
    + surrogateDiagTailX0RatChunk001Sub000Block090Part005
    + surrogateDiagTailX0RatChunk001Sub000Block090Part006
    + surrogateDiagTailX0RatChunk001Sub000Block090Part007
    + surrogateDiagTailX0RatChunk001Sub000Block090Part008
    + surrogateDiagTailX0RatChunk001Sub000Block090Part009
    + surrogateDiagTailX0RatChunk001Sub000Block090Part010
    + surrogateDiagTailX0RatChunk001Sub000Block090Part011
    + surrogateDiagTailX0RatChunk001Sub000Block090Part012
    + surrogateDiagTailX0RatChunk001Sub000Block090Part013
    + surrogateDiagTailX0RatChunk001Sub000Block090Part014
    + surrogateDiagTailX0RatChunk001Sub000Block090Part015
    + surrogateDiagTailX0RatChunk001Sub000Block090Part016
    + surrogateDiagTailX0RatChunk001Sub000Block090Part017
    + surrogateDiagTailX0RatChunk001Sub000Block090Part018
    + surrogateDiagTailX0RatChunk001Sub000Block090Part019
    + surrogateDiagTailX0RatChunk001Sub000Block090Part020
    + surrogateDiagTailX0RatChunk001Sub000Block090Part021
    + surrogateDiagTailX0RatChunk001Sub000Block090Part022
    + surrogateDiagTailX0RatChunk001Sub000Block090Part023
    + surrogateDiagTailX0RatChunk001Sub000Block090Part024

theorem surrogateDiagTailX0RatChunk001Sub000Block090_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk001Sub000Block090Head + surrogateDiagTailX0RatChunk001Sub000Block090Mid + surrogateDiagTailX0RatChunk001Sub000Block090Tail =
      surrogateDiagTailX0RatChunk001Sub000Block090 := by
  unfold surrogateDiagTailX0RatChunk001Sub000Block090Head surrogateDiagTailX0RatChunk001Sub000Block090Mid surrogateDiagTailX0RatChunk001Sub000Block090Tail surrogateDiagTailX0RatChunk001Sub000Block090
  ring

def SurrogateDiagonalTailChunk001Sub000Block090HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block090HeadSum X0 = surrogateDiagTailX0RatChunk001Sub000Block090Head

def SurrogateDiagonalTailChunk001Sub000Block090MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block090MidSum X0 = surrogateDiagTailX0RatChunk001Sub000Block090Mid

def SurrogateDiagonalTailChunk001Sub000Block090TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block090TailSum X0 = surrogateDiagTailX0RatChunk001Sub000Block090Tail

theorem surrogateDiagonalTailChunk001Sub000Block090_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk001Sub000Block090HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk001Sub000Block090MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk001Sub000Block090TailCertificateAt X0) :
    surrogateDiagonalTailChunk001Sub000Block090Sum X0 = surrogateDiagTailX0RatChunk001Sub000Block090 := by
  unfold SurrogateDiagonalTailChunk001Sub000Block090HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk001Sub000Block090MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk001Sub000Block090TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk001Sub000Block090Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk001Sub000Block090_eq_head_add_mid_add_tail

/-- Block 091 covers tail-support indices [12275,12300) and q from 20243 to 20281. -/

def TailChunk001Sub000Block091Part000SupportExplicit : Finset ℕ :=
  ([20243] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block091Part000 : ℚ :=
  (5771219 : ℚ) / 9531714735254700

def SurrogateDiagonalTailChunk001Sub000Block091Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20243
    = surrogateDiagTailX0RatChunk001Sub000Block091Part000

theorem surrogateDiagonalTailChunk001Sub000Block091Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block091Part000CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block091Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block091Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block091Part000CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block091Part000SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block091Part000] using hcert

def TailChunk001Sub000Block091Part001SupportExplicit : Finset ℕ :=
  ([20245] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block091Part001 : ℚ :=
  (341798227125 : ℚ) / 57293794340730044416

def SurrogateDiagonalTailChunk001Sub000Block091Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20245
    = surrogateDiagTailX0RatChunk001Sub000Block091Part001

theorem surrogateDiagonalTailChunk001Sub000Block091Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block091Part001CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block091Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block091Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block091Part001CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block091Part001SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block091Part001] using hcert

def TailChunk001Sub000Block091Part002SupportExplicit : Finset ℕ :=
  ([20246] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block091Part002 : ℚ :=
  (149450009 : ℚ) / 47652384007887360

def SurrogateDiagonalTailChunk001Sub000Block091Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20246
    = surrogateDiagTailX0RatChunk001Sub000Block091Part002

theorem surrogateDiagonalTailChunk001Sub000Block091Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block091Part002CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block091Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block091Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block091Part002CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block091Part002SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block091Part002] using hcert

def TailChunk001Sub000Block091Part003SupportExplicit : Finset ℕ :=
  ([20247] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block091Part003 : ℚ :=
  (284471629075 : ℚ) / 64477399895431446528

def SurrogateDiagonalTailChunk001Sub000Block091Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20247
    = surrogateDiagTailX0RatChunk001Sub000Block091Part003

theorem surrogateDiagonalTailChunk001Sub000Block091Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block091Part003CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block091Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block091Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block091Part003CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block091Part003SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block091Part003] using hcert

def TailChunk001Sub000Block091Part004SupportExplicit : Finset ℕ :=
  ([20249] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block091Part004 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block091Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20249
    = surrogateDiagTailX0RatChunk001Sub000Block091Part004

theorem surrogateDiagonalTailChunk001Sub000Block091Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block091Part004CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block091Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block091Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block091Part004CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block091Part004SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block091Part004] using hcert

def TailChunk001Sub000Block091Part005SupportExplicit : Finset ℕ :=
  ([20251] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block091Part005 : ℚ :=
  (6222169949 : ℚ) / 678663523547596800

def SurrogateDiagonalTailChunk001Sub000Block091Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20251
    = surrogateDiagTailX0RatChunk001Sub000Block091Part005

theorem surrogateDiagonalTailChunk001Sub000Block091Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block091Part005CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block091Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block091Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block091Part005CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block091Part005SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block091Part005] using hcert

def TailChunk001Sub000Block091Part006SupportExplicit : Finset ℕ :=
  ([20253] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block091Part006 : ℚ :=
  (125294683375 : ℚ) / 73729688073801596928

def SurrogateDiagonalTailChunk001Sub000Block091Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20253
    = surrogateDiagTailX0RatChunk001Sub000Block091Part006

theorem surrogateDiagonalTailChunk001Sub000Block091Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block091Part006CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block091Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block091Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block091Part006CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block091Part006SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block091Part006] using hcert

def TailChunk001Sub000Block091Part007SupportExplicit : Finset ℕ :=
  ([20254] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block091Part007 : ℚ :=
  (5777601191 : ℚ) / 185789243090534400

def SurrogateDiagonalTailChunk001Sub000Block091Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20254
    = surrogateDiagTailX0RatChunk001Sub000Block091Part007

theorem surrogateDiagonalTailChunk001Sub000Block091Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block091Part007CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block091Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block091Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block091Part007CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block091Part007SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block091Part007] using hcert

def TailChunk001Sub000Block091Part008SupportExplicit : Finset ℕ :=
  ([20255] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block091Part008 : ℚ :=
  (8211255449 : ℚ) / 1377770571014400000

def SurrogateDiagonalTailChunk001Sub000Block091Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20255
    = surrogateDiagTailX0RatChunk001Sub000Block091Part008

theorem surrogateDiagonalTailChunk001Sub000Block091Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block091Part008CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block091Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block091Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block091Part008CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block091Part008SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block091Part008] using hcert

def TailChunk001Sub000Block091Part009SupportExplicit : Finset ℕ :=
  ([20257] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block091Part009 : ℚ :=
  (941280483 : ℚ) / 2551765426077675200

def SurrogateDiagonalTailChunk001Sub000Block091Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20257
    = surrogateDiagTailX0RatChunk001Sub000Block091Part009

theorem surrogateDiagonalTailChunk001Sub000Block091Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block091Part009CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block091Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block091Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block091Part009CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block091Part009SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block091Part009] using hcert

def TailChunk001Sub000Block091Part010SupportExplicit : Finset ℕ :=
  ([20258] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block091Part010 : ℚ :=
  (7291936225 : ℚ) / 262368246299988672

def SurrogateDiagonalTailChunk001Sub000Block091Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20258
    = surrogateDiagTailX0RatChunk001Sub000Block091Part010

theorem surrogateDiagonalTailChunk001Sub000Block091Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block091Part010CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block091Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block091Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block091Part010CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block091Part010SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block091Part010] using hcert

def TailChunk001Sub000Block091Part011SupportExplicit : Finset ℕ :=
  ([20261] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block091Part011 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block091Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20261
    = surrogateDiagTailX0RatChunk001Sub000Block091Part011

theorem surrogateDiagonalTailChunk001Sub000Block091Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block091Part011CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block091Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block091Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block091Part011CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block091Part011SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block091Part011] using hcert

def TailChunk001Sub000Block091Part012SupportExplicit : Finset ℕ :=
  ([20262] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block091Part012 : ℚ :=
  (10460794607 : ℚ) / 46770421525862400

def SurrogateDiagonalTailChunk001Sub000Block091Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20262
    = surrogateDiagTailX0RatChunk001Sub000Block091Part012

theorem surrogateDiagonalTailChunk001Sub000Block091Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block091Part012CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block091Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block091Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block091Part012CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block091Part012SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block091Part012] using hcert

def TailChunk001Sub000Block091Part013SupportExplicit : Finset ℕ :=
  ([20263] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block091Part013 : ℚ :=
  (2375795003 : ℚ) / 2810206653988208640

def SurrogateDiagonalTailChunk001Sub000Block091Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20263
    = surrogateDiagTailX0RatChunk001Sub000Block091Part013

theorem surrogateDiagonalTailChunk001Sub000Block091Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block091Part013CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block091Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block091Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block091Part013CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block091Part013SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block091Part013] using hcert

def TailChunk001Sub000Block091Part014SupportExplicit : Finset ℕ :=
  ([20265] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block091Part014 : ℚ :=
  (500659097075 : ℚ) / 9019173211245379584

def SurrogateDiagonalTailChunk001Sub000Block091Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20265
    = surrogateDiagTailX0RatChunk001Sub000Block091Part014

theorem surrogateDiagonalTailChunk001Sub000Block091Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block091Part014CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block091Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block091Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block091Part014CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block091Part014SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block091Part014] using hcert

def TailChunk001Sub000Block091Part015SupportExplicit : Finset ℕ :=
  ([20266] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block091Part015 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block091Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20266
    = surrogateDiagTailX0RatChunk001Sub000Block091Part015

theorem surrogateDiagonalTailChunk001Sub000Block091Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block091Part015CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block091Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block091Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block091Part015CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block091Part015SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block091Part015] using hcert

def TailChunk001Sub000Block091Part016SupportExplicit : Finset ℕ :=
  ([20267] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block091Part016 : ℚ :=
  (114675485575 : ℚ) / 76376836323710341632

def SurrogateDiagonalTailChunk001Sub000Block091Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20267
    = surrogateDiagTailX0RatChunk001Sub000Block091Part016

theorem surrogateDiagonalTailChunk001Sub000Block091Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block091Part016CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block091Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block091Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block091Part016CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block091Part016SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block091Part016] using hcert

def TailChunk001Sub000Block091Part017SupportExplicit : Finset ℕ :=
  ([20269] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block091Part017 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block091Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20269
    = surrogateDiagTailX0RatChunk001Sub000Block091Part017

theorem surrogateDiagonalTailChunk001Sub000Block091Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block091Part017CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block091Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block091Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block091Part017CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block091Part017SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block091Part017] using hcert

def TailChunk001Sub000Block091Part018SupportExplicit : Finset ℕ :=
  ([20270] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block091Part018 : ℚ :=
  (192642224425 : ℚ) / 2696277558078239232

def SurrogateDiagonalTailChunk001Sub000Block091Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20270
    = surrogateDiagTailX0RatChunk001Sub000Block091Part018

theorem surrogateDiagonalTailChunk001Sub000Block091Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block091Part018CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block091Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block091Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block091Part018CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block091Part018SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block091Part018] using hcert

def TailChunk001Sub000Block091Part019SupportExplicit : Finset ℕ :=
  ([20271] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block091Part019 : ℚ :=
  (233004579525 : ℚ) / 5936762296157077504

def SurrogateDiagonalTailChunk001Sub000Block091Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20271
    = surrogateDiagTailX0RatChunk001Sub000Block091Part019

theorem surrogateDiagonalTailChunk001Sub000Block091Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block091Part019CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block091Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block091Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block091Part019CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block091Part019SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block091Part019] using hcert

def TailChunk001Sub000Block091Part020SupportExplicit : Finset ℕ :=
  ([20273] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block091Part020 : ℚ :=
  (4130152231 : ℚ) / 990875963149516800

def SurrogateDiagonalTailChunk001Sub000Block091Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20273
    = surrogateDiagTailX0RatChunk001Sub000Block091Part020

theorem surrogateDiagonalTailChunk001Sub000Block091Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block091Part020CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block091Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block091Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block091Part020CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block091Part020SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block091Part020] using hcert

def TailChunk001Sub000Block091Part021SupportExplicit : Finset ℕ :=
  ([20274] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block091Part021 : ℚ :=
  (55818319693 : ℚ) / 176354633089843200

def SurrogateDiagonalTailChunk001Sub000Block091Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20274
    = surrogateDiagTailX0RatChunk001Sub000Block091Part021

theorem surrogateDiagonalTailChunk001Sub000Block091Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block091Part021CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block091Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block091Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block091Part021CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block091Part021SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block091Part021] using hcert

def TailChunk001Sub000Block091Part022SupportExplicit : Finset ℕ :=
  ([20278] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block091Part022 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block091Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20278
    = surrogateDiagTailX0RatChunk001Sub000Block091Part022

theorem surrogateDiagonalTailChunk001Sub000Block091Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block091Part022CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block091Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block091Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block091Part022CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block091Part022SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block091Part022] using hcert

def TailChunk001Sub000Block091Part023SupportExplicit : Finset ℕ :=
  ([20279] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block091Part023 : ℚ :=
  (525008580875 : ℚ) / 113971455574094905344

def SurrogateDiagonalTailChunk001Sub000Block091Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20279
    = surrogateDiagTailX0RatChunk001Sub000Block091Part023

theorem surrogateDiagonalTailChunk001Sub000Block091Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block091Part023CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block091Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block091Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block091Part023CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block091Part023SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block091Part023] using hcert

def TailChunk001Sub000Block091Part024SupportExplicit : Finset ℕ :=
  ([20281] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block091Part024 : ℚ :=
  (360001688275 : ℚ) / 330835276168773500928

def SurrogateDiagonalTailChunk001Sub000Block091Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20281
    = surrogateDiagTailX0RatChunk001Sub000Block091Part024

theorem surrogateDiagonalTailChunk001Sub000Block091Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block091Part024CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block091Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block091Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block091Part024CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block091Part024SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block091Part024] using hcert

def surrogateDiagonalTailChunk001Sub000Block091HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block091Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block091Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block091Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block091Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block091Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block091Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block091Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block091Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block091Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block091Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block091Head : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block091Part000
    + surrogateDiagTailX0RatChunk001Sub000Block091Part001
    + surrogateDiagTailX0RatChunk001Sub000Block091Part002
    + surrogateDiagTailX0RatChunk001Sub000Block091Part003
    + surrogateDiagTailX0RatChunk001Sub000Block091Part004
    + surrogateDiagTailX0RatChunk001Sub000Block091Part005
    + surrogateDiagTailX0RatChunk001Sub000Block091Part006
    + surrogateDiagTailX0RatChunk001Sub000Block091Part007
    + surrogateDiagTailX0RatChunk001Sub000Block091Part008
    + surrogateDiagTailX0RatChunk001Sub000Block091Part009

def surrogateDiagonalTailChunk001Sub000Block091MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block091Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block091Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block091Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block091Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block091Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block091Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block091Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block091Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block091Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block091Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block091Mid : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block091Part010
    + surrogateDiagTailX0RatChunk001Sub000Block091Part011
    + surrogateDiagTailX0RatChunk001Sub000Block091Part012
    + surrogateDiagTailX0RatChunk001Sub000Block091Part013
    + surrogateDiagTailX0RatChunk001Sub000Block091Part014
    + surrogateDiagTailX0RatChunk001Sub000Block091Part015
    + surrogateDiagTailX0RatChunk001Sub000Block091Part016
    + surrogateDiagTailX0RatChunk001Sub000Block091Part017
    + surrogateDiagTailX0RatChunk001Sub000Block091Part018
    + surrogateDiagTailX0RatChunk001Sub000Block091Part019

def surrogateDiagonalTailChunk001Sub000Block091TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block091Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block091Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block091Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block091Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block091Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block091Tail : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block091Part020
    + surrogateDiagTailX0RatChunk001Sub000Block091Part021
    + surrogateDiagTailX0RatChunk001Sub000Block091Part022
    + surrogateDiagTailX0RatChunk001Sub000Block091Part023
    + surrogateDiagTailX0RatChunk001Sub000Block091Part024

def surrogateDiagonalTailChunk001Sub000Block091Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk001Sub000Block091HeadSum X0
    + surrogateDiagonalTailChunk001Sub000Block091MidSum X0
    + surrogateDiagonalTailChunk001Sub000Block091TailSum X0

def surrogateDiagTailX0RatChunk001Sub000Block091 : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block091Part000
    + surrogateDiagTailX0RatChunk001Sub000Block091Part001
    + surrogateDiagTailX0RatChunk001Sub000Block091Part002
    + surrogateDiagTailX0RatChunk001Sub000Block091Part003
    + surrogateDiagTailX0RatChunk001Sub000Block091Part004
    + surrogateDiagTailX0RatChunk001Sub000Block091Part005
    + surrogateDiagTailX0RatChunk001Sub000Block091Part006
    + surrogateDiagTailX0RatChunk001Sub000Block091Part007
    + surrogateDiagTailX0RatChunk001Sub000Block091Part008
    + surrogateDiagTailX0RatChunk001Sub000Block091Part009
    + surrogateDiagTailX0RatChunk001Sub000Block091Part010
    + surrogateDiagTailX0RatChunk001Sub000Block091Part011
    + surrogateDiagTailX0RatChunk001Sub000Block091Part012
    + surrogateDiagTailX0RatChunk001Sub000Block091Part013
    + surrogateDiagTailX0RatChunk001Sub000Block091Part014
    + surrogateDiagTailX0RatChunk001Sub000Block091Part015
    + surrogateDiagTailX0RatChunk001Sub000Block091Part016
    + surrogateDiagTailX0RatChunk001Sub000Block091Part017
    + surrogateDiagTailX0RatChunk001Sub000Block091Part018
    + surrogateDiagTailX0RatChunk001Sub000Block091Part019
    + surrogateDiagTailX0RatChunk001Sub000Block091Part020
    + surrogateDiagTailX0RatChunk001Sub000Block091Part021
    + surrogateDiagTailX0RatChunk001Sub000Block091Part022
    + surrogateDiagTailX0RatChunk001Sub000Block091Part023
    + surrogateDiagTailX0RatChunk001Sub000Block091Part024

theorem surrogateDiagTailX0RatChunk001Sub000Block091_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk001Sub000Block091Head + surrogateDiagTailX0RatChunk001Sub000Block091Mid + surrogateDiagTailX0RatChunk001Sub000Block091Tail =
      surrogateDiagTailX0RatChunk001Sub000Block091 := by
  unfold surrogateDiagTailX0RatChunk001Sub000Block091Head surrogateDiagTailX0RatChunk001Sub000Block091Mid surrogateDiagTailX0RatChunk001Sub000Block091Tail surrogateDiagTailX0RatChunk001Sub000Block091
  ring

def SurrogateDiagonalTailChunk001Sub000Block091HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block091HeadSum X0 = surrogateDiagTailX0RatChunk001Sub000Block091Head

def SurrogateDiagonalTailChunk001Sub000Block091MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block091MidSum X0 = surrogateDiagTailX0RatChunk001Sub000Block091Mid

def SurrogateDiagonalTailChunk001Sub000Block091TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block091TailSum X0 = surrogateDiagTailX0RatChunk001Sub000Block091Tail

theorem surrogateDiagonalTailChunk001Sub000Block091_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk001Sub000Block091HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk001Sub000Block091MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk001Sub000Block091TailCertificateAt X0) :
    surrogateDiagonalTailChunk001Sub000Block091Sum X0 = surrogateDiagTailX0RatChunk001Sub000Block091 := by
  unfold SurrogateDiagonalTailChunk001Sub000Block091HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk001Sub000Block091MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk001Sub000Block091TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk001Sub000Block091Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk001Sub000Block091_eq_head_add_mid_add_tail

/-- Block 092 covers tail-support indices [12300,12325) and q from 20282 to 20318. -/

def TailChunk001Sub000Block092Part000SupportExplicit : Finset ℕ :=
  ([20282] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block092Part000 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block092Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20282
    = surrogateDiagTailX0RatChunk001Sub000Block092Part000

theorem surrogateDiagonalTailChunk001Sub000Block092Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block092Part000CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block092Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block092Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block092Part000CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block092Part000SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block092Part000] using hcert

def TailChunk001Sub000Block092Part001SupportExplicit : Finset ℕ :=
  ([20283] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block092Part001 : ℚ :=
  (5713450037 : ℚ) / 167095063991132160

def SurrogateDiagonalTailChunk001Sub000Block092Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20283
    = surrogateDiagTailX0RatChunk001Sub000Block092Part001

theorem surrogateDiagonalTailChunk001Sub000Block092Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block092Part001CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block092Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block092Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block092Part001CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block092Part001SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block092Part001] using hcert

def TailChunk001Sub000Block092Part002SupportExplicit : Finset ℕ :=
  ([20285] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block092Part002 : ℚ :=
  (1029446680375 : ℚ) / 173244162346005823488

def SurrogateDiagonalTailChunk001Sub000Block092Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20285
    = surrogateDiagTailX0RatChunk001Sub000Block092Part002

theorem surrogateDiagonalTailChunk001Sub000Block092Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block092Part002CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block092Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block092Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block092Part002CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block092Part002SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block092Part002] using hcert

def TailChunk001Sub000Block092Part003SupportExplicit : Finset ℕ :=
  ([20287] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block092Part003 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block092Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20287
    = surrogateDiagTailX0RatChunk001Sub000Block092Part003

theorem surrogateDiagonalTailChunk001Sub000Block092Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block092Part003CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block092Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block092Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block092Part003CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block092Part003SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block092Part003] using hcert

def TailChunk001Sub000Block092Part004SupportExplicit : Finset ℕ :=
  ([20289] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block092Part004 : ℚ :=
  (204172519175 : ℚ) / 5974746335830060992

def SurrogateDiagonalTailChunk001Sub000Block092Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20289
    = surrogateDiagTailX0RatChunk001Sub000Block092Part004

theorem surrogateDiagonalTailChunk001Sub000Block092Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block092Part004CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block092Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block092Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block092Part004CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block092Part004SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block092Part004] using hcert

def TailChunk001Sub000Block092Part005SupportExplicit : Finset ℕ :=
  ([20290] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block092Part005 : ℚ :=
  (171748565575 : ℚ) / 3609253382208454656

def SurrogateDiagonalTailChunk001Sub000Block092Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20290
    = surrogateDiagTailX0RatChunk001Sub000Block092Part005

theorem surrogateDiagonalTailChunk001Sub000Block092Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block092Part005CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block092Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block092Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block092Part005CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block092Part005SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block092Part005] using hcert

def TailChunk001Sub000Block092Part006SupportExplicit : Finset ℕ :=
  ([20291] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block092Part006 : ℚ :=
  (356512075 : ℚ) / 1560313499899960008

def SurrogateDiagonalTailChunk001Sub000Block092Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20291
    = surrogateDiagTailX0RatChunk001Sub000Block092Part006

theorem surrogateDiagonalTailChunk001Sub000Block092Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block092Part006CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block092Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block092Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block092Part006CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block092Part006SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block092Part006] using hcert

def TailChunk001Sub000Block092Part007SupportExplicit : Finset ℕ :=
  ([20293] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block092Part007 : ℚ :=
  (647253750725 : ℚ) / 81609129754640400384

def SurrogateDiagonalTailChunk001Sub000Block092Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20293
    = surrogateDiagTailX0RatChunk001Sub000Block092Part007

theorem surrogateDiagonalTailChunk001Sub000Block092Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block092Part007CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block092Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block092Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block092Part007CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block092Part007SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block092Part007] using hcert

def TailChunk001Sub000Block092Part008SupportExplicit : Finset ℕ :=
  ([20294] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block092Part008 : ℚ :=
  (16222927825 : ℚ) / 6092747762777137152

def SurrogateDiagonalTailChunk001Sub000Block092Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20294
    = surrogateDiagTailX0RatChunk001Sub000Block092Part008

theorem surrogateDiagonalTailChunk001Sub000Block092Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block092Part008CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block092Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block092Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block092Part008CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block092Part008SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block092Part008] using hcert

def TailChunk001Sub000Block092Part009SupportExplicit : Finset ℕ :=
  ([20297] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block092Part009 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block092Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20297
    = surrogateDiagTailX0RatChunk001Sub000Block092Part009

theorem surrogateDiagonalTailChunk001Sub000Block092Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block092Part009CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block092Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block092Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block092Part009CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block092Part009SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block092Part009] using hcert

def TailChunk001Sub000Block092Part010SupportExplicit : Finset ℕ :=
  ([20298] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block092Part010 : ℚ :=
  (459796016375 : ℚ) / 1343279164488155136

def SurrogateDiagonalTailChunk001Sub000Block092Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20298
    = surrogateDiagTailX0RatChunk001Sub000Block092Part010

theorem surrogateDiagonalTailChunk001Sub000Block092Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block092Part010CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block092Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block092Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block092Part010CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block092Part010SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block092Part010] using hcert

def TailChunk001Sub000Block092Part011SupportExplicit : Finset ℕ :=
  ([20299] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block092Part011 : ℚ :=
  (5609871675 : ℚ) / 16221179994116993792

def SurrogateDiagonalTailChunk001Sub000Block092Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20299
    = surrogateDiagTailX0RatChunk001Sub000Block092Part011

theorem surrogateDiagonalTailChunk001Sub000Block092Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block092Part011CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block092Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block092Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block092Part011CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block092Part011SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block092Part011] using hcert

def TailChunk001Sub000Block092Part012SupportExplicit : Finset ℕ :=
  ([20301] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block092Part012 : ℚ :=
  (112973042287 : ℚ) / 3036564951552000000

def SurrogateDiagonalTailChunk001Sub000Block092Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20301
    = surrogateDiagTailX0RatChunk001Sub000Block092Part012

theorem surrogateDiagonalTailChunk001Sub000Block092Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block092Part012CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block092Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block092Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block092Part012CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block092Part012SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block092Part012] using hcert

def TailChunk001Sub000Block092Part013SupportExplicit : Finset ℕ :=
  ([20302] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block092Part013 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block092Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20302
    = surrogateDiagTailX0RatChunk001Sub000Block092Part013

theorem surrogateDiagonalTailChunk001Sub000Block092Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block092Part013CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block092Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block092Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block092Part013CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block092Part013SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block092Part013] using hcert

def TailChunk001Sub000Block092Part014SupportExplicit : Finset ℕ :=
  ([20303] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block092Part014 : ℚ :=
  (101812481425 : ℚ) / 397525626676511244288

def SurrogateDiagonalTailChunk001Sub000Block092Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20303
    = surrogateDiagTailX0RatChunk001Sub000Block092Part014

theorem surrogateDiagonalTailChunk001Sub000Block092Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block092Part014CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block092Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block092Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block092Part014CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block092Part014SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block092Part014] using hcert

def TailChunk001Sub000Block092Part015SupportExplicit : Finset ℕ :=
  ([20305] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block092Part015 : ℚ :=
  (45548229787 : ℚ) / 5923593441792000000

def SurrogateDiagonalTailChunk001Sub000Block092Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20305
    = surrogateDiagTailX0RatChunk001Sub000Block092Part015

theorem surrogateDiagonalTailChunk001Sub000Block092Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block092Part015CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block092Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block092Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block092Part015CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block092Part015SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block092Part015] using hcert

def TailChunk001Sub000Block092Part016SupportExplicit : Finset ℕ :=
  ([20306] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block092Part016 : ℚ :=
  (136955321 : ℚ) / 3387557376000000

def SurrogateDiagonalTailChunk001Sub000Block092Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20306
    = surrogateDiagTailX0RatChunk001Sub000Block092Part016

theorem surrogateDiagonalTailChunk001Sub000Block092Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block092Part016CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block092Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block092Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block092Part016CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block092Part016SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block092Part016] using hcert

def TailChunk001Sub000Block092Part017SupportExplicit : Finset ℕ :=
  ([20307] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block092Part017 : ℚ :=
  (671589685675 : ℚ) / 11287567421626470912

def SurrogateDiagonalTailChunk001Sub000Block092Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20307
    = surrogateDiagTailX0RatChunk001Sub000Block092Part017

theorem surrogateDiagonalTailChunk001Sub000Block092Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block092Part017CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block092Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block092Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block092Part017CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block092Part017SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block092Part017] using hcert

def TailChunk001Sub000Block092Part018SupportExplicit : Finset ℕ :=
  ([20309] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block092Part018 : ℚ :=
  (249771630025 : ℚ) / 354480151552756403328

def SurrogateDiagonalTailChunk001Sub000Block092Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20309
    = surrogateDiagTailX0RatChunk001Sub000Block092Part018

theorem surrogateDiagonalTailChunk001Sub000Block092Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block092Part018CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block092Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block092Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block092Part018CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block092Part018SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block092Part018] using hcert

def TailChunk001Sub000Block092Part019SupportExplicit : Finset ℕ :=
  ([20310] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block092Part019 : ℚ :=
  (1230404025475 : ℚ) / 2138816819086491648

def SurrogateDiagonalTailChunk001Sub000Block092Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20310
    = surrogateDiagTailX0RatChunk001Sub000Block092Part019

theorem surrogateDiagonalTailChunk001Sub000Block092Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block092Part019CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block092Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block092Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block092Part019CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block092Part019SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block092Part019] using hcert

def TailChunk001Sub000Block092Part020SupportExplicit : Finset ℕ :=
  ([20311] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block092Part020 : ℚ :=
  (90445599325 : ℚ) / 85377198231400591872

def SurrogateDiagonalTailChunk001Sub000Block092Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20311
    = surrogateDiagTailX0RatChunk001Sub000Block092Part020

theorem surrogateDiagonalTailChunk001Sub000Block092Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block092Part020CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block092Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block092Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block092Part020CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block092Part020SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block092Part020] using hcert

def TailChunk001Sub000Block092Part021SupportExplicit : Finset ℕ :=
  ([20314] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block092Part021 : ℚ :=
  (21087361693 : ℚ) / 573012189522000000

def SurrogateDiagonalTailChunk001Sub000Block092Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20314
    = surrogateDiagTailX0RatChunk001Sub000Block092Part021

theorem surrogateDiagonalTailChunk001Sub000Block092Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block092Part021CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block092Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block092Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block092Part021CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block092Part021SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block092Part021] using hcert

def TailChunk001Sub000Block092Part022SupportExplicit : Finset ℕ :=
  ([20315] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block092Part022 : ℚ :=
  (172291093375 : ℚ) / 19228993075002998784

def SurrogateDiagonalTailChunk001Sub000Block092Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20315
    = surrogateDiagTailX0RatChunk001Sub000Block092Part022

theorem surrogateDiagonalTailChunk001Sub000Block092Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block092Part022CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block092Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block092Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block092Part022CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block092Part022SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block092Part022] using hcert

def TailChunk001Sub000Block092Part023SupportExplicit : Finset ℕ :=
  ([20317] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block092Part023 : ℚ :=
  (25672740583 : ℚ) / 11614850842323331200

def SurrogateDiagonalTailChunk001Sub000Block092Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20317
    = surrogateDiagTailX0RatChunk001Sub000Block092Part023

theorem surrogateDiagonalTailChunk001Sub000Block092Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block092Part023CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block092Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block092Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block092Part023CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block092Part023SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block092Part023] using hcert

def TailChunk001Sub000Block092Part024SupportExplicit : Finset ℕ :=
  ([20318] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block092Part024 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block092Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20318
    = surrogateDiagTailX0RatChunk001Sub000Block092Part024

theorem surrogateDiagonalTailChunk001Sub000Block092Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block092Part024CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block092Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block092Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block092Part024CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block092Part024SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block092Part024] using hcert

def surrogateDiagonalTailChunk001Sub000Block092HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block092Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block092Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block092Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block092Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block092Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block092Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block092Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block092Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block092Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block092Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block092Head : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block092Part000
    + surrogateDiagTailX0RatChunk001Sub000Block092Part001
    + surrogateDiagTailX0RatChunk001Sub000Block092Part002
    + surrogateDiagTailX0RatChunk001Sub000Block092Part003
    + surrogateDiagTailX0RatChunk001Sub000Block092Part004
    + surrogateDiagTailX0RatChunk001Sub000Block092Part005
    + surrogateDiagTailX0RatChunk001Sub000Block092Part006
    + surrogateDiagTailX0RatChunk001Sub000Block092Part007
    + surrogateDiagTailX0RatChunk001Sub000Block092Part008
    + surrogateDiagTailX0RatChunk001Sub000Block092Part009

def surrogateDiagonalTailChunk001Sub000Block092MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block092Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block092Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block092Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block092Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block092Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block092Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block092Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block092Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block092Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block092Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block092Mid : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block092Part010
    + surrogateDiagTailX0RatChunk001Sub000Block092Part011
    + surrogateDiagTailX0RatChunk001Sub000Block092Part012
    + surrogateDiagTailX0RatChunk001Sub000Block092Part013
    + surrogateDiagTailX0RatChunk001Sub000Block092Part014
    + surrogateDiagTailX0RatChunk001Sub000Block092Part015
    + surrogateDiagTailX0RatChunk001Sub000Block092Part016
    + surrogateDiagTailX0RatChunk001Sub000Block092Part017
    + surrogateDiagTailX0RatChunk001Sub000Block092Part018
    + surrogateDiagTailX0RatChunk001Sub000Block092Part019

def surrogateDiagonalTailChunk001Sub000Block092TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block092Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block092Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block092Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block092Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block092Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block092Tail : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block092Part020
    + surrogateDiagTailX0RatChunk001Sub000Block092Part021
    + surrogateDiagTailX0RatChunk001Sub000Block092Part022
    + surrogateDiagTailX0RatChunk001Sub000Block092Part023
    + surrogateDiagTailX0RatChunk001Sub000Block092Part024

def surrogateDiagonalTailChunk001Sub000Block092Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk001Sub000Block092HeadSum X0
    + surrogateDiagonalTailChunk001Sub000Block092MidSum X0
    + surrogateDiagonalTailChunk001Sub000Block092TailSum X0

def surrogateDiagTailX0RatChunk001Sub000Block092 : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block092Part000
    + surrogateDiagTailX0RatChunk001Sub000Block092Part001
    + surrogateDiagTailX0RatChunk001Sub000Block092Part002
    + surrogateDiagTailX0RatChunk001Sub000Block092Part003
    + surrogateDiagTailX0RatChunk001Sub000Block092Part004
    + surrogateDiagTailX0RatChunk001Sub000Block092Part005
    + surrogateDiagTailX0RatChunk001Sub000Block092Part006
    + surrogateDiagTailX0RatChunk001Sub000Block092Part007
    + surrogateDiagTailX0RatChunk001Sub000Block092Part008
    + surrogateDiagTailX0RatChunk001Sub000Block092Part009
    + surrogateDiagTailX0RatChunk001Sub000Block092Part010
    + surrogateDiagTailX0RatChunk001Sub000Block092Part011
    + surrogateDiagTailX0RatChunk001Sub000Block092Part012
    + surrogateDiagTailX0RatChunk001Sub000Block092Part013
    + surrogateDiagTailX0RatChunk001Sub000Block092Part014
    + surrogateDiagTailX0RatChunk001Sub000Block092Part015
    + surrogateDiagTailX0RatChunk001Sub000Block092Part016
    + surrogateDiagTailX0RatChunk001Sub000Block092Part017
    + surrogateDiagTailX0RatChunk001Sub000Block092Part018
    + surrogateDiagTailX0RatChunk001Sub000Block092Part019
    + surrogateDiagTailX0RatChunk001Sub000Block092Part020
    + surrogateDiagTailX0RatChunk001Sub000Block092Part021
    + surrogateDiagTailX0RatChunk001Sub000Block092Part022
    + surrogateDiagTailX0RatChunk001Sub000Block092Part023
    + surrogateDiagTailX0RatChunk001Sub000Block092Part024

theorem surrogateDiagTailX0RatChunk001Sub000Block092_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk001Sub000Block092Head + surrogateDiagTailX0RatChunk001Sub000Block092Mid + surrogateDiagTailX0RatChunk001Sub000Block092Tail =
      surrogateDiagTailX0RatChunk001Sub000Block092 := by
  unfold surrogateDiagTailX0RatChunk001Sub000Block092Head surrogateDiagTailX0RatChunk001Sub000Block092Mid surrogateDiagTailX0RatChunk001Sub000Block092Tail surrogateDiagTailX0RatChunk001Sub000Block092
  ring

def SurrogateDiagonalTailChunk001Sub000Block092HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block092HeadSum X0 = surrogateDiagTailX0RatChunk001Sub000Block092Head

def SurrogateDiagonalTailChunk001Sub000Block092MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block092MidSum X0 = surrogateDiagTailX0RatChunk001Sub000Block092Mid

def SurrogateDiagonalTailChunk001Sub000Block092TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block092TailSum X0 = surrogateDiagTailX0RatChunk001Sub000Block092Tail

theorem surrogateDiagonalTailChunk001Sub000Block092_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk001Sub000Block092HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk001Sub000Block092MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk001Sub000Block092TailCertificateAt X0) :
    surrogateDiagonalTailChunk001Sub000Block092Sum X0 = surrogateDiagTailX0RatChunk001Sub000Block092 := by
  unfold SurrogateDiagonalTailChunk001Sub000Block092HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk001Sub000Block092MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk001Sub000Block092TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk001Sub000Block092Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk001Sub000Block092_eq_head_add_mid_add_tail

/-- Block 093 covers tail-support indices [12325,12350) and q from 20319 to 20362. -/

def TailChunk001Sub000Block093Part000SupportExplicit : Finset ℕ :=
  ([20319] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block093Part000 : ℚ :=
  (1118314423 : ℚ) / 24263038737580032

def SurrogateDiagonalTailChunk001Sub000Block093Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20319
    = surrogateDiagTailX0RatChunk001Sub000Block093Part000

theorem surrogateDiagonalTailChunk001Sub000Block093Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block093Part000CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block093Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block093Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block093Part000CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block093Part000SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block093Part000] using hcert

def TailChunk001Sub000Block093Part001SupportExplicit : Finset ℕ :=
  ([20321] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block093Part001 : ℚ :=
  (528225144925 : ℚ) / 229837819514552304768

def SurrogateDiagonalTailChunk001Sub000Block093Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20321
    = surrogateDiagTailX0RatChunk001Sub000Block093Part001

theorem surrogateDiagonalTailChunk001Sub000Block093Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block093Part001CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block093Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block093Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block093Part001CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block093Part001SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block093Part001] using hcert

def TailChunk001Sub000Block093Part002SupportExplicit : Finset ℕ :=
  ([20323] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block093Part002 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block093Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20323
    = surrogateDiagTailX0RatChunk001Sub000Block093Part002

theorem surrogateDiagonalTailChunk001Sub000Block093Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block093Part002CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block093Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block093Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block093Part002CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block093Part002SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block093Part002] using hcert

def TailChunk001Sub000Block093Part003SupportExplicit : Finset ℕ :=
  ([20326] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block093Part003 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block093Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20326
    = surrogateDiagTailX0RatChunk001Sub000Block093Part003

theorem surrogateDiagonalTailChunk001Sub000Block093Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block093Part003CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block093Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block093Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block093Part003CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block093Part003SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block093Part003] using hcert

def TailChunk001Sub000Block093Part004SupportExplicit : Finset ℕ :=
  ([20327] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block093Part004 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block093Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20327
    = surrogateDiagTailX0RatChunk001Sub000Block093Part004

theorem surrogateDiagonalTailChunk001Sub000Block093Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block093Part004CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block093Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block093Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block093Part004CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block093Part004SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block093Part004] using hcert

def TailChunk001Sub000Block093Part005SupportExplicit : Finset ℕ :=
  ([20329] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block093Part005 : ℚ :=
  (8913984217 : ℚ) / 14760842138112000000

def SurrogateDiagonalTailChunk001Sub000Block093Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20329
    = surrogateDiagTailX0RatChunk001Sub000Block093Part005

theorem surrogateDiagonalTailChunk001Sub000Block093Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block093Part005CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block093Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block093Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block093Part005CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block093Part005SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block093Part005] using hcert

def TailChunk001Sub000Block093Part006SupportExplicit : Finset ℕ :=
  ([20330] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block093Part006 : ℚ :=
  (830266492675 : ℚ) / 8483602387790757888

def SurrogateDiagonalTailChunk001Sub000Block093Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20330
    = surrogateDiagTailX0RatChunk001Sub000Block093Part006

theorem surrogateDiagonalTailChunk001Sub000Block093Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block093Part006CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block093Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block093Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block093Part006CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block093Part006SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block093Part006] using hcert

def TailChunk001Sub000Block093Part007SupportExplicit : Finset ℕ :=
  ([20333] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block093Part007 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block093Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20333
    = surrogateDiagTailX0RatChunk001Sub000Block093Part007

theorem surrogateDiagonalTailChunk001Sub000Block093Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block093Part007CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block093Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block093Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block093Part007CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block093Part007SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block093Part007] using hcert

def TailChunk001Sub000Block093Part008SupportExplicit : Finset ℕ :=
  ([20334] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block093Part008 : ℚ :=
  (717577911275 : ℚ) / 2635666475088159744

def SurrogateDiagonalTailChunk001Sub000Block093Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20334
    = surrogateDiagTailX0RatChunk001Sub000Block093Part008

theorem surrogateDiagonalTailChunk001Sub000Block093Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block093Part008CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block093Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block093Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block093Part008CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block093Part008SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block093Part008] using hcert

def TailChunk001Sub000Block093Part009SupportExplicit : Finset ℕ :=
  ([20337] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block093Part009 : ℚ :=
  (1435977634025 : ℚ) / 42220473917675394624

def SurrogateDiagonalTailChunk001Sub000Block093Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20337
    = surrogateDiagTailX0RatChunk001Sub000Block093Part009

theorem surrogateDiagonalTailChunk001Sub000Block093Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block093Part009CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block093Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block093Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block093Part009CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block093Part009SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block093Part009] using hcert

def TailChunk001Sub000Block093Part010SupportExplicit : Finset ℕ :=
  ([20338] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block093Part010 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block093Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20338
    = surrogateDiagTailX0RatChunk001Sub000Block093Part010

theorem surrogateDiagonalTailChunk001Sub000Block093Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block093Part010CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block093Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block093Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block093Part010CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block093Part010SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block093Part010] using hcert

def TailChunk001Sub000Block093Part011SupportExplicit : Finset ℕ :=
  ([20341] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block093Part011 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block093Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20341
    = surrogateDiagTailX0RatChunk001Sub000Block093Part011

theorem surrogateDiagonalTailChunk001Sub000Block093Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block093Part011CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block093Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block093Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block093Part011CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block093Part011SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block093Part011] using hcert

def TailChunk001Sub000Block093Part012SupportExplicit : Finset ℕ :=
  ([20342] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block093Part012 : ℚ :=
  (7352287075 : ℚ) / 266750084734036992

def SurrogateDiagonalTailChunk001Sub000Block093Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20342
    = surrogateDiagTailX0RatChunk001Sub000Block093Part012

theorem surrogateDiagonalTailChunk001Sub000Block093Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block093Part012CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block093Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block093Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block093Part012CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block093Part012SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block093Part012] using hcert

def TailChunk001Sub000Block093Part013SupportExplicit : Finset ℕ :=
  ([20343] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block093Part013 : ℚ :=
  (1436825009 : ℚ) / 42270328346394240

def SurrogateDiagonalTailChunk001Sub000Block093Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20343
    = surrogateDiagTailX0RatChunk001Sub000Block093Part013

theorem surrogateDiagonalTailChunk001Sub000Block093Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block093Part013CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block093Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block093Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block093Part013CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block093Part013SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block093Part013] using hcert

def TailChunk001Sub000Block093Part014SupportExplicit : Finset ℕ :=
  ([20345] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block093Part014 : ℚ :=
  (29525023475 : ℚ) / 1746938789105762304

def SurrogateDiagonalTailChunk001Sub000Block093Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20345
    = surrogateDiagTailX0RatChunk001Sub000Block093Part014

theorem surrogateDiagonalTailChunk001Sub000Block093Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block093Part014CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block093Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block093Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block093Part014CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block093Part014SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block093Part014] using hcert

def TailChunk001Sub000Block093Part015SupportExplicit : Finset ℕ :=
  ([20346] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block093Part015 : ℚ :=
  (2875525411 : ℚ) / 21135164173197120

def SurrogateDiagonalTailChunk001Sub000Block093Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20346
    = surrogateDiagTailX0RatChunk001Sub000Block093Part015

theorem surrogateDiagonalTailChunk001Sub000Block093Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block093Part015CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block093Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block093Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block093Part015CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block093Part015SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block093Part015] using hcert

def TailChunk001Sub000Block093Part016SupportExplicit : Finset ℕ :=
  ([20347] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block093Part016 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block093Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20347
    = surrogateDiagTailX0RatChunk001Sub000Block093Part016

theorem surrogateDiagonalTailChunk001Sub000Block093Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block093Part016CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block093Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block093Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block093Part016CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block093Part016SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block093Part016] using hcert

def TailChunk001Sub000Block093Part017SupportExplicit : Finset ℕ :=
  ([20351] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block093Part017 : ℚ :=
  (153987529225 : ℚ) / 389935856817736777728

def SurrogateDiagonalTailChunk001Sub000Block093Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20351
    = surrogateDiagTailX0RatChunk001Sub000Block093Part017

theorem surrogateDiagonalTailChunk001Sub000Block093Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block093Part017CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block093Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block093Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block093Part017CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block093Part017SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block093Part017] using hcert

def TailChunk001Sub000Block093Part018SupportExplicit : Finset ℕ :=
  ([20353] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block093Part018 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block093Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20353
    = surrogateDiagTailX0RatChunk001Sub000Block093Part018

theorem surrogateDiagonalTailChunk001Sub000Block093Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block093Part018CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block093Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block093Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block093Part018CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block093Part018SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block093Part018] using hcert

def TailChunk001Sub000Block093Part019SupportExplicit : Finset ℕ :=
  ([20354] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block093Part019 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block093Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20354
    = surrogateDiagTailX0RatChunk001Sub000Block093Part019

theorem surrogateDiagonalTailChunk001Sub000Block093Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block093Part019CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block093Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block093Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block093Part019CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block093Part019SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block093Part019] using hcert

def TailChunk001Sub000Block093Part020SupportExplicit : Finset ℕ :=
  ([20355] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block093Part020 : ℚ :=
  (2738452600075 : ℚ) / 27151229730748366848

def SurrogateDiagonalTailChunk001Sub000Block093Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20355
    = surrogateDiagTailX0RatChunk001Sub000Block093Part020

theorem surrogateDiagonalTailChunk001Sub000Block093Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block093Part020CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block093Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block093Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block093Part020CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block093Part020SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block093Part020] using hcert

def TailChunk001Sub000Block093Part021SupportExplicit : Finset ℕ :=
  ([20357] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block093Part021 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block093Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20357
    = surrogateDiagTailX0RatChunk001Sub000Block093Part021

theorem surrogateDiagonalTailChunk001Sub000Block093Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block093Part021CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block093Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block093Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block093Part021CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block093Part021SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block093Part021] using hcert

def TailChunk001Sub000Block093Part022SupportExplicit : Finset ℕ :=
  ([20359] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block093Part022 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block093Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20359
    = surrogateDiagTailX0RatChunk001Sub000Block093Part022

theorem surrogateDiagonalTailChunk001Sub000Block093Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block093Part022CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block093Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block093Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block093Part022CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block093Part022SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block093Part022] using hcert

def TailChunk001Sub000Block093Part023SupportExplicit : Finset ℕ :=
  ([20361] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block093Part023 : ℚ :=
  (21490505051 : ℚ) / 460850090582999040

def SurrogateDiagonalTailChunk001Sub000Block093Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20361
    = surrogateDiagTailX0RatChunk001Sub000Block093Part023

theorem surrogateDiagonalTailChunk001Sub000Block093Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block093Part023CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block093Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block093Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block093Part023CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block093Part023SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block093Part023] using hcert

def TailChunk001Sub000Block093Part024SupportExplicit : Finset ℕ :=
  ([20362] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block093Part024 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block093Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20362
    = surrogateDiagTailX0RatChunk001Sub000Block093Part024

theorem surrogateDiagonalTailChunk001Sub000Block093Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block093Part024CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block093Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block093Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block093Part024CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block093Part024SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block093Part024] using hcert

def surrogateDiagonalTailChunk001Sub000Block093HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block093Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block093Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block093Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block093Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block093Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block093Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block093Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block093Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block093Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block093Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block093Head : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block093Part000
    + surrogateDiagTailX0RatChunk001Sub000Block093Part001
    + surrogateDiagTailX0RatChunk001Sub000Block093Part002
    + surrogateDiagTailX0RatChunk001Sub000Block093Part003
    + surrogateDiagTailX0RatChunk001Sub000Block093Part004
    + surrogateDiagTailX0RatChunk001Sub000Block093Part005
    + surrogateDiagTailX0RatChunk001Sub000Block093Part006
    + surrogateDiagTailX0RatChunk001Sub000Block093Part007
    + surrogateDiagTailX0RatChunk001Sub000Block093Part008
    + surrogateDiagTailX0RatChunk001Sub000Block093Part009

def surrogateDiagonalTailChunk001Sub000Block093MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block093Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block093Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block093Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block093Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block093Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block093Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block093Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block093Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block093Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block093Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block093Mid : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block093Part010
    + surrogateDiagTailX0RatChunk001Sub000Block093Part011
    + surrogateDiagTailX0RatChunk001Sub000Block093Part012
    + surrogateDiagTailX0RatChunk001Sub000Block093Part013
    + surrogateDiagTailX0RatChunk001Sub000Block093Part014
    + surrogateDiagTailX0RatChunk001Sub000Block093Part015
    + surrogateDiagTailX0RatChunk001Sub000Block093Part016
    + surrogateDiagTailX0RatChunk001Sub000Block093Part017
    + surrogateDiagTailX0RatChunk001Sub000Block093Part018
    + surrogateDiagTailX0RatChunk001Sub000Block093Part019

def surrogateDiagonalTailChunk001Sub000Block093TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block093Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block093Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block093Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block093Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block093Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block093Tail : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block093Part020
    + surrogateDiagTailX0RatChunk001Sub000Block093Part021
    + surrogateDiagTailX0RatChunk001Sub000Block093Part022
    + surrogateDiagTailX0RatChunk001Sub000Block093Part023
    + surrogateDiagTailX0RatChunk001Sub000Block093Part024

def surrogateDiagonalTailChunk001Sub000Block093Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk001Sub000Block093HeadSum X0
    + surrogateDiagonalTailChunk001Sub000Block093MidSum X0
    + surrogateDiagonalTailChunk001Sub000Block093TailSum X0

def surrogateDiagTailX0RatChunk001Sub000Block093 : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block093Part000
    + surrogateDiagTailX0RatChunk001Sub000Block093Part001
    + surrogateDiagTailX0RatChunk001Sub000Block093Part002
    + surrogateDiagTailX0RatChunk001Sub000Block093Part003
    + surrogateDiagTailX0RatChunk001Sub000Block093Part004
    + surrogateDiagTailX0RatChunk001Sub000Block093Part005
    + surrogateDiagTailX0RatChunk001Sub000Block093Part006
    + surrogateDiagTailX0RatChunk001Sub000Block093Part007
    + surrogateDiagTailX0RatChunk001Sub000Block093Part008
    + surrogateDiagTailX0RatChunk001Sub000Block093Part009
    + surrogateDiagTailX0RatChunk001Sub000Block093Part010
    + surrogateDiagTailX0RatChunk001Sub000Block093Part011
    + surrogateDiagTailX0RatChunk001Sub000Block093Part012
    + surrogateDiagTailX0RatChunk001Sub000Block093Part013
    + surrogateDiagTailX0RatChunk001Sub000Block093Part014
    + surrogateDiagTailX0RatChunk001Sub000Block093Part015
    + surrogateDiagTailX0RatChunk001Sub000Block093Part016
    + surrogateDiagTailX0RatChunk001Sub000Block093Part017
    + surrogateDiagTailX0RatChunk001Sub000Block093Part018
    + surrogateDiagTailX0RatChunk001Sub000Block093Part019
    + surrogateDiagTailX0RatChunk001Sub000Block093Part020
    + surrogateDiagTailX0RatChunk001Sub000Block093Part021
    + surrogateDiagTailX0RatChunk001Sub000Block093Part022
    + surrogateDiagTailX0RatChunk001Sub000Block093Part023
    + surrogateDiagTailX0RatChunk001Sub000Block093Part024

theorem surrogateDiagTailX0RatChunk001Sub000Block093_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk001Sub000Block093Head + surrogateDiagTailX0RatChunk001Sub000Block093Mid + surrogateDiagTailX0RatChunk001Sub000Block093Tail =
      surrogateDiagTailX0RatChunk001Sub000Block093 := by
  unfold surrogateDiagTailX0RatChunk001Sub000Block093Head surrogateDiagTailX0RatChunk001Sub000Block093Mid surrogateDiagTailX0RatChunk001Sub000Block093Tail surrogateDiagTailX0RatChunk001Sub000Block093
  ring

def SurrogateDiagonalTailChunk001Sub000Block093HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block093HeadSum X0 = surrogateDiagTailX0RatChunk001Sub000Block093Head

def SurrogateDiagonalTailChunk001Sub000Block093MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block093MidSum X0 = surrogateDiagTailX0RatChunk001Sub000Block093Mid

def SurrogateDiagonalTailChunk001Sub000Block093TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block093TailSum X0 = surrogateDiagTailX0RatChunk001Sub000Block093Tail

theorem surrogateDiagonalTailChunk001Sub000Block093_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk001Sub000Block093HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk001Sub000Block093MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk001Sub000Block093TailCertificateAt X0) :
    surrogateDiagonalTailChunk001Sub000Block093Sum X0 = surrogateDiagTailX0RatChunk001Sub000Block093 := by
  unfold SurrogateDiagonalTailChunk001Sub000Block093HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk001Sub000Block093MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk001Sub000Block093TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk001Sub000Block093Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk001Sub000Block093_eq_head_add_mid_add_tail

/-- Block 094 covers tail-support indices [12350,12375) and q from 20363 to 20401. -/

def TailChunk001Sub000Block094Part000SupportExplicit : Finset ℕ :=
  ([20363] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block094Part000 : ℚ :=
  (529360710575 : ℚ) / 115872258898755707904

def SurrogateDiagonalTailChunk001Sub000Block094Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20363
    = surrogateDiagTailX0RatChunk001Sub000Block094Part000

theorem surrogateDiagonalTailChunk001Sub000Block094Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block094Part000CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block094Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block094Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block094Part000CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block094Part000SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block094Part000] using hcert

def TailChunk001Sub000Block094Part001SupportExplicit : Finset ℕ :=
  ([20365] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block094Part001 : ℚ :=
  (345858226125 : ℚ) / 58664671994543865856

def SurrogateDiagonalTailChunk001Sub000Block094Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20365
    = surrogateDiagTailX0RatChunk001Sub000Block094Part001

theorem surrogateDiagonalTailChunk001Sub000Block094Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block094Part001CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block094Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block094Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block094Part001CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block094Part001SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block094Part001] using hcert

def TailChunk001Sub000Block094Part002SupportExplicit : Finset ℕ :=
  ([20366] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block094Part002 : ℚ :=
  (68609407725 : ℚ) / 6985383768892112896

def SurrogateDiagonalTailChunk001Sub000Block094Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20366
    = surrogateDiagTailX0RatChunk001Sub000Block094Part002

theorem surrogateDiagonalTailChunk001Sub000Block094Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block094Part002CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block094Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block094Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block094Part002CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block094Part002SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block094Part002] using hcert

def TailChunk001Sub000Block094Part003SupportExplicit : Finset ℕ :=
  ([20369] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block094Part003 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block094Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20369
    = surrogateDiagTailX0RatChunk001Sub000Block094Part003

theorem surrogateDiagonalTailChunk001Sub000Block094Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block094Part003CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block094Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block094Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block094Part003CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block094Part003SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block094Part003] using hcert

def TailChunk001Sub000Block094Part004SupportExplicit : Finset ℕ :=
  ([20370] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block094Part004 : ℚ :=
  (418753806425 : ℚ) / 563698325702836224

def SurrogateDiagonalTailChunk001Sub000Block094Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20370
    = surrogateDiagTailX0RatChunk001Sub000Block094Part004

theorem surrogateDiagonalTailChunk001Sub000Block094Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block094Part004CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block094Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block094Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block094Part004CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block094Part004SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block094Part004] using hcert

def TailChunk001Sub000Block094Part005SupportExplicit : Finset ℕ :=
  ([20371] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block094Part005 : ℚ :=
  (115846515925 : ℚ) / 77957675779010867712

def SurrogateDiagonalTailChunk001Sub000Block094Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20371
    = surrogateDiagTailX0RatChunk001Sub000Block094Part005

theorem surrogateDiagonalTailChunk001Sub000Block094Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block094Part005CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block094Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block094Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block094Part005CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block094Part005SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block094Part005] using hcert

def TailChunk001Sub000Block094Part006SupportExplicit : Finset ℕ :=
  ([20373] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block094Part006 : ℚ :=
  (1646932153 : ℚ) / 48594586386682560

def SurrogateDiagonalTailChunk001Sub000Block094Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20373
    = surrogateDiagTailX0RatChunk001Sub000Block094Part006

theorem surrogateDiagonalTailChunk001Sub000Block094Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block094Part006CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block094Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block094Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block094Part006CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block094Part006SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block094Part006] using hcert

def TailChunk001Sub000Block094Part007SupportExplicit : Finset ℕ :=
  ([20374] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block094Part007 : ℚ :=
  (2736852439 : ℚ) / 984292563404851200

def SurrogateDiagonalTailChunk001Sub000Block094Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20374
    = surrogateDiagTailX0RatChunk001Sub000Block094Part007

theorem surrogateDiagonalTailChunk001Sub000Block094Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block094Part007CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block094Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block094Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block094Part007CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block094Part007SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block094Part007] using hcert

def TailChunk001Sub000Block094Part008SupportExplicit : Finset ℕ :=
  ([20377] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block094Part008 : ℚ :=
  (23622917063 : ℚ) / 3983767474176000000

def SurrogateDiagonalTailChunk001Sub000Block094Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20377
    = surrogateDiagTailX0RatChunk001Sub000Block094Part008

theorem surrogateDiagonalTailChunk001Sub000Block094Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block094Part008CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block094Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block094Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block094Part008CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block094Part008SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block094Part008] using hcert

def TailChunk001Sub000Block094Part009SupportExplicit : Finset ℕ :=
  ([20378] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block094Part009 : ℚ :=
  (1806512025 : ℚ) / 286623672879068096

def SurrogateDiagonalTailChunk001Sub000Block094Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20378
    = surrogateDiagTailX0RatChunk001Sub000Block094Part009

theorem surrogateDiagonalTailChunk001Sub000Block094Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block094Part009CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block094Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block094Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block094Part009CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block094Part009SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block094Part009] using hcert

def TailChunk001Sub000Block094Part010SupportExplicit : Finset ℕ :=
  ([20379] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block094Part010 : ℚ :=
  (720957254425 : ℚ) / 21285191369413435392

def SurrogateDiagonalTailChunk001Sub000Block094Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20379
    = surrogateDiagTailX0RatChunk001Sub000Block094Part010

theorem surrogateDiagonalTailChunk001Sub000Block094Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block094Part010CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block094Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block094Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block094Part010CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block094Part010SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block094Part010] using hcert

def TailChunk001Sub000Block094Part011SupportExplicit : Finset ℕ :=
  ([20381] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block094Part011 : ℚ :=
  (99067098475 : ℚ) / 405225657396437188608

def SurrogateDiagonalTailChunk001Sub000Block094Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20381
    = surrogateDiagTailX0RatChunk001Sub000Block094Part011

theorem surrogateDiagonalTailChunk001Sub000Block094Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block094Part011CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block094Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block094Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block094Part011CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block094Part011SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block094Part011] using hcert

def TailChunk001Sub000Block094Part012SupportExplicit : Finset ℕ :=
  ([20382] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block094Part012 : ℚ :=
  (744587859025 : ℚ) / 4608105504612599808

def SurrogateDiagonalTailChunk001Sub000Block094Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20382
    = surrogateDiagTailX0RatChunk001Sub000Block094Part012

theorem surrogateDiagonalTailChunk001Sub000Block094Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block094Part012CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block094Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block094Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block094Part012CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block094Part012SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block094Part012] using hcert

def TailChunk001Sub000Block094Part013SupportExplicit : Finset ℕ :=
  ([20383] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block094Part013 : ℚ :=
  (1550108611 : ℚ) / 371578486181068800

def SurrogateDiagonalTailChunk001Sub000Block094Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20383
    = surrogateDiagTailX0RatChunk001Sub000Block094Part013

theorem surrogateDiagonalTailChunk001Sub000Block094Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block094Part013CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block094Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block094Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block094Part013CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block094Part013SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block094Part013] using hcert

def TailChunk001Sub000Block094Part014SupportExplicit : Finset ℕ :=
  ([20386] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block094Part014 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block094Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20386
    = surrogateDiagTailX0RatChunk001Sub000Block094Part014

theorem surrogateDiagonalTailChunk001Sub000Block094Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block094Part014CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block094Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block094Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block094Part014CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block094Part014SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block094Part014] using hcert

def TailChunk001Sub000Block094Part015SupportExplicit : Finset ℕ :=
  ([20387] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block094Part015 : ℚ :=
  (333441892475 : ℚ) / 135496791695588327424

def SurrogateDiagonalTailChunk001Sub000Block094Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20387
    = surrogateDiagTailX0RatChunk001Sub000Block094Part015

theorem surrogateDiagonalTailChunk001Sub000Block094Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block094Part015CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block094Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block094Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block094Part015CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block094Part015SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block094Part015] using hcert

def TailChunk001Sub000Block094Part016SupportExplicit : Finset ℕ :=
  ([20389] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block094Part016 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block094Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20389
    = surrogateDiagTailX0RatChunk001Sub000Block094Part016

theorem surrogateDiagonalTailChunk001Sub000Block094Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block094Part016CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block094Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block094Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block094Part016CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block094Part016SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block094Part016] using hcert

def TailChunk001Sub000Block094Part017SupportExplicit : Finset ℕ :=
  ([20390] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block094Part017 : ℚ :=
  (520327177225 : ℚ) / 11042910259550865408

def SurrogateDiagonalTailChunk001Sub000Block094Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20390
    = surrogateDiagTailX0RatChunk001Sub000Block094Part017

theorem surrogateDiagonalTailChunk001Sub000Block094Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block094Part017CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block094Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block094Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block094Part017CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block094Part017SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block094Part017] using hcert

def TailChunk001Sub000Block094Part018SupportExplicit : Finset ℕ :=
  ([20391] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block094Part018 : ℚ :=
  (110704629013 : ℚ) / 1836110319450163200

def SurrogateDiagonalTailChunk001Sub000Block094Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20391
    = surrogateDiagTailX0RatChunk001Sub000Block094Part018

theorem surrogateDiagonalTailChunk001Sub000Block094Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block094Part018CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block094Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block094Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block094Part018CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block094Part018SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block094Part018] using hcert

def TailChunk001Sub000Block094Part019SupportExplicit : Finset ℕ :=
  ([20393] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block094Part019 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block094Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20393
    = surrogateDiagTailX0RatChunk001Sub000Block094Part019

theorem surrogateDiagonalTailChunk001Sub000Block094Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block094Part019CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block094Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block094Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block094Part019CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block094Part019SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block094Part019] using hcert

def TailChunk001Sub000Block094Part020SupportExplicit : Finset ℕ :=
  ([20395] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block094Part020 : ℚ :=
  (346876975875 : ℚ) / 59011201234309421056

def SurrogateDiagonalTailChunk001Sub000Block094Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20395
    = surrogateDiagTailX0RatChunk001Sub000Block094Part020

theorem surrogateDiagonalTailChunk001Sub000Block094Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block094Part020CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block094Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block094Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block094Part020CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block094Part020SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block094Part020] using hcert

def TailChunk001Sub000Block094Part021SupportExplicit : Finset ℕ :=
  ([20397] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block094Part021 : ℚ :=
  (397762225 : ℚ) / 8911485571446144

def SurrogateDiagonalTailChunk001Sub000Block094Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20397
    = surrogateDiagTailX0RatChunk001Sub000Block094Part021

theorem surrogateDiagonalTailChunk001Sub000Block094Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block094Part021CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block094Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block094Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block094Part021CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block094Part021SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block094Part021] using hcert

def TailChunk001Sub000Block094Part022SupportExplicit : Finset ℕ :=
  ([20398] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block094Part022 : ℚ :=
  (2479683701 : ℚ) / 58764928267526400

def SurrogateDiagonalTailChunk001Sub000Block094Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20398
    = surrogateDiagTailX0RatChunk001Sub000Block094Part022

theorem surrogateDiagonalTailChunk001Sub000Block094Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block094Part022CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block094Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block094Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block094Part022CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block094Part022SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block094Part022] using hcert

def TailChunk001Sub000Block094Part023SupportExplicit : Finset ℕ :=
  ([20399] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block094Part023 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block094Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20399
    = surrogateDiagTailX0RatChunk001Sub000Block094Part023

theorem surrogateDiagonalTailChunk001Sub000Block094Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block094Part023CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block094Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block094Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block094Part023CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block094Part023SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block094Part023] using hcert

def TailChunk001Sub000Block094Part024SupportExplicit : Finset ℕ :=
  ([20401] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block094Part024 : ℚ :=
  (300943905475 : ℚ) / 360954507656408274048

def SurrogateDiagonalTailChunk001Sub000Block094Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20401
    = surrogateDiagTailX0RatChunk001Sub000Block094Part024

theorem surrogateDiagonalTailChunk001Sub000Block094Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block094Part024CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block094Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block094Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block094Part024CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block094Part024SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block094Part024] using hcert

def surrogateDiagonalTailChunk001Sub000Block094HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block094Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block094Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block094Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block094Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block094Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block094Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block094Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block094Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block094Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block094Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block094Head : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block094Part000
    + surrogateDiagTailX0RatChunk001Sub000Block094Part001
    + surrogateDiagTailX0RatChunk001Sub000Block094Part002
    + surrogateDiagTailX0RatChunk001Sub000Block094Part003
    + surrogateDiagTailX0RatChunk001Sub000Block094Part004
    + surrogateDiagTailX0RatChunk001Sub000Block094Part005
    + surrogateDiagTailX0RatChunk001Sub000Block094Part006
    + surrogateDiagTailX0RatChunk001Sub000Block094Part007
    + surrogateDiagTailX0RatChunk001Sub000Block094Part008
    + surrogateDiagTailX0RatChunk001Sub000Block094Part009

def surrogateDiagonalTailChunk001Sub000Block094MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block094Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block094Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block094Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block094Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block094Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block094Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block094Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block094Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block094Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block094Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block094Mid : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block094Part010
    + surrogateDiagTailX0RatChunk001Sub000Block094Part011
    + surrogateDiagTailX0RatChunk001Sub000Block094Part012
    + surrogateDiagTailX0RatChunk001Sub000Block094Part013
    + surrogateDiagTailX0RatChunk001Sub000Block094Part014
    + surrogateDiagTailX0RatChunk001Sub000Block094Part015
    + surrogateDiagTailX0RatChunk001Sub000Block094Part016
    + surrogateDiagTailX0RatChunk001Sub000Block094Part017
    + surrogateDiagTailX0RatChunk001Sub000Block094Part018
    + surrogateDiagTailX0RatChunk001Sub000Block094Part019

def surrogateDiagonalTailChunk001Sub000Block094TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block094Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block094Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block094Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block094Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block094Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block094Tail : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block094Part020
    + surrogateDiagTailX0RatChunk001Sub000Block094Part021
    + surrogateDiagTailX0RatChunk001Sub000Block094Part022
    + surrogateDiagTailX0RatChunk001Sub000Block094Part023
    + surrogateDiagTailX0RatChunk001Sub000Block094Part024

def surrogateDiagonalTailChunk001Sub000Block094Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk001Sub000Block094HeadSum X0
    + surrogateDiagonalTailChunk001Sub000Block094MidSum X0
    + surrogateDiagonalTailChunk001Sub000Block094TailSum X0

def surrogateDiagTailX0RatChunk001Sub000Block094 : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block094Part000
    + surrogateDiagTailX0RatChunk001Sub000Block094Part001
    + surrogateDiagTailX0RatChunk001Sub000Block094Part002
    + surrogateDiagTailX0RatChunk001Sub000Block094Part003
    + surrogateDiagTailX0RatChunk001Sub000Block094Part004
    + surrogateDiagTailX0RatChunk001Sub000Block094Part005
    + surrogateDiagTailX0RatChunk001Sub000Block094Part006
    + surrogateDiagTailX0RatChunk001Sub000Block094Part007
    + surrogateDiagTailX0RatChunk001Sub000Block094Part008
    + surrogateDiagTailX0RatChunk001Sub000Block094Part009
    + surrogateDiagTailX0RatChunk001Sub000Block094Part010
    + surrogateDiagTailX0RatChunk001Sub000Block094Part011
    + surrogateDiagTailX0RatChunk001Sub000Block094Part012
    + surrogateDiagTailX0RatChunk001Sub000Block094Part013
    + surrogateDiagTailX0RatChunk001Sub000Block094Part014
    + surrogateDiagTailX0RatChunk001Sub000Block094Part015
    + surrogateDiagTailX0RatChunk001Sub000Block094Part016
    + surrogateDiagTailX0RatChunk001Sub000Block094Part017
    + surrogateDiagTailX0RatChunk001Sub000Block094Part018
    + surrogateDiagTailX0RatChunk001Sub000Block094Part019
    + surrogateDiagTailX0RatChunk001Sub000Block094Part020
    + surrogateDiagTailX0RatChunk001Sub000Block094Part021
    + surrogateDiagTailX0RatChunk001Sub000Block094Part022
    + surrogateDiagTailX0RatChunk001Sub000Block094Part023
    + surrogateDiagTailX0RatChunk001Sub000Block094Part024

theorem surrogateDiagTailX0RatChunk001Sub000Block094_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk001Sub000Block094Head + surrogateDiagTailX0RatChunk001Sub000Block094Mid + surrogateDiagTailX0RatChunk001Sub000Block094Tail =
      surrogateDiagTailX0RatChunk001Sub000Block094 := by
  unfold surrogateDiagTailX0RatChunk001Sub000Block094Head surrogateDiagTailX0RatChunk001Sub000Block094Mid surrogateDiagTailX0RatChunk001Sub000Block094Tail surrogateDiagTailX0RatChunk001Sub000Block094
  ring

def SurrogateDiagonalTailChunk001Sub000Block094HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block094HeadSum X0 = surrogateDiagTailX0RatChunk001Sub000Block094Head

def SurrogateDiagonalTailChunk001Sub000Block094MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block094MidSum X0 = surrogateDiagTailX0RatChunk001Sub000Block094Mid

def SurrogateDiagonalTailChunk001Sub000Block094TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block094TailSum X0 = surrogateDiagTailX0RatChunk001Sub000Block094Tail

theorem surrogateDiagonalTailChunk001Sub000Block094_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk001Sub000Block094HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk001Sub000Block094MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk001Sub000Block094TailCertificateAt X0) :
    surrogateDiagonalTailChunk001Sub000Block094Sum X0 = surrogateDiagTailX0RatChunk001Sub000Block094 := by
  unfold SurrogateDiagonalTailChunk001Sub000Block094HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk001Sub000Block094MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk001Sub000Block094TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk001Sub000Block094Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk001Sub000Block094_eq_head_add_mid_add_tail

/-- Block 095 covers tail-support indices [12375,12400) and q from 20405 to 20443. -/

def TailChunk001Sub000Block095Part000SupportExplicit : Finset ℕ :=
  ([20405] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block095Part000 : ℚ :=
  (2761263223 : ℚ) / 97052154950320128

def SurrogateDiagonalTailChunk001Sub000Block095Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20405
    = surrogateDiagTailX0RatChunk001Sub000Block095Part000

theorem surrogateDiagonalTailChunk001Sub000Block095Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block095Part000CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block095Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block095Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block095Part000CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block095Part000SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block095Part000] using hcert

def TailChunk001Sub000Block095Part001SupportExplicit : Finset ℕ :=
  ([20406] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block095Part001 : ℚ :=
  (379897733225 : ℚ) / 2108078968676557824

def SurrogateDiagonalTailChunk001Sub000Block095Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20406
    = surrogateDiagTailX0RatChunk001Sub000Block095Part001

theorem surrogateDiagonalTailChunk001Sub000Block095Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block095Part001CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block095Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block095Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block095Part001CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block095Part001SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block095Part001] using hcert

def TailChunk001Sub000Block095Part002SupportExplicit : Finset ℕ :=
  ([20407] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block095Part002 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block095Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20407
    = surrogateDiagTailX0RatChunk001Sub000Block095Part002

theorem surrogateDiagonalTailChunk001Sub000Block095Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block095Part002CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block095Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block095Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block095Part002CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block095Part002SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block095Part002] using hcert

def TailChunk001Sub000Block095Part003SupportExplicit : Finset ℕ :=
  ([20409] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block095Part003 : ℚ :=
  (1446162633725 : ℚ) / 42821645936216230464

def SurrogateDiagonalTailChunk001Sub000Block095Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20409
    = surrogateDiagTailX0RatChunk001Sub000Block095Part003

theorem surrogateDiagonalTailChunk001Sub000Block095Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block095Part003CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block095Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block095Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block095Part003CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block095Part003SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block095Part003] using hcert

def TailChunk001Sub000Block095Part004SupportExplicit : Finset ℕ :=
  ([20410] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block095Part004 : ℚ :=
  (76647048425 : ℚ) / 145578232425480192

def SurrogateDiagonalTailChunk001Sub000Block095Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20410
    = surrogateDiagTailX0RatChunk001Sub000Block095Part004

theorem surrogateDiagonalTailChunk001Sub000Block095Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block095Part004CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block095Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block095Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block095Part004CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block095Part004SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block095Part004] using hcert

def TailChunk001Sub000Block095Part005SupportExplicit : Finset ℕ :=
  ([20411] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block095Part005 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block095Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20411
    = surrogateDiagTailX0RatChunk001Sub000Block095Part005

theorem surrogateDiagonalTailChunk001Sub000Block095Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block095Part005CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block095Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block095Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block095Part005CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block095Part005SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block095Part005] using hcert

def TailChunk001Sub000Block095Part006SupportExplicit : Finset ℕ :=
  ([20413] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block095Part006 : ℚ :=
  (309046975 : ℚ) / 1420141148257124352

def SurrogateDiagonalTailChunk001Sub000Block095Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20413
    = surrogateDiagTailX0RatChunk001Sub000Block095Part006

theorem surrogateDiagonalTailChunk001Sub000Block095Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block095Part006CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block095Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block095Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block095Part006CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block095Part006SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block095Part006] using hcert

def TailChunk001Sub000Block095Part007SupportExplicit : Finset ℕ :=
  ([20414] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block095Part007 : ℚ :=
  (1572674391925 : ℚ) / 6191453697738281472

def SurrogateDiagonalTailChunk001Sub000Block095Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20414
    = surrogateDiagTailX0RatChunk001Sub000Block095Part007

theorem surrogateDiagonalTailChunk001Sub000Block095Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block095Part007CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block095Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block095Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block095Part007CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block095Part007SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block095Part007] using hcert

def TailChunk001Sub000Block095Part008SupportExplicit : Finset ℕ :=
  ([20415] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block095Part008 : ℚ :=
  (25458387853 : ℚ) / 350382526876876800

def SurrogateDiagonalTailChunk001Sub000Block095Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20415
    = surrogateDiagTailX0RatChunk001Sub000Block095Part008

theorem surrogateDiagonalTailChunk001Sub000Block095Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block095Part008CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block095Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block095Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block095Part008CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block095Part008SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block095Part008] using hcert

def TailChunk001Sub000Block095Part009SupportExplicit : Finset ℕ :=
  ([20417] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block095Part009 : ℚ :=
  (14591312683 : ℚ) / 13592262868992000000

def SurrogateDiagonalTailChunk001Sub000Block095Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20417
    = surrogateDiagTailX0RatChunk001Sub000Block095Part009

theorem surrogateDiagonalTailChunk001Sub000Block095Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block095Part009CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block095Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block095Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block095Part009CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block095Part009SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block095Part009] using hcert

def TailChunk001Sub000Block095Part010SupportExplicit : Finset ℕ :=
  ([20418] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block095Part010 : ℚ :=
  (6870333347 : ℚ) / 9261305535528960

def SurrogateDiagonalTailChunk001Sub000Block095Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20418
    = surrogateDiagTailX0RatChunk001Sub000Block095Part010

theorem surrogateDiagonalTailChunk001Sub000Block095Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block095Part010CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block095Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block095Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block095Part010CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block095Part010SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block095Part010] using hcert

def TailChunk001Sub000Block095Part011SupportExplicit : Finset ℕ :=
  ([20419] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block095Part011 : ℚ :=
  (532272128375 : ℚ) / 117152603204874200064

def SurrogateDiagonalTailChunk001Sub000Block095Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20419
    = surrogateDiagTailX0RatChunk001Sub000Block095Part011

theorem surrogateDiagonalTailChunk001Sub000Block095Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block095Part011CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block095Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block095Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block095Part011CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block095Part011SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block095Part011] using hcert

def TailChunk001Sub000Block095Part012SupportExplicit : Finset ℕ :=
  ([20422] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block095Part012 : ℚ :=
  (2606613025 : ℚ) / 10869005751286962

def SurrogateDiagonalTailChunk001Sub000Block095Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20422
    = surrogateDiagTailX0RatChunk001Sub000Block095Part012

theorem surrogateDiagonalTailChunk001Sub000Block095Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block095Part012CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block095Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block095Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block095Part012CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block095Part012SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block095Part012] using hcert

def TailChunk001Sub000Block095Part013SupportExplicit : Finset ℕ :=
  ([20423] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block095Part013 : ℚ :=
  (582171401 : ℚ) / 393786175734849600

def SurrogateDiagonalTailChunk001Sub000Block095Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20423
    = surrogateDiagTailX0RatChunk001Sub000Block095Part013

theorem surrogateDiagonalTailChunk001Sub000Block095Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block095Part013CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block095Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block095Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block095Part013CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block095Part013SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block095Part013] using hcert

def TailChunk001Sub000Block095Part014SupportExplicit : Finset ℕ :=
  ([20426] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block095Part014 : ℚ :=
  (288012146075 : ℚ) / 813559744478293056

def SurrogateDiagonalTailChunk001Sub000Block095Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20426
    = surrogateDiagTailX0RatChunk001Sub000Block095Part014

theorem surrogateDiagonalTailChunk001Sub000Block095Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block095Part014CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block095Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block095Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block095Part014CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block095Part014SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block095Part014] using hcert

def TailChunk001Sub000Block095Part015SupportExplicit : Finset ℕ :=
  ([20427] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block095Part015 : ℚ :=
  (108149774383 : ℚ) / 2334321839429683200

def SurrogateDiagonalTailChunk001Sub000Block095Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20427
    = surrogateDiagTailX0RatChunk001Sub000Block095Part015

theorem surrogateDiagonalTailChunk001Sub000Block095Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block095Part015CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block095Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block095Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block095Part015CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block095Part015SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block095Part015] using hcert

def TailChunk001Sub000Block095Part016SupportExplicit : Finset ℕ :=
  ([20429] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block095Part016 : ℚ :=
  (7517977 : ℚ) / 12655933888121496

def SurrogateDiagonalTailChunk001Sub000Block095Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20429
    = surrogateDiagTailX0RatChunk001Sub000Block095Part016

theorem surrogateDiagonalTailChunk001Sub000Block095Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block095Part016CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block095Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block095Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block095Part016CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block095Part016SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block095Part016] using hcert

def TailChunk001Sub000Block095Part017SupportExplicit : Finset ℕ :=
  ([20431] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block095Part017 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block095Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20431
    = surrogateDiagTailX0RatChunk001Sub000Block095Part017

theorem surrogateDiagonalTailChunk001Sub000Block095Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block095Part017CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block095Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block095Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block095Part017CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block095Part017SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block095Part017] using hcert

def TailChunk001Sub000Block095Part018SupportExplicit : Finset ℕ :=
  ([20434] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block095Part018 : ℚ :=
  (237835254493 : ℚ) / 849516429312000000

def SurrogateDiagonalTailChunk001Sub000Block095Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20434
    = surrogateDiagTailX0RatChunk001Sub000Block095Part018

theorem surrogateDiagonalTailChunk001Sub000Block095Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block095Part018CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block095Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block095Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block095Part018CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block095Part018SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block095Part018] using hcert

def TailChunk001Sub000Block095Part019SupportExplicit : Finset ℕ :=
  ([20435] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block095Part019 : ℚ :=
  (4127166569 : ℚ) / 572420098503475200

def SurrogateDiagonalTailChunk001Sub000Block095Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20435
    = surrogateDiagTailX0RatChunk001Sub000Block095Part019

theorem surrogateDiagonalTailChunk001Sub000Block095Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block095Part019CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block095Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block095Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block095Part019CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block095Part019SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block095Part019] using hcert

def TailChunk001Sub000Block095Part020SupportExplicit : Finset ℕ :=
  ([20437] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block095Part020 : ℚ :=
  (229207237 : ℚ) / 1028501033475880200

def SurrogateDiagonalTailChunk001Sub000Block095Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20437
    = surrogateDiagTailX0RatChunk001Sub000Block095Part020

theorem surrogateDiagonalTailChunk001Sub000Block095Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block095Part020CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block095Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block095Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block095Part020CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block095Part020SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block095Part020] using hcert

def TailChunk001Sub000Block095Part021SupportExplicit : Finset ℕ :=
  ([20438] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block095Part021 : ℚ :=
  (224061989089 : ℚ) / 741786209432371200

def SurrogateDiagonalTailChunk001Sub000Block095Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20438
    = surrogateDiagTailX0RatChunk001Sub000Block095Part021

theorem surrogateDiagonalTailChunk001Sub000Block095Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block095Part021CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block095Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block095Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block095Part021CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block095Part021SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block095Part021] using hcert

def TailChunk001Sub000Block095Part022SupportExplicit : Finset ℕ :=
  ([20441] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block095Part022 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block095Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20441
    = surrogateDiagTailX0RatChunk001Sub000Block095Part022

theorem surrogateDiagonalTailChunk001Sub000Block095Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block095Part022CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block095Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block095Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block095Part022CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block095Part022SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block095Part022] using hcert

def TailChunk001Sub000Block095Part023SupportExplicit : Finset ℕ :=
  ([20442] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block095Part023 : ℚ :=
  (906616536025 : ℚ) / 1346063117780757792

def SurrogateDiagonalTailChunk001Sub000Block095Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20442
    = surrogateDiagTailX0RatChunk001Sub000Block095Part023

theorem surrogateDiagonalTailChunk001Sub000Block095Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block095Part023CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block095Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block095Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block095Part023CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block095Part023SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block095Part023] using hcert

def TailChunk001Sub000Block095Part024SupportExplicit : Finset ℕ :=
  ([20443] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block095Part024 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block095Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20443
    = surrogateDiagTailX0RatChunk001Sub000Block095Part024

theorem surrogateDiagonalTailChunk001Sub000Block095Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block095Part024CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block095Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block095Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block095Part024CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block095Part024SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block095Part024] using hcert

def surrogateDiagonalTailChunk001Sub000Block095HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block095Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block095Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block095Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block095Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block095Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block095Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block095Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block095Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block095Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block095Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block095Head : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block095Part000
    + surrogateDiagTailX0RatChunk001Sub000Block095Part001
    + surrogateDiagTailX0RatChunk001Sub000Block095Part002
    + surrogateDiagTailX0RatChunk001Sub000Block095Part003
    + surrogateDiagTailX0RatChunk001Sub000Block095Part004
    + surrogateDiagTailX0RatChunk001Sub000Block095Part005
    + surrogateDiagTailX0RatChunk001Sub000Block095Part006
    + surrogateDiagTailX0RatChunk001Sub000Block095Part007
    + surrogateDiagTailX0RatChunk001Sub000Block095Part008
    + surrogateDiagTailX0RatChunk001Sub000Block095Part009

def surrogateDiagonalTailChunk001Sub000Block095MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block095Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block095Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block095Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block095Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block095Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block095Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block095Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block095Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block095Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block095Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block095Mid : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block095Part010
    + surrogateDiagTailX0RatChunk001Sub000Block095Part011
    + surrogateDiagTailX0RatChunk001Sub000Block095Part012
    + surrogateDiagTailX0RatChunk001Sub000Block095Part013
    + surrogateDiagTailX0RatChunk001Sub000Block095Part014
    + surrogateDiagTailX0RatChunk001Sub000Block095Part015
    + surrogateDiagTailX0RatChunk001Sub000Block095Part016
    + surrogateDiagTailX0RatChunk001Sub000Block095Part017
    + surrogateDiagTailX0RatChunk001Sub000Block095Part018
    + surrogateDiagTailX0RatChunk001Sub000Block095Part019

def surrogateDiagonalTailChunk001Sub000Block095TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block095Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block095Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block095Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block095Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block095Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block095Tail : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block095Part020
    + surrogateDiagTailX0RatChunk001Sub000Block095Part021
    + surrogateDiagTailX0RatChunk001Sub000Block095Part022
    + surrogateDiagTailX0RatChunk001Sub000Block095Part023
    + surrogateDiagTailX0RatChunk001Sub000Block095Part024

def surrogateDiagonalTailChunk001Sub000Block095Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk001Sub000Block095HeadSum X0
    + surrogateDiagonalTailChunk001Sub000Block095MidSum X0
    + surrogateDiagonalTailChunk001Sub000Block095TailSum X0

def surrogateDiagTailX0RatChunk001Sub000Block095 : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block095Part000
    + surrogateDiagTailX0RatChunk001Sub000Block095Part001
    + surrogateDiagTailX0RatChunk001Sub000Block095Part002
    + surrogateDiagTailX0RatChunk001Sub000Block095Part003
    + surrogateDiagTailX0RatChunk001Sub000Block095Part004
    + surrogateDiagTailX0RatChunk001Sub000Block095Part005
    + surrogateDiagTailX0RatChunk001Sub000Block095Part006
    + surrogateDiagTailX0RatChunk001Sub000Block095Part007
    + surrogateDiagTailX0RatChunk001Sub000Block095Part008
    + surrogateDiagTailX0RatChunk001Sub000Block095Part009
    + surrogateDiagTailX0RatChunk001Sub000Block095Part010
    + surrogateDiagTailX0RatChunk001Sub000Block095Part011
    + surrogateDiagTailX0RatChunk001Sub000Block095Part012
    + surrogateDiagTailX0RatChunk001Sub000Block095Part013
    + surrogateDiagTailX0RatChunk001Sub000Block095Part014
    + surrogateDiagTailX0RatChunk001Sub000Block095Part015
    + surrogateDiagTailX0RatChunk001Sub000Block095Part016
    + surrogateDiagTailX0RatChunk001Sub000Block095Part017
    + surrogateDiagTailX0RatChunk001Sub000Block095Part018
    + surrogateDiagTailX0RatChunk001Sub000Block095Part019
    + surrogateDiagTailX0RatChunk001Sub000Block095Part020
    + surrogateDiagTailX0RatChunk001Sub000Block095Part021
    + surrogateDiagTailX0RatChunk001Sub000Block095Part022
    + surrogateDiagTailX0RatChunk001Sub000Block095Part023
    + surrogateDiagTailX0RatChunk001Sub000Block095Part024

theorem surrogateDiagTailX0RatChunk001Sub000Block095_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk001Sub000Block095Head + surrogateDiagTailX0RatChunk001Sub000Block095Mid + surrogateDiagTailX0RatChunk001Sub000Block095Tail =
      surrogateDiagTailX0RatChunk001Sub000Block095 := by
  unfold surrogateDiagTailX0RatChunk001Sub000Block095Head surrogateDiagTailX0RatChunk001Sub000Block095Mid surrogateDiagTailX0RatChunk001Sub000Block095Tail surrogateDiagTailX0RatChunk001Sub000Block095
  ring

def SurrogateDiagonalTailChunk001Sub000Block095HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block095HeadSum X0 = surrogateDiagTailX0RatChunk001Sub000Block095Head

def SurrogateDiagonalTailChunk001Sub000Block095MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block095MidSum X0 = surrogateDiagTailX0RatChunk001Sub000Block095Mid

def SurrogateDiagonalTailChunk001Sub000Block095TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block095TailSum X0 = surrogateDiagTailX0RatChunk001Sub000Block095Tail

theorem surrogateDiagonalTailChunk001Sub000Block095_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk001Sub000Block095HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk001Sub000Block095MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk001Sub000Block095TailCertificateAt X0) :
    surrogateDiagonalTailChunk001Sub000Block095Sum X0 = surrogateDiagTailX0RatChunk001Sub000Block095 := by
  unfold SurrogateDiagonalTailChunk001Sub000Block095HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk001Sub000Block095MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk001Sub000Block095TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk001Sub000Block095Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk001Sub000Block095_eq_head_add_mid_add_tail

/-- Block 096 covers tail-support indices [12400,12425) and q from 20445 to 20485. -/

def TailChunk001Sub000Block096Part000SupportExplicit : Finset ℕ :=
  ([20445] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block096Part000 : ℚ :=
  (2456827221775 : ℚ) / 28187091089152278528

def SurrogateDiagonalTailChunk001Sub000Block096Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20445
    = surrogateDiagTailX0RatChunk001Sub000Block096Part000

theorem surrogateDiagonalTailChunk001Sub000Block096Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block096Part000CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block096Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block096Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block096Part000CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block096Part000SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block096Part000] using hcert

def TailChunk001Sub000Block096Part001SupportExplicit : Finset ℕ :=
  ([20446] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block096Part001 : ℚ :=
  (1632964515625 : ℚ) / 6825121295579264082

def SurrogateDiagonalTailChunk001Sub000Block096Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20446
    = surrogateDiagTailX0RatChunk001Sub000Block096Part001

theorem surrogateDiagonalTailChunk001Sub000Block096Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block096Part001CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block096Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block096Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block096Part001CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block096Part001SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block096Part001] using hcert

def TailChunk001Sub000Block096Part002SupportExplicit : Finset ℕ :=
  ([20447] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block096Part002 : ℚ :=
  (34885307575 : ℚ) / 8697252591957371904

def SurrogateDiagonalTailChunk001Sub000Block096Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20447
    = surrogateDiagTailX0RatChunk001Sub000Block096Part002

theorem surrogateDiagonalTailChunk001Sub000Block096Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block096Part002CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block096Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block096Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block096Part002CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block096Part002SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block096Part002] using hcert

def TailChunk001Sub000Block096Part003SupportExplicit : Finset ℕ :=
  ([20451] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block096Part003 : ℚ :=
  (112401052303 : ℚ) / 2684891430912000000

def SurrogateDiagonalTailChunk001Sub000Block096Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20451
    = surrogateDiagTailX0RatChunk001Sub000Block096Part003

theorem surrogateDiagonalTailChunk001Sub000Block096Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block096Part003CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block096Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block096Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block096Part003CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block096Part003SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block096Part003] using hcert

def TailChunk001Sub000Block096Part004SupportExplicit : Finset ℕ :=
  ([20453] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block096Part004 : ℚ :=
  (1026503 : ℚ) / 4609788077260800

def SurrogateDiagonalTailChunk001Sub000Block096Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20453
    = surrogateDiagTailX0RatChunk001Sub000Block096Part004

theorem surrogateDiagonalTailChunk001Sub000Block096Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block096Part004CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block096Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block096Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block096Part004CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block096Part004SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block096Part004] using hcert

def TailChunk001Sub000Block096Part005SupportExplicit : Finset ℕ :=
  ([20454] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block096Part005 : ℚ :=
  (1433998518725 : ℚ) / 1446328434628076544

def SurrogateDiagonalTailChunk001Sub000Block096Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20454
    = surrogateDiagTailX0RatChunk001Sub000Block096Part005

theorem surrogateDiagonalTailChunk001Sub000Block096Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block096Part005CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block096Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block096Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block096Part005CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block096Part005SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block096Part005] using hcert

def TailChunk001Sub000Block096Part006SupportExplicit : Finset ℕ :=
  ([20455] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block096Part006 : ℚ :=
  (2791351803 : ℚ) / 477670904278906880

def SurrogateDiagonalTailChunk001Sub000Block096Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20455
    = surrogateDiagTailX0RatChunk001Sub000Block096Part006

theorem surrogateDiagonalTailChunk001Sub000Block096Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block096Part006CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block096Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block096Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block096Part006CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block096Part006SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block096Part006] using hcert

def TailChunk001Sub000Block096Part007SupportExplicit : Finset ℕ :=
  ([20458] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block096Part007 : ℚ :=
  (1576183201825 : ℚ) / 6211337916820488192

def SurrogateDiagonalTailChunk001Sub000Block096Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20458
    = surrogateDiagTailX0RatChunk001Sub000Block096Part007

theorem surrogateDiagonalTailChunk001Sub000Block096Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block096Part007CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block096Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block096Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block096Part007CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block096Part007SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block096Part007] using hcert

def TailChunk001Sub000Block096Part008SupportExplicit : Finset ℕ :=
  ([20459] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block096Part008 : ℚ :=
  (3344578757 : ℚ) / 7874340507238809600

def SurrogateDiagonalTailChunk001Sub000Block096Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20459
    = surrogateDiagTailX0RatChunk001Sub000Block096Part008

theorem surrogateDiagonalTailChunk001Sub000Block096Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block096Part008CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block096Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block096Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block096Part008CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block096Part008SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block096Part008] using hcert

def TailChunk001Sub000Block096Part009SupportExplicit : Finset ℕ :=
  ([20461] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block096Part009 : ℚ :=
  (702716986825 : ℚ) / 201474587027160465408

def SurrogateDiagonalTailChunk001Sub000Block096Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20461
    = surrogateDiagTailX0RatChunk001Sub000Block096Part009

theorem surrogateDiagonalTailChunk001Sub000Block096Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block096Part009CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block096Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block096Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block096Part009CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block096Part009SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block096Part009] using hcert

def TailChunk001Sub000Block096Part010SupportExplicit : Finset ℕ :=
  ([20462] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block096Part010 : ℚ :=
  (639749113175 : ℚ) / 2198869816294213632

def SurrogateDiagonalTailChunk001Sub000Block096Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20462
    = surrogateDiagTailX0RatChunk001Sub000Block096Part010

theorem surrogateDiagonalTailChunk001Sub000Block096Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block096Part010CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block096Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block096Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block096Part010CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block096Part010SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block096Part010] using hcert

def TailChunk001Sub000Block096Part011SupportExplicit : Finset ℕ :=
  ([20463] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block096Part011 : ℚ :=
  (2806912252825 : ℚ) / 68987271488098387968

def SurrogateDiagonalTailChunk001Sub000Block096Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20463
    = surrogateDiagTailX0RatChunk001Sub000Block096Part011

theorem surrogateDiagonalTailChunk001Sub000Block096Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block096Part011CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block096Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block096Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block096Part011CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block096Part011SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block096Part011] using hcert

def TailChunk001Sub000Block096Part012SupportExplicit : Finset ℕ :=
  ([20465] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block096Part012 : ℚ :=
  (1047779675875 : ℚ) / 179477216039824293888

def SurrogateDiagonalTailChunk001Sub000Block096Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20465
    = surrogateDiagTailX0RatChunk001Sub000Block096Part012

theorem surrogateDiagonalTailChunk001Sub000Block096Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block096Part012CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block096Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block096Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block096Part012CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block096Part012SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block096Part012] using hcert

def TailChunk001Sub000Block096Part013SupportExplicit : Finset ℕ :=
  ([20467] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block096Part013 : ℚ :=
  (1922061527 : ℚ) / 8260740234451353600

def SurrogateDiagonalTailChunk001Sub000Block096Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20467
    = surrogateDiagTailX0RatChunk001Sub000Block096Part013

theorem surrogateDiagonalTailChunk001Sub000Block096Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block096Part013CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block096Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block096Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block096Part013CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block096Part013SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block096Part013] using hcert

def TailChunk001Sub000Block096Part014SupportExplicit : Finset ℕ :=
  ([20469] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block096Part014 : ℚ :=
  (1454677633475 : ℚ) / 43327507505144399424

def SurrogateDiagonalTailChunk001Sub000Block096Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20469
    = surrogateDiagTailX0RatChunk001Sub000Block096Part014

theorem surrogateDiagonalTailChunk001Sub000Block096Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block096Part014CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block096Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block096Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block096Part014CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block096Part014SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block096Part014] using hcert

def TailChunk001Sub000Block096Part015SupportExplicit : Finset ℕ :=
  ([20470] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block096Part015 : ℚ :=
  (4109103222625 : ℚ) / 8992661292762267648

def SurrogateDiagonalTailChunk001Sub000Block096Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20470
    = surrogateDiagTailX0RatChunk001Sub000Block096Part015

theorem surrogateDiagonalTailChunk001Sub000Block096Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block096Part015CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block096Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block096Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block096Part015CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block096Part015SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block096Part015] using hcert

def TailChunk001Sub000Block096Part016SupportExplicit : Finset ℕ :=
  ([20471] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block096Part016 : ℚ :=
  (26061714637 : ℚ) / 11971225926432000000

def SurrogateDiagonalTailChunk001Sub000Block096Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20471
    = surrogateDiagTailX0RatChunk001Sub000Block096Part016

theorem surrogateDiagonalTailChunk001Sub000Block096Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block096Part016CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block096Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block096Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block096Part016CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block096Part016SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block096Part016] using hcert

def TailChunk001Sub000Block096Part017SupportExplicit : Finset ℕ :=
  ([20473] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block096Part017 : ℚ :=
  (65048460125 : ℚ) / 202774450250620705344

def SurrogateDiagonalTailChunk001Sub000Block096Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20473
    = surrogateDiagTailX0RatChunk001Sub000Block096Part017

theorem surrogateDiagonalTailChunk001Sub000Block096Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block096Part017CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block096Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block096Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block096Part017CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block096Part017SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block096Part017] using hcert

def TailChunk001Sub000Block096Part018SupportExplicit : Finset ℕ :=
  ([20474] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block096Part018 : ℚ :=
  (772691492975 : ℚ) / 2949440579731193856

def SurrogateDiagonalTailChunk001Sub000Block096Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20474
    = surrogateDiagTailX0RatChunk001Sub000Block096Part018

theorem surrogateDiagonalTailChunk001Sub000Block096Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block096Part018CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block096Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block096Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block096Part018CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block096Part018SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block096Part018] using hcert

def TailChunk001Sub000Block096Part019SupportExplicit : Finset ℕ :=
  ([20477] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block096Part019 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block096Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20477
    = surrogateDiagTailX0RatChunk001Sub000Block096Part019

theorem surrogateDiagonalTailChunk001Sub000Block096Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block096Part019CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block096Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block096Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block096Part019CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block096Part019SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block096Part019] using hcert

def TailChunk001Sub000Block096Part020SupportExplicit : Finset ℕ :=
  ([20478] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block096Part020 : ℚ :=
  (2911060658725 : ℚ) / 5422292376088332288

def SurrogateDiagonalTailChunk001Sub000Block096Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20478
    = surrogateDiagTailX0RatChunk001Sub000Block096Part020

theorem surrogateDiagonalTailChunk001Sub000Block096Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block096Part020CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block096Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block096Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block096Part020CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block096Part020SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block096Part020] using hcert

def TailChunk001Sub000Block096Part021SupportExplicit : Finset ℕ :=
  ([20479] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block096Part021 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block096Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20479
    = surrogateDiagTailX0RatChunk001Sub000Block096Part021

theorem surrogateDiagonalTailChunk001Sub000Block096Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block096Part021CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block096Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block096Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block096Part021CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block096Part021SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block096Part021] using hcert

def TailChunk001Sub000Block096Part022SupportExplicit : Finset ℕ :=
  ([20481] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block096Part022 : ℚ :=
  (125025 : ℚ) / 17368212447713408

def SurrogateDiagonalTailChunk001Sub000Block096Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20481
    = surrogateDiagTailX0RatChunk001Sub000Block096Part022

theorem surrogateDiagonalTailChunk001Sub000Block096Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block096Part022CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block096Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block096Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block096Part022CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block096Part022SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block096Part022] using hcert

def TailChunk001Sub000Block096Part023SupportExplicit : Finset ℕ :=
  ([20483] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block096Part023 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block096Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20483
    = surrogateDiagTailX0RatChunk001Sub000Block096Part023

theorem surrogateDiagonalTailChunk001Sub000Block096Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block096Part023CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block096Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block096Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block096Part023CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block096Part023SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block096Part023] using hcert

def TailChunk001Sub000Block096Part024SupportExplicit : Finset ℕ :=
  ([20485] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block096Part024 : ℚ :=
  (51342171217 : ℚ) / 5567390871139123200

def SurrogateDiagonalTailChunk001Sub000Block096Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20485
    = surrogateDiagTailX0RatChunk001Sub000Block096Part024

theorem surrogateDiagonalTailChunk001Sub000Block096Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block096Part024CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block096Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block096Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block096Part024CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block096Part024SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block096Part024] using hcert

def surrogateDiagonalTailChunk001Sub000Block096HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block096Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block096Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block096Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block096Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block096Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block096Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block096Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block096Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block096Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block096Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block096Head : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block096Part000
    + surrogateDiagTailX0RatChunk001Sub000Block096Part001
    + surrogateDiagTailX0RatChunk001Sub000Block096Part002
    + surrogateDiagTailX0RatChunk001Sub000Block096Part003
    + surrogateDiagTailX0RatChunk001Sub000Block096Part004
    + surrogateDiagTailX0RatChunk001Sub000Block096Part005
    + surrogateDiagTailX0RatChunk001Sub000Block096Part006
    + surrogateDiagTailX0RatChunk001Sub000Block096Part007
    + surrogateDiagTailX0RatChunk001Sub000Block096Part008
    + surrogateDiagTailX0RatChunk001Sub000Block096Part009

def surrogateDiagonalTailChunk001Sub000Block096MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block096Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block096Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block096Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block096Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block096Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block096Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block096Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block096Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block096Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block096Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block096Mid : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block096Part010
    + surrogateDiagTailX0RatChunk001Sub000Block096Part011
    + surrogateDiagTailX0RatChunk001Sub000Block096Part012
    + surrogateDiagTailX0RatChunk001Sub000Block096Part013
    + surrogateDiagTailX0RatChunk001Sub000Block096Part014
    + surrogateDiagTailX0RatChunk001Sub000Block096Part015
    + surrogateDiagTailX0RatChunk001Sub000Block096Part016
    + surrogateDiagTailX0RatChunk001Sub000Block096Part017
    + surrogateDiagTailX0RatChunk001Sub000Block096Part018
    + surrogateDiagTailX0RatChunk001Sub000Block096Part019

def surrogateDiagonalTailChunk001Sub000Block096TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block096Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block096Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block096Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block096Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block096Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block096Tail : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block096Part020
    + surrogateDiagTailX0RatChunk001Sub000Block096Part021
    + surrogateDiagTailX0RatChunk001Sub000Block096Part022
    + surrogateDiagTailX0RatChunk001Sub000Block096Part023
    + surrogateDiagTailX0RatChunk001Sub000Block096Part024

def surrogateDiagonalTailChunk001Sub000Block096Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk001Sub000Block096HeadSum X0
    + surrogateDiagonalTailChunk001Sub000Block096MidSum X0
    + surrogateDiagonalTailChunk001Sub000Block096TailSum X0

def surrogateDiagTailX0RatChunk001Sub000Block096 : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block096Part000
    + surrogateDiagTailX0RatChunk001Sub000Block096Part001
    + surrogateDiagTailX0RatChunk001Sub000Block096Part002
    + surrogateDiagTailX0RatChunk001Sub000Block096Part003
    + surrogateDiagTailX0RatChunk001Sub000Block096Part004
    + surrogateDiagTailX0RatChunk001Sub000Block096Part005
    + surrogateDiagTailX0RatChunk001Sub000Block096Part006
    + surrogateDiagTailX0RatChunk001Sub000Block096Part007
    + surrogateDiagTailX0RatChunk001Sub000Block096Part008
    + surrogateDiagTailX0RatChunk001Sub000Block096Part009
    + surrogateDiagTailX0RatChunk001Sub000Block096Part010
    + surrogateDiagTailX0RatChunk001Sub000Block096Part011
    + surrogateDiagTailX0RatChunk001Sub000Block096Part012
    + surrogateDiagTailX0RatChunk001Sub000Block096Part013
    + surrogateDiagTailX0RatChunk001Sub000Block096Part014
    + surrogateDiagTailX0RatChunk001Sub000Block096Part015
    + surrogateDiagTailX0RatChunk001Sub000Block096Part016
    + surrogateDiagTailX0RatChunk001Sub000Block096Part017
    + surrogateDiagTailX0RatChunk001Sub000Block096Part018
    + surrogateDiagTailX0RatChunk001Sub000Block096Part019
    + surrogateDiagTailX0RatChunk001Sub000Block096Part020
    + surrogateDiagTailX0RatChunk001Sub000Block096Part021
    + surrogateDiagTailX0RatChunk001Sub000Block096Part022
    + surrogateDiagTailX0RatChunk001Sub000Block096Part023
    + surrogateDiagTailX0RatChunk001Sub000Block096Part024

theorem surrogateDiagTailX0RatChunk001Sub000Block096_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk001Sub000Block096Head + surrogateDiagTailX0RatChunk001Sub000Block096Mid + surrogateDiagTailX0RatChunk001Sub000Block096Tail =
      surrogateDiagTailX0RatChunk001Sub000Block096 := by
  unfold surrogateDiagTailX0RatChunk001Sub000Block096Head surrogateDiagTailX0RatChunk001Sub000Block096Mid surrogateDiagTailX0RatChunk001Sub000Block096Tail surrogateDiagTailX0RatChunk001Sub000Block096
  ring

def SurrogateDiagonalTailChunk001Sub000Block096HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block096HeadSum X0 = surrogateDiagTailX0RatChunk001Sub000Block096Head

def SurrogateDiagonalTailChunk001Sub000Block096MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block096MidSum X0 = surrogateDiagTailX0RatChunk001Sub000Block096Mid

def SurrogateDiagonalTailChunk001Sub000Block096TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block096TailSum X0 = surrogateDiagTailX0RatChunk001Sub000Block096Tail

theorem surrogateDiagonalTailChunk001Sub000Block096_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk001Sub000Block096HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk001Sub000Block096MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk001Sub000Block096TailCertificateAt X0) :
    surrogateDiagonalTailChunk001Sub000Block096Sum X0 = surrogateDiagTailX0RatChunk001Sub000Block096 := by
  unfold SurrogateDiagonalTailChunk001Sub000Block096HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk001Sub000Block096MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk001Sub000Block096TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk001Sub000Block096Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk001Sub000Block096_eq_head_add_mid_add_tail

/-- Block 097 covers tail-support indices [12425,12450) and q from 20486 to 20523. -/

def TailChunk001Sub000Block097Part000SupportExplicit : Finset ℕ :=
  ([20486] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block097Part000 : ℚ :=
  (1639360140625 : ℚ) / 6878693419379967762

def SurrogateDiagonalTailChunk001Sub000Block097Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20486
    = surrogateDiagTailX0RatChunk001Sub000Block097Part000

theorem surrogateDiagonalTailChunk001Sub000Block097Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block097Part000CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block097Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block097Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block097Part000CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block097Part000SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block097Part000] using hcert

def TailChunk001Sub000Block097Part001SupportExplicit : Finset ℕ :=
  ([20487] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block097Part001 : ℚ :=
  (41675 : ℚ) / 5796192252450816

def SurrogateDiagonalTailChunk001Sub000Block097Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20487
    = surrogateDiagTailX0RatChunk001Sub000Block097Part001

theorem surrogateDiagonalTailChunk001Sub000Block097Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block097Part001CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block097Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block097Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block097Part001CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block097Part001SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block097Part001] using hcert

def TailChunk001Sub000Block097Part002SupportExplicit : Finset ℕ :=
  ([20489] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block097Part002 : ℚ :=
  (535922648375 : ℚ) / 118767920337993858624

def SurrogateDiagonalTailChunk001Sub000Block097Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20489
    = surrogateDiagTailX0RatChunk001Sub000Block097Part002

theorem surrogateDiagonalTailChunk001Sub000Block097Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block097Part002CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block097Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block097Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block097Part002CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block097Part002SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block097Part002] using hcert

def TailChunk001Sub000Block097Part003SupportExplicit : Finset ℕ :=
  ([20490] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block097Part003 : ℚ :=
  (1062170646575 : ℚ) / 1107884049628545024

def SurrogateDiagonalTailChunk001Sub000Block097Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20490
    = surrogateDiagTailX0RatChunk001Sub000Block097Part003

theorem surrogateDiagonalTailChunk001Sub000Block097Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block097Part003CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block097Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block097Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block097Part003CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block097Part003SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block097Part003] using hcert

def TailChunk001Sub000Block097Part004SupportExplicit : Finset ℕ :=
  ([20491] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block097Part004 : ℚ :=
  (16436777 : ℚ) / 31630884912000000

def SurrogateDiagonalTailChunk001Sub000Block097Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20491
    = surrogateDiagTailX0RatChunk001Sub000Block097Part004

theorem surrogateDiagonalTailChunk001Sub000Block097Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block097Part004CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block097Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block097Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block097Part004CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block097Part004SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block097Part004] using hcert

def TailChunk001Sub000Block097Part005SupportExplicit : Finset ℕ :=
  ([20494] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block097Part005 : ℚ :=
  (1640640765625 : ℚ) / 6889445575858863282

def SurrogateDiagonalTailChunk001Sub000Block097Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20494
    = surrogateDiagTailX0RatChunk001Sub000Block097Part005

theorem surrogateDiagonalTailChunk001Sub000Block097Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block097Part005CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block097Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block097Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block097Part005CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block097Part005SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block097Part005] using hcert

def TailChunk001Sub000Block097Part006SupportExplicit : Finset ℕ :=
  ([20495] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block097Part006 : ℚ :=
  (700010185075 : ℚ) / 60177395271653922816

def SurrogateDiagonalTailChunk001Sub000Block097Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20495
    = surrogateDiagTailX0RatChunk001Sub000Block097Part006

theorem surrogateDiagonalTailChunk001Sub000Block097Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block097Part006CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block097Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block097Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block097Part006CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block097Part006SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block097Part006] using hcert

def TailChunk001Sub000Block097Part007SupportExplicit : Finset ℕ :=
  ([20497] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block097Part007 : ℚ :=
  (170022925 : ℚ) / 764697036760647012

def SurrogateDiagonalTailChunk001Sub000Block097Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20497
    = surrogateDiagTailX0RatChunk001Sub000Block097Part007

theorem surrogateDiagonalTailChunk001Sub000Block097Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block097Part007CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block097Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block097Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block097Part007CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block097Part007SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block097Part007] using hcert

def TailChunk001Sub000Block097Part008SupportExplicit : Finset ℕ :=
  ([20498] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block097Part008 : ℚ :=
  (782906937875 : ℚ) / 3046373881388568576

def SurrogateDiagonalTailChunk001Sub000Block097Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20498
    = surrogateDiagTailX0RatChunk001Sub000Block097Part008

theorem surrogateDiagonalTailChunk001Sub000Block097Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block097Part008CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block097Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block097Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block097Part008CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block097Part008SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block097Part008] using hcert

def TailChunk001Sub000Block097Part009SupportExplicit : Finset ℕ :=
  ([20499] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block097Part009 : ℚ :=
  (125025 : ℚ) / 17429359095185408

def SurrogateDiagonalTailChunk001Sub000Block097Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20499
    = surrogateDiagTailX0RatChunk001Sub000Block097Part009

theorem surrogateDiagonalTailChunk001Sub000Block097Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block097Part009CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block097Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block097Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block097Part009CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block097Part009SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block097Part009] using hcert

def TailChunk001Sub000Block097Part010SupportExplicit : Finset ℕ :=
  ([20501] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block097Part010 : ℚ :=
  (16655057675 : ℚ) / 5126914036569839616

def SurrogateDiagonalTailChunk001Sub000Block097Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20501
    = surrogateDiagTailX0RatChunk001Sub000Block097Part010

theorem surrogateDiagonalTailChunk001Sub000Block097Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block097Part010CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block097Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block097Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block097Part010CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block097Part010SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block097Part010] using hcert

def TailChunk001Sub000Block097Part011SupportExplicit : Finset ℕ :=
  ([20503] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block097Part011 : ℚ :=
  (9714020579 : ℚ) / 1593506989670400000

def SurrogateDiagonalTailChunk001Sub000Block097Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20503
    = surrogateDiagTailX0RatChunk001Sub000Block097Part011

theorem surrogateDiagonalTailChunk001Sub000Block097Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block097Part011CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block097Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block097Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block097Part011CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block097Part011SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block097Part011] using hcert

def TailChunk001Sub000Block097Part012SupportExplicit : Finset ℕ :=
  ([20505] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block097Part012 : ℚ :=
  (48702624675 : ℚ) / 1485861611645775872

def SurrogateDiagonalTailChunk001Sub000Block097Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20505
    = surrogateDiagTailX0RatChunk001Sub000Block097Part012

theorem surrogateDiagonalTailChunk001Sub000Block097Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block097Part012CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block097Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block097Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block097Part012CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block097Part012SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block097Part012] using hcert

def TailChunk001Sub000Block097Part013SupportExplicit : Finset ℕ :=
  ([20506] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block097Part013 : ℚ :=
  (1642562640625 : ℚ) / 6905597438992894752

def SurrogateDiagonalTailChunk001Sub000Block097Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20506
    = surrogateDiagTailX0RatChunk001Sub000Block097Part013

theorem surrogateDiagonalTailChunk001Sub000Block097Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block097Part013CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block097Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block097Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block097Part013CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block097Part013SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block097Part013] using hcert

def TailChunk001Sub000Block097Part014SupportExplicit : Finset ℕ :=
  ([20507] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block097Part014 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block097Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20507
    = surrogateDiagTailX0RatChunk001Sub000Block097Part014

theorem surrogateDiagonalTailChunk001Sub000Block097Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block097Part014CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block097Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block097Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block097Part014CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block097Part014SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block097Part014] using hcert

def TailChunk001Sub000Block097Part015SupportExplicit : Finset ℕ :=
  ([20509] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block097Part015 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block097Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20509
    = surrogateDiagTailX0RatChunk001Sub000Block097Part015

theorem surrogateDiagonalTailChunk001Sub000Block097Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block097Part015CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block097Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block097Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block097Part015CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block097Part015SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block097Part015] using hcert

def TailChunk001Sub000Block097Part016SupportExplicit : Finset ℕ :=
  ([20510] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block097Part016 : ℚ :=
  (1847797236575 : ℚ) / 3015596536632705024

def SurrogateDiagonalTailChunk001Sub000Block097Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20510
    = surrogateDiagTailX0RatChunk001Sub000Block097Part016

theorem surrogateDiagonalTailChunk001Sub000Block097Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block097Part016CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block097Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block097Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block097Part016CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block097Part016SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block097Part016] using hcert

def TailChunk001Sub000Block097Part017SupportExplicit : Finset ℕ :=
  ([20513] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block097Part017 : ℚ :=
  (4409846593 : ℚ) / 16521480468902707200

def SurrogateDiagonalTailChunk001Sub000Block097Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20513
    = surrogateDiagTailX0RatChunk001Sub000Block097Part017

theorem surrogateDiagonalTailChunk001Sub000Block097Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block097Part017CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block097Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block097Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block097Part017CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block097Part017SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block097Part017] using hcert

def TailChunk001Sub000Block097Part018SupportExplicit : Finset ℕ :=
  ([20514] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block097Part018 : ℚ :=
  (1316559680375 : ℚ) / 1954550947817078784

def SurrogateDiagonalTailChunk001Sub000Block097Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20514
    = surrogateDiagTailX0RatChunk001Sub000Block097Part018

theorem surrogateDiagonalTailChunk001Sub000Block097Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block097Part018CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block097Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block097Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block097Part018CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block097Part018SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block097Part018] using hcert

def TailChunk001Sub000Block097Part019SupportExplicit : Finset ℕ :=
  ([20515] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block097Part019 : ℚ :=
  (5591195887 : ℚ) / 326894275964436480

def SurrogateDiagonalTailChunk001Sub000Block097Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20515
    = surrogateDiagTailX0RatChunk001Sub000Block097Part019

theorem surrogateDiagonalTailChunk001Sub000Block097Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block097Part019CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block097Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block097Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block097Part019CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block097Part019SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block097Part019] using hcert

def TailChunk001Sub000Block097Part020SupportExplicit : Finset ℕ :=
  ([20517] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block097Part020 : ℚ :=
  (658763984725 : ℚ) / 47049077628566765568

def SurrogateDiagonalTailChunk001Sub000Block097Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20517
    = surrogateDiagTailX0RatChunk001Sub000Block097Part020

theorem surrogateDiagonalTailChunk001Sub000Block097Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block097Part020CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block097Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block097Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block097Part020CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block097Part020SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block097Part020] using hcert

def TailChunk001Sub000Block097Part021SupportExplicit : Finset ℕ :=
  ([20518] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block097Part021 : ℚ :=
  (1644485640625 : ℚ) / 6921777685750215762

def SurrogateDiagonalTailChunk001Sub000Block097Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20518
    = surrogateDiagTailX0RatChunk001Sub000Block097Part021

theorem surrogateDiagonalTailChunk001Sub000Block097Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block097Part021CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block097Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block097Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block097Part021CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block097Part021SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block097Part021] using hcert

def TailChunk001Sub000Block097Part022SupportExplicit : Finset ℕ :=
  ([20521] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block097Part022 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block097Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20521
    = surrogateDiagTailX0RatChunk001Sub000Block097Part022

theorem surrogateDiagonalTailChunk001Sub000Block097Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block097Part022CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block097Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block097Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block097Part022CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block097Part022SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block097Part022] using hcert

def TailChunk001Sub000Block097Part023SupportExplicit : Finset ℕ :=
  ([20522] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block097Part023 : ℚ :=
  (411974099 : ℚ) / 1588079552400000

def SurrogateDiagonalTailChunk001Sub000Block097Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20522
    = surrogateDiagTailX0RatChunk001Sub000Block097Part023

theorem surrogateDiagonalTailChunk001Sub000Block097Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block097Part023CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block097Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block097Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block097Part023CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block097Part023SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block097Part023] using hcert

def TailChunk001Sub000Block097Part024SupportExplicit : Finset ℕ :=
  ([20523] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block097Part024 : ℚ :=
  (1667 : ℚ) / 233481852518400

def SurrogateDiagonalTailChunk001Sub000Block097Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20523
    = surrogateDiagTailX0RatChunk001Sub000Block097Part024

theorem surrogateDiagonalTailChunk001Sub000Block097Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block097Part024CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block097Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block097Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block097Part024CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block097Part024SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block097Part024] using hcert

def surrogateDiagonalTailChunk001Sub000Block097HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block097Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block097Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block097Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block097Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block097Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block097Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block097Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block097Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block097Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block097Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block097Head : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block097Part000
    + surrogateDiagTailX0RatChunk001Sub000Block097Part001
    + surrogateDiagTailX0RatChunk001Sub000Block097Part002
    + surrogateDiagTailX0RatChunk001Sub000Block097Part003
    + surrogateDiagTailX0RatChunk001Sub000Block097Part004
    + surrogateDiagTailX0RatChunk001Sub000Block097Part005
    + surrogateDiagTailX0RatChunk001Sub000Block097Part006
    + surrogateDiagTailX0RatChunk001Sub000Block097Part007
    + surrogateDiagTailX0RatChunk001Sub000Block097Part008
    + surrogateDiagTailX0RatChunk001Sub000Block097Part009

def surrogateDiagonalTailChunk001Sub000Block097MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block097Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block097Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block097Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block097Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block097Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block097Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block097Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block097Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block097Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block097Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block097Mid : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block097Part010
    + surrogateDiagTailX0RatChunk001Sub000Block097Part011
    + surrogateDiagTailX0RatChunk001Sub000Block097Part012
    + surrogateDiagTailX0RatChunk001Sub000Block097Part013
    + surrogateDiagTailX0RatChunk001Sub000Block097Part014
    + surrogateDiagTailX0RatChunk001Sub000Block097Part015
    + surrogateDiagTailX0RatChunk001Sub000Block097Part016
    + surrogateDiagTailX0RatChunk001Sub000Block097Part017
    + surrogateDiagTailX0RatChunk001Sub000Block097Part018
    + surrogateDiagTailX0RatChunk001Sub000Block097Part019

def surrogateDiagonalTailChunk001Sub000Block097TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block097Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block097Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block097Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block097Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block097Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block097Tail : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block097Part020
    + surrogateDiagTailX0RatChunk001Sub000Block097Part021
    + surrogateDiagTailX0RatChunk001Sub000Block097Part022
    + surrogateDiagTailX0RatChunk001Sub000Block097Part023
    + surrogateDiagTailX0RatChunk001Sub000Block097Part024

def surrogateDiagonalTailChunk001Sub000Block097Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk001Sub000Block097HeadSum X0
    + surrogateDiagonalTailChunk001Sub000Block097MidSum X0
    + surrogateDiagonalTailChunk001Sub000Block097TailSum X0

def surrogateDiagTailX0RatChunk001Sub000Block097 : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block097Part000
    + surrogateDiagTailX0RatChunk001Sub000Block097Part001
    + surrogateDiagTailX0RatChunk001Sub000Block097Part002
    + surrogateDiagTailX0RatChunk001Sub000Block097Part003
    + surrogateDiagTailX0RatChunk001Sub000Block097Part004
    + surrogateDiagTailX0RatChunk001Sub000Block097Part005
    + surrogateDiagTailX0RatChunk001Sub000Block097Part006
    + surrogateDiagTailX0RatChunk001Sub000Block097Part007
    + surrogateDiagTailX0RatChunk001Sub000Block097Part008
    + surrogateDiagTailX0RatChunk001Sub000Block097Part009
    + surrogateDiagTailX0RatChunk001Sub000Block097Part010
    + surrogateDiagTailX0RatChunk001Sub000Block097Part011
    + surrogateDiagTailX0RatChunk001Sub000Block097Part012
    + surrogateDiagTailX0RatChunk001Sub000Block097Part013
    + surrogateDiagTailX0RatChunk001Sub000Block097Part014
    + surrogateDiagTailX0RatChunk001Sub000Block097Part015
    + surrogateDiagTailX0RatChunk001Sub000Block097Part016
    + surrogateDiagTailX0RatChunk001Sub000Block097Part017
    + surrogateDiagTailX0RatChunk001Sub000Block097Part018
    + surrogateDiagTailX0RatChunk001Sub000Block097Part019
    + surrogateDiagTailX0RatChunk001Sub000Block097Part020
    + surrogateDiagTailX0RatChunk001Sub000Block097Part021
    + surrogateDiagTailX0RatChunk001Sub000Block097Part022
    + surrogateDiagTailX0RatChunk001Sub000Block097Part023
    + surrogateDiagTailX0RatChunk001Sub000Block097Part024

theorem surrogateDiagTailX0RatChunk001Sub000Block097_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk001Sub000Block097Head + surrogateDiagTailX0RatChunk001Sub000Block097Mid + surrogateDiagTailX0RatChunk001Sub000Block097Tail =
      surrogateDiagTailX0RatChunk001Sub000Block097 := by
  unfold surrogateDiagTailX0RatChunk001Sub000Block097Head surrogateDiagTailX0RatChunk001Sub000Block097Mid surrogateDiagTailX0RatChunk001Sub000Block097Tail surrogateDiagTailX0RatChunk001Sub000Block097
  ring

def SurrogateDiagonalTailChunk001Sub000Block097HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block097HeadSum X0 = surrogateDiagTailX0RatChunk001Sub000Block097Head

def SurrogateDiagonalTailChunk001Sub000Block097MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block097MidSum X0 = surrogateDiagTailX0RatChunk001Sub000Block097Mid

def SurrogateDiagonalTailChunk001Sub000Block097TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block097TailSum X0 = surrogateDiagTailX0RatChunk001Sub000Block097Tail

theorem surrogateDiagonalTailChunk001Sub000Block097_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk001Sub000Block097HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk001Sub000Block097MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk001Sub000Block097TailCertificateAt X0) :
    surrogateDiagonalTailChunk001Sub000Block097Sum X0 = surrogateDiagTailX0RatChunk001Sub000Block097 := by
  unfold SurrogateDiagonalTailChunk001Sub000Block097HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk001Sub000Block097MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk001Sub000Block097TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk001Sub000Block097Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk001Sub000Block097_eq_head_add_mid_add_tail

/-- Block 098 covers tail-support indices [12450,12475) and q from 20526 to 20567. -/

def TailChunk001Sub000Block098Part000SupportExplicit : Finset ℕ :=
  ([20526] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block098Part000 : ℚ :=
  (2588958451 : ℚ) / 3694822816800000

def SurrogateDiagonalTailChunk001Sub000Block098Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20526
    = surrogateDiagTailX0RatChunk001Sub000Block098Part000

theorem surrogateDiagonalTailChunk001Sub000Block098Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block098Part000CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block098Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block098Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block098Part000CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block098Part000SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block098Part000] using hcert

def TailChunk001Sub000Block098Part001SupportExplicit : Finset ℕ :=
  ([20527] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block098Part001 : ℚ :=
  (58807153475 : ℚ) / 40187394631074744576

def SurrogateDiagonalTailChunk001Sub000Block098Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20527
    = surrogateDiagTailX0RatChunk001Sub000Block098Part001

theorem surrogateDiagonalTailChunk001Sub000Block098Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block098Part001CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block098Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block098Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block098Part001CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block098Part001SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block098Part001] using hcert

def TailChunk001Sub000Block098Part002SupportExplicit : Finset ℕ :=
  ([20530] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block098Part002 : ℚ :=
  (4475544411775 : ℚ) / 11349487476000718848

def SurrogateDiagonalTailChunk001Sub000Block098Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20530
    = surrogateDiagTailX0RatChunk001Sub000Block098Part002

theorem surrogateDiagonalTailChunk001Sub000Block098Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block098Part002CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block098Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block098Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block098Part002CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block098Part002SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block098Part002] using hcert

def TailChunk001Sub000Block098Part003SupportExplicit : Finset ℕ :=
  ([20533] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block098Part003 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block098Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20533
    = surrogateDiagTailX0RatChunk001Sub000Block098Part003

theorem surrogateDiagonalTailChunk001Sub000Block098Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block098Part003CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block098Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block098Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block098Part003CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block098Part003SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block098Part003] using hcert

def TailChunk001Sub000Block098Part004SupportExplicit : Finset ℕ :=
  ([20534] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block098Part004 : ℚ :=
  (1647051390625 : ℚ) / 6943395557838491442

def SurrogateDiagonalTailChunk001Sub000Block098Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20534
    = surrogateDiagTailX0RatChunk001Sub000Block098Part004

theorem surrogateDiagonalTailChunk001Sub000Block098Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block098Part004CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block098Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block098Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block098Part004CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block098Part004SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block098Part004] using hcert

def TailChunk001Sub000Block098Part005SupportExplicit : Finset ℕ :=
  ([20537] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block098Part005 : ℚ :=
  (26229317443 : ℚ) / 12126442389453187200

def SurrogateDiagonalTailChunk001Sub000Block098Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20537
    = surrogateDiagTailX0RatChunk001Sub000Block098Part005

theorem surrogateDiagonalTailChunk001Sub000Block098Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block098Part005CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block098Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block098Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block098Part005CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block098Part005SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block098Part005] using hcert

def TailChunk001Sub000Block098Part006SupportExplicit : Finset ℕ :=
  ([20539] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block098Part006 : ℚ :=
  (118100407175 : ℚ) / 45886790120792214528

def SurrogateDiagonalTailChunk001Sub000Block098Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20539
    = surrogateDiagTailX0RatChunk001Sub000Block098Part006

theorem surrogateDiagonalTailChunk001Sub000Block098Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block098Part006CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block098Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block098Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block098Part006CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block098Part006SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block098Part006] using hcert

def TailChunk001Sub000Block098Part007SupportExplicit : Finset ℕ :=
  ([20541] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block098Part007 : ℚ :=
  (1212745873 : ℚ) / 777712642690252800

def SurrogateDiagonalTailChunk001Sub000Block098Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20541
    = surrogateDiagTailX0RatChunk001Sub000Block098Part007

theorem surrogateDiagonalTailChunk001Sub000Block098Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block098Part007CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block098Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block098Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block098Part007CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block098Part007SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block098Part007] using hcert

def TailChunk001Sub000Block098Part008SupportExplicit : Finset ℕ :=
  ([20542] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block098Part008 : ℚ :=
  (2637336025 : ℚ) / 11126757540936882

def SurrogateDiagonalTailChunk001Sub000Block098Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20542
    = surrogateDiagTailX0RatChunk001Sub000Block098Part008

theorem surrogateDiagonalTailChunk001Sub000Block098Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block098Part008CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block098Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block098Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block098Part008CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block098Part008SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block098Part008] using hcert

def TailChunk001Sub000Block098Part009SupportExplicit : Finset ℕ :=
  ([20543] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block098Part009 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block098Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20543
    = surrogateDiagTailX0RatChunk001Sub000Block098Part009

theorem surrogateDiagonalTailChunk001Sub000Block098Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block098Part009CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block098Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block098Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block098Part009CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block098Part009SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block098Part009] using hcert

def TailChunk001Sub000Block098Part010SupportExplicit : Finset ℕ :=
  ([20545] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block098Part010 : ℚ :=
  (1595750071375 : ℚ) / 97827800629899460608

def SurrogateDiagonalTailChunk001Sub000Block098Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20545
    = surrogateDiagTailX0RatChunk001Sub000Block098Part010

theorem surrogateDiagonalTailChunk001Sub000Block098Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block098Part010CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block098Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block098Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block098Part010CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block098Part010SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block098Part010] using hcert

def TailChunk001Sub000Block098Part011SupportExplicit : Finset ℕ :=
  ([20546] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block098Part011 : ℚ :=
  (1648977015625 : ℚ) / 6959642162322604032

def SurrogateDiagonalTailChunk001Sub000Block098Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20546
    = surrogateDiagTailX0RatChunk001Sub000Block098Part011

theorem surrogateDiagonalTailChunk001Sub000Block098Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block098Part011CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block098Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block098Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block098Part011CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block098Part011SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block098Part011] using hcert

def TailChunk001Sub000Block098Part012SupportExplicit : Finset ℕ :=
  ([20549] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block098Part012 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block098Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20549
    = surrogateDiagTailX0RatChunk001Sub000Block098Part012

theorem surrogateDiagonalTailChunk001Sub000Block098Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block098Part012CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block098Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block098Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block098Part012CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block098Part012SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block098Part012] using hcert

def TailChunk001Sub000Block098Part013SupportExplicit : Finset ℕ :=
  ([20551] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block098Part013 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block098Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20551
    = surrogateDiagTailX0RatChunk001Sub000Block098Part013

theorem surrogateDiagonalTailChunk001Sub000Block098Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block098Part013CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block098Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block098Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block098Part013CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block098Part013SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block098Part013] using hcert

def TailChunk001Sub000Block098Part014SupportExplicit : Finset ℕ :=
  ([20553] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block098Part014 : ℚ :=
  (5314862471 : ℚ) / 88077863391068160

def SurrogateDiagonalTailChunk001Sub000Block098Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20553
    = surrogateDiagTailX0RatChunk001Sub000Block098Part014

theorem surrogateDiagonalTailChunk001Sub000Block098Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block098Part014CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block098Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block098Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block098Part014CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block098Part014SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block098Part014] using hcert

def TailChunk001Sub000Block098Part015SupportExplicit : Finset ℕ :=
  ([20554] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block098Part015 : ℚ :=
  (451875020225 : ℚ) / 1783215428457097152

def SurrogateDiagonalTailChunk001Sub000Block098Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20554
    = surrogateDiagTailX0RatChunk001Sub000Block098Part015

theorem surrogateDiagonalTailChunk001Sub000Block098Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block098Part015CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block098Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block098Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block098Part015CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block098Part015SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block098Part015] using hcert

def TailChunk001Sub000Block098Part016SupportExplicit : Finset ℕ :=
  ([20555] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block098Part016 : ℚ :=
  (8456055389 : ℚ) / 1461248568414627840

def SurrogateDiagonalTailChunk001Sub000Block098Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20555
    = surrogateDiagTailX0RatChunk001Sub000Block098Part016

theorem surrogateDiagonalTailChunk001Sub000Block098Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block098Part016CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block098Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block098Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block098Part016CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block098Part016SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block098Part016] using hcert

def TailChunk001Sub000Block098Part017SupportExplicit : Finset ℕ :=
  ([20557] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block098Part017 : ℚ :=
  (1243018801 : ℚ) / 4130370117225676800

def SurrogateDiagonalTailChunk001Sub000Block098Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20557
    = surrogateDiagTailX0RatChunk001Sub000Block098Part017

theorem surrogateDiagonalTailChunk001Sub000Block098Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block098Part017CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block098Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block098Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block098Part017CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block098Part017SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block098Part017] using hcert

def TailChunk001Sub000Block098Part018SupportExplicit : Finset ℕ :=
  ([20558] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block098Part018 : ℚ :=
  (242285839711 : ℚ) / 892795330017331200

def SurrogateDiagonalTailChunk001Sub000Block098Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20558
    = surrogateDiagTailX0RatChunk001Sub000Block098Part018

theorem surrogateDiagonalTailChunk001Sub000Block098Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block098Part018CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block098Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block098Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block098Part018CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block098Part018SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block098Part018] using hcert

def TailChunk001Sub000Block098Part019SupportExplicit : Finset ℕ :=
  ([20559] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block098Part019 : ℚ :=
  (12205437173 : ℚ) / 155472125519462400

def SurrogateDiagonalTailChunk001Sub000Block098Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20559
    = surrogateDiagTailX0RatChunk001Sub000Block098Part019

theorem surrogateDiagonalTailChunk001Sub000Block098Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block098Part019CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block098Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block098Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block098Part019CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block098Part019SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block098Part019] using hcert

def TailChunk001Sub000Block098Part020SupportExplicit : Finset ℕ :=
  ([20561] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block098Part020 : ℚ :=
  (75923900075 : ℚ) / 128727329665730052096

def SurrogateDiagonalTailChunk001Sub000Block098Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20561
    = surrogateDiagTailX0RatChunk001Sub000Block098Part020

theorem surrogateDiagonalTailChunk001Sub000Block098Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block098Part020CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block098Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block098Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block098Part020CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block098Part020SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block098Part020] using hcert

def TailChunk001Sub000Block098Part021SupportExplicit : Finset ℕ :=
  ([20562] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block098Part021 : ℚ :=
  (3411919557325 : ℚ) / 4496601762896314368

def SurrogateDiagonalTailChunk001Sub000Block098Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20562
    = surrogateDiagTailX0RatChunk001Sub000Block098Part021

theorem surrogateDiagonalTailChunk001Sub000Block098Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block098Part021CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block098Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block098Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block098Part021CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block098Part021SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block098Part021] using hcert

def TailChunk001Sub000Block098Part022SupportExplicit : Finset ℕ :=
  ([20563] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block098Part022 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block098Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20563
    = surrogateDiagTailX0RatChunk001Sub000Block098Part022

theorem surrogateDiagonalTailChunk001Sub000Block098Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block098Part022CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block098Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block098Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block098Part022CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block098Part022SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block098Part022] using hcert

def TailChunk001Sub000Block098Part023SupportExplicit : Finset ℕ :=
  ([20566] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block098Part023 : ℚ :=
  (1120688651575 : ℚ) / 2643436875024433152

def SurrogateDiagonalTailChunk001Sub000Block098Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20566
    = surrogateDiagTailX0RatChunk001Sub000Block098Part023

theorem surrogateDiagonalTailChunk001Sub000Block098Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block098Part023CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block098Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block098Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block098Part023CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block098Part023SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block098Part023] using hcert

def TailChunk001Sub000Block098Part024SupportExplicit : Finset ℕ :=
  ([20567] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block098Part024 : ℚ :=
  (710441 : ℚ) / 3382998446131200

def SurrogateDiagonalTailChunk001Sub000Block098Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20567
    = surrogateDiagTailX0RatChunk001Sub000Block098Part024

theorem surrogateDiagonalTailChunk001Sub000Block098Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block098Part024CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block098Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block098Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block098Part024CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block098Part024SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block098Part024] using hcert

def surrogateDiagonalTailChunk001Sub000Block098HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block098Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block098Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block098Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block098Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block098Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block098Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block098Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block098Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block098Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block098Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block098Head : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block098Part000
    + surrogateDiagTailX0RatChunk001Sub000Block098Part001
    + surrogateDiagTailX0RatChunk001Sub000Block098Part002
    + surrogateDiagTailX0RatChunk001Sub000Block098Part003
    + surrogateDiagTailX0RatChunk001Sub000Block098Part004
    + surrogateDiagTailX0RatChunk001Sub000Block098Part005
    + surrogateDiagTailX0RatChunk001Sub000Block098Part006
    + surrogateDiagTailX0RatChunk001Sub000Block098Part007
    + surrogateDiagTailX0RatChunk001Sub000Block098Part008
    + surrogateDiagTailX0RatChunk001Sub000Block098Part009

def surrogateDiagonalTailChunk001Sub000Block098MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block098Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block098Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block098Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block098Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block098Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block098Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block098Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block098Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block098Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block098Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block098Mid : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block098Part010
    + surrogateDiagTailX0RatChunk001Sub000Block098Part011
    + surrogateDiagTailX0RatChunk001Sub000Block098Part012
    + surrogateDiagTailX0RatChunk001Sub000Block098Part013
    + surrogateDiagTailX0RatChunk001Sub000Block098Part014
    + surrogateDiagTailX0RatChunk001Sub000Block098Part015
    + surrogateDiagTailX0RatChunk001Sub000Block098Part016
    + surrogateDiagTailX0RatChunk001Sub000Block098Part017
    + surrogateDiagTailX0RatChunk001Sub000Block098Part018
    + surrogateDiagTailX0RatChunk001Sub000Block098Part019

def surrogateDiagonalTailChunk001Sub000Block098TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block098Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block098Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block098Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block098Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block098Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block098Tail : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block098Part020
    + surrogateDiagTailX0RatChunk001Sub000Block098Part021
    + surrogateDiagTailX0RatChunk001Sub000Block098Part022
    + surrogateDiagTailX0RatChunk001Sub000Block098Part023
    + surrogateDiagTailX0RatChunk001Sub000Block098Part024

def surrogateDiagonalTailChunk001Sub000Block098Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk001Sub000Block098HeadSum X0
    + surrogateDiagonalTailChunk001Sub000Block098MidSum X0
    + surrogateDiagonalTailChunk001Sub000Block098TailSum X0

def surrogateDiagTailX0RatChunk001Sub000Block098 : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block098Part000
    + surrogateDiagTailX0RatChunk001Sub000Block098Part001
    + surrogateDiagTailX0RatChunk001Sub000Block098Part002
    + surrogateDiagTailX0RatChunk001Sub000Block098Part003
    + surrogateDiagTailX0RatChunk001Sub000Block098Part004
    + surrogateDiagTailX0RatChunk001Sub000Block098Part005
    + surrogateDiagTailX0RatChunk001Sub000Block098Part006
    + surrogateDiagTailX0RatChunk001Sub000Block098Part007
    + surrogateDiagTailX0RatChunk001Sub000Block098Part008
    + surrogateDiagTailX0RatChunk001Sub000Block098Part009
    + surrogateDiagTailX0RatChunk001Sub000Block098Part010
    + surrogateDiagTailX0RatChunk001Sub000Block098Part011
    + surrogateDiagTailX0RatChunk001Sub000Block098Part012
    + surrogateDiagTailX0RatChunk001Sub000Block098Part013
    + surrogateDiagTailX0RatChunk001Sub000Block098Part014
    + surrogateDiagTailX0RatChunk001Sub000Block098Part015
    + surrogateDiagTailX0RatChunk001Sub000Block098Part016
    + surrogateDiagTailX0RatChunk001Sub000Block098Part017
    + surrogateDiagTailX0RatChunk001Sub000Block098Part018
    + surrogateDiagTailX0RatChunk001Sub000Block098Part019
    + surrogateDiagTailX0RatChunk001Sub000Block098Part020
    + surrogateDiagTailX0RatChunk001Sub000Block098Part021
    + surrogateDiagTailX0RatChunk001Sub000Block098Part022
    + surrogateDiagTailX0RatChunk001Sub000Block098Part023
    + surrogateDiagTailX0RatChunk001Sub000Block098Part024

theorem surrogateDiagTailX0RatChunk001Sub000Block098_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk001Sub000Block098Head + surrogateDiagTailX0RatChunk001Sub000Block098Mid + surrogateDiagTailX0RatChunk001Sub000Block098Tail =
      surrogateDiagTailX0RatChunk001Sub000Block098 := by
  unfold surrogateDiagTailX0RatChunk001Sub000Block098Head surrogateDiagTailX0RatChunk001Sub000Block098Mid surrogateDiagTailX0RatChunk001Sub000Block098Tail surrogateDiagTailX0RatChunk001Sub000Block098
  ring

def SurrogateDiagonalTailChunk001Sub000Block098HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block098HeadSum X0 = surrogateDiagTailX0RatChunk001Sub000Block098Head

def SurrogateDiagonalTailChunk001Sub000Block098MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block098MidSum X0 = surrogateDiagTailX0RatChunk001Sub000Block098Mid

def SurrogateDiagonalTailChunk001Sub000Block098TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block098TailSum X0 = surrogateDiagTailX0RatChunk001Sub000Block098Tail

theorem surrogateDiagonalTailChunk001Sub000Block098_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk001Sub000Block098HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk001Sub000Block098MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk001Sub000Block098TailCertificateAt X0) :
    surrogateDiagonalTailChunk001Sub000Block098Sum X0 = surrogateDiagTailX0RatChunk001Sub000Block098 := by
  unfold SurrogateDiagonalTailChunk001Sub000Block098HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk001Sub000Block098MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk001Sub000Block098TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk001Sub000Block098Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk001Sub000Block098_eq_head_add_mid_add_tail

/-- Block 099 covers tail-support indices [12475,12500) and q from 20569 to 20609. -/

def TailChunk001Sub000Block099Part000SupportExplicit : Finset ℕ :=
  ([20569] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block099Part000 : ℚ :=
  (114079946125 : ℚ) / 415995187997791974528

def SurrogateDiagonalTailChunk001Sub000Block099Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20569
    = surrogateDiagTailX0RatChunk001Sub000Block099Part000

theorem surrogateDiagonalTailChunk001Sub000Block099Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block099Part000CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block099Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block099Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block099Part000CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block099Part000SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block099Part000] using hcert

def TailChunk001Sub000Block099Part001SupportExplicit : Finset ℕ :=
  ([20571] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block099Part001 : ℚ :=
  (734605254025 : ℚ) / 22098870954709819392

def SurrogateDiagonalTailChunk001Sub000Block099Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20571
    = surrogateDiagTailX0RatChunk001Sub000Block099Part001

theorem surrogateDiagonalTailChunk001Sub000Block099Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block099Part001CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block099Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block099Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block099Part001CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block099Part001SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block099Part001] using hcert

def TailChunk001Sub000Block099Part002SupportExplicit : Finset ℕ :=
  ([20573] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block099Part002 : ℚ :=
  (41643472825 : ℚ) / 18573582275405629056

def SurrogateDiagonalTailChunk001Sub000Block099Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20573
    = surrogateDiagTailX0RatChunk001Sub000Block099Part002

theorem surrogateDiagonalTailChunk001Sub000Block099Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block099Part002CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block099Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block099Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block099Part002CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block099Part002SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block099Part002] using hcert

def TailChunk001Sub000Block099Part003SupportExplicit : Finset ℕ :=
  ([20578] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block099Part003 : ℚ :=
  (1654117515625 : ℚ) / 7003105837716283392

def SurrogateDiagonalTailChunk001Sub000Block099Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20578
    = surrogateDiagTailX0RatChunk001Sub000Block099Part003

theorem surrogateDiagonalTailChunk001Sub000Block099Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block099Part003CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block099Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block099Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block099Part003CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block099Part003SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block099Part003] using hcert

def TailChunk001Sub000Block099Part004SupportExplicit : Finset ℕ :=
  ([20579] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block099Part004 : ℚ :=
  (104843054275 : ℚ) / 54128564458502704128

def SurrogateDiagonalTailChunk001Sub000Block099Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20579
    = surrogateDiagTailX0RatChunk001Sub000Block099Part004

theorem surrogateDiagonalTailChunk001Sub000Block099Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block099Part004CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block099Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block099Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block099Part004CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block099Part004SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block099Part004] using hcert

def TailChunk001Sub000Block099Part005SupportExplicit : Finset ℕ :=
  ([20581] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block099Part005 : ℚ :=
  (1100382229 : ℚ) / 764422204495125000

def SurrogateDiagonalTailChunk001Sub000Block099Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20581
    = surrogateDiagTailX0RatChunk001Sub000Block099Part005

theorem surrogateDiagonalTailChunk001Sub000Block099Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block099Part005CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block099Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block099Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block099Part005CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block099Part005SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block099Part005] using hcert

def TailChunk001Sub000Block099Part006SupportExplicit : Finset ℕ :=
  ([20582] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block099Part006 : ℚ :=
  (25334407351 : ℚ) / 100020000000000000

def SurrogateDiagonalTailChunk001Sub000Block099Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20582
    = surrogateDiagTailX0RatChunk001Sub000Block099Part006

theorem surrogateDiagonalTailChunk001Sub000Block099Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block099Part006CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block099Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block099Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block099Part006CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block099Part006SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block099Part006] using hcert

def TailChunk001Sub000Block099Part007SupportExplicit : Finset ℕ :=
  ([20585] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block099Part007 : ℚ :=
  (1217804043625 : ℚ) / 150535024199450001408

def SurrogateDiagonalTailChunk001Sub000Block099Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20585
    = surrogateDiagTailX0RatChunk001Sub000Block099Part007

theorem surrogateDiagonalTailChunk001Sub000Block099Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block099Part007CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block099Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block099Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block099Part007CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block099Part007SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block099Part007] using hcert

def TailChunk001Sub000Block099Part008SupportExplicit : Finset ℕ :=
  ([20586] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block099Part008 : ℚ :=
  (1166032906825 : ℚ) / 1604674307891920896

def SurrogateDiagonalTailChunk001Sub000Block099Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20586
    = surrogateDiagTailX0RatChunk001Sub000Block099Part008

theorem surrogateDiagonalTailChunk001Sub000Block099Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block099Part008CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block099Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block099Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block099Part008CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block099Part008SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block099Part008] using hcert

def TailChunk001Sub000Block099Part009SupportExplicit : Finset ℕ :=
  ([20587] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block099Part009 : ℚ :=
  (439314013025 : ℚ) / 92938483777545437184

def SurrogateDiagonalTailChunk001Sub000Block099Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20587
    = surrogateDiagTailX0RatChunk001Sub000Block099Part009

theorem surrogateDiagonalTailChunk001Sub000Block099Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block099Part009CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block099Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block099Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block099Part009CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block099Part009SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block099Part009] using hcert

def TailChunk001Sub000Block099Part010SupportExplicit : Finset ℕ :=
  ([20589] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block099Part010 : ℚ :=
  (1471782632975 : ℚ) / 44352663012009351744

def SurrogateDiagonalTailChunk001Sub000Block099Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20589
    = surrogateDiagTailX0RatChunk001Sub000Block099Part010

theorem surrogateDiagonalTailChunk001Sub000Block099Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block099Part010CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block099Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block099Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block099Part010CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block099Part010SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block099Part010] using hcert

def TailChunk001Sub000Block099Part011SupportExplicit : Finset ℕ :=
  ([20590] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block099Part011 : ℚ :=
  (44364342481 : ℚ) / 94469389683916800

def SurrogateDiagonalTailChunk001Sub000Block099Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20590
    = surrogateDiagTailX0RatChunk001Sub000Block099Part011

theorem surrogateDiagonalTailChunk001Sub000Block099Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block099Part011CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block099Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block099Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block099Part011CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block099Part011SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block099Part011] using hcert

def TailChunk001Sub000Block099Part012SupportExplicit : Finset ℕ :=
  ([20591] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block099Part012 : ℚ :=
  (123868328725 : ℚ) / 415007369643325114368

def SurrogateDiagonalTailChunk001Sub000Block099Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20591
    = surrogateDiagTailX0RatChunk001Sub000Block099Part012

theorem surrogateDiagonalTailChunk001Sub000Block099Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block099Part012CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block099Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block099Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block099Part012CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block099Part012SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block099Part012] using hcert

def TailChunk001Sub000Block099Part013SupportExplicit : Finset ℕ :=
  ([20593] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block099Part013 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block099Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20593
    = surrogateDiagTailX0RatChunk001Sub000Block099Part013

theorem surrogateDiagonalTailChunk001Sub000Block099Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block099Part013CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block099Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block099Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block099Part013CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block099Part013SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block099Part013] using hcert

def TailChunk001Sub000Block099Part014SupportExplicit : Finset ℕ :=
  ([20594] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block099Part014 : ℚ :=
  (11710835111 : ℚ) / 33627043495886400

def SurrogateDiagonalTailChunk001Sub000Block099Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20594
    = surrogateDiagTailX0RatChunk001Sub000Block099Part014

theorem surrogateDiagonalTailChunk001Sub000Block099Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block099Part014CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block099Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block099Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block099Part014CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block099Part014SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block099Part014] using hcert

def TailChunk001Sub000Block099Part015SupportExplicit : Finset ℕ :=
  ([20595] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block099Part015 : ℚ :=
  (412172508375 : ℚ) / 6048560123495579648

def SurrogateDiagonalTailChunk001Sub000Block099Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20595
    = surrogateDiagTailX0RatChunk001Sub000Block099Part015

theorem surrogateDiagonalTailChunk001Sub000Block099Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block099Part015CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block099Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block099Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block099Part015CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block099Part015SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block099Part015] using hcert

def TailChunk001Sub000Block099Part016SupportExplicit : Finset ℕ :=
  ([20597] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block099Part016 : ℚ :=
  (42492406825 : ℚ) / 101548991706845290272

def SurrogateDiagonalTailChunk001Sub000Block099Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20597
    = surrogateDiagTailX0RatChunk001Sub000Block099Part016

theorem surrogateDiagonalTailChunk001Sub000Block099Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block099Part016CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block099Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block099Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block099Part016CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block099Part016SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block099Part016] using hcert

def TailChunk001Sub000Block099Part017SupportExplicit : Finset ℕ :=
  ([20598] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block099Part017 : ℚ :=
  (1841016891425 : ℚ) / 2775274610600853504

def SurrogateDiagonalTailChunk001Sub000Block099Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20598
    = surrogateDiagTailX0RatChunk001Sub000Block099Part017

theorem surrogateDiagonalTailChunk001Sub000Block099Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block099Part017CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block099Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block099Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block099Part017CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block099Part017SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block099Part017] using hcert

def TailChunk001Sub000Block099Part018SupportExplicit : Finset ℕ :=
  ([20599] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block099Part018 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block099Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20599
    = surrogateDiagTailX0RatChunk001Sub000Block099Part018

theorem surrogateDiagonalTailChunk001Sub000Block099Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block099Part018CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block099Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block099Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block099Part018CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block099Part018SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block099Part018] using hcert

def TailChunk001Sub000Block099Part019SupportExplicit : Finset ℕ :=
  ([20602] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block099Part019 : ℚ :=
  (106110601 : ℚ) / 450293564704800

def SurrogateDiagonalTailChunk001Sub000Block099Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20602
    = surrogateDiagTailX0RatChunk001Sub000Block099Part019

theorem surrogateDiagonalTailChunk001Sub000Block099Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block099Part019CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block099Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block099Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block099Part019CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block099Part019SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block099Part019] using hcert

def TailChunk001Sub000Block099Part020SupportExplicit : Finset ℕ :=
  ([20603] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block099Part020 : ℚ :=
  (26397460033 : ℚ) / 12283163360899891200

def SurrogateDiagonalTailChunk001Sub000Block099Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20603
    = surrogateDiagTailX0RatChunk001Sub000Block099Part020

theorem surrogateDiagonalTailChunk001Sub000Block099Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block099Part020CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block099Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block099Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block099Part020CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block099Part020SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block099Part020] using hcert

def TailChunk001Sub000Block099Part021SupportExplicit : Finset ℕ :=
  ([20605] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block099Part021 : ℚ :=
  (80515195825 : ℚ) / 8272183433133293568

def SurrogateDiagonalTailChunk001Sub000Block099Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20605
    = surrogateDiagTailX0RatChunk001Sub000Block099Part021

theorem surrogateDiagonalTailChunk001Sub000Block099Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block099Part021CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block099Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block099Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block099Part021CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block099Part021SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block099Part021] using hcert

def TailChunk001Sub000Block099Part022SupportExplicit : Finset ℕ :=
  ([20606] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block099Part022 : ℚ :=
  (1658622015625 : ℚ) / 7041303268113821202

def SurrogateDiagonalTailChunk001Sub000Block099Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20606
    = surrogateDiagTailX0RatChunk001Sub000Block099Part022

theorem surrogateDiagonalTailChunk001Sub000Block099Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block099Part022CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block099Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block099Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block099Part022CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block099Part022SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block099Part022] using hcert

def TailChunk001Sub000Block099Part023SupportExplicit : Finset ℕ :=
  ([20607] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block099Part023 : ℚ :=
  (368589251975 : ℚ) / 11126997757019371776

def SurrogateDiagonalTailChunk001Sub000Block099Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20607
    = surrogateDiagTailX0RatChunk001Sub000Block099Part023

theorem surrogateDiagonalTailChunk001Sub000Block099Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block099Part023CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block099Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block099Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block099Part023CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block099Part023SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block099Part023] using hcert

def TailChunk001Sub000Block099Part024SupportExplicit : Finset ℕ :=
  ([20609] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block099Part024 : ℚ :=
  (427896325 : ℚ) / 929078224830388224

def SurrogateDiagonalTailChunk001Sub000Block099Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20609
    = surrogateDiagTailX0RatChunk001Sub000Block099Part024

theorem surrogateDiagonalTailChunk001Sub000Block099Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block099Part024CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block099Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block099Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block099Part024CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block099Part024SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block099Part024] using hcert

def surrogateDiagonalTailChunk001Sub000Block099HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block099Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block099Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block099Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block099Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block099Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block099Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block099Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block099Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block099Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block099Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block099Head : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block099Part000
    + surrogateDiagTailX0RatChunk001Sub000Block099Part001
    + surrogateDiagTailX0RatChunk001Sub000Block099Part002
    + surrogateDiagTailX0RatChunk001Sub000Block099Part003
    + surrogateDiagTailX0RatChunk001Sub000Block099Part004
    + surrogateDiagTailX0RatChunk001Sub000Block099Part005
    + surrogateDiagTailX0RatChunk001Sub000Block099Part006
    + surrogateDiagTailX0RatChunk001Sub000Block099Part007
    + surrogateDiagTailX0RatChunk001Sub000Block099Part008
    + surrogateDiagTailX0RatChunk001Sub000Block099Part009

def surrogateDiagonalTailChunk001Sub000Block099MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block099Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block099Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block099Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block099Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block099Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block099Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block099Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block099Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block099Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block099Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block099Mid : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block099Part010
    + surrogateDiagTailX0RatChunk001Sub000Block099Part011
    + surrogateDiagTailX0RatChunk001Sub000Block099Part012
    + surrogateDiagTailX0RatChunk001Sub000Block099Part013
    + surrogateDiagTailX0RatChunk001Sub000Block099Part014
    + surrogateDiagTailX0RatChunk001Sub000Block099Part015
    + surrogateDiagTailX0RatChunk001Sub000Block099Part016
    + surrogateDiagTailX0RatChunk001Sub000Block099Part017
    + surrogateDiagTailX0RatChunk001Sub000Block099Part018
    + surrogateDiagTailX0RatChunk001Sub000Block099Part019

def surrogateDiagonalTailChunk001Sub000Block099TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block099Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block099Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block099Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block099Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block099Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block099Tail : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block099Part020
    + surrogateDiagTailX0RatChunk001Sub000Block099Part021
    + surrogateDiagTailX0RatChunk001Sub000Block099Part022
    + surrogateDiagTailX0RatChunk001Sub000Block099Part023
    + surrogateDiagTailX0RatChunk001Sub000Block099Part024

def surrogateDiagonalTailChunk001Sub000Block099Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk001Sub000Block099HeadSum X0
    + surrogateDiagonalTailChunk001Sub000Block099MidSum X0
    + surrogateDiagonalTailChunk001Sub000Block099TailSum X0

def surrogateDiagTailX0RatChunk001Sub000Block099 : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block099Part000
    + surrogateDiagTailX0RatChunk001Sub000Block099Part001
    + surrogateDiagTailX0RatChunk001Sub000Block099Part002
    + surrogateDiagTailX0RatChunk001Sub000Block099Part003
    + surrogateDiagTailX0RatChunk001Sub000Block099Part004
    + surrogateDiagTailX0RatChunk001Sub000Block099Part005
    + surrogateDiagTailX0RatChunk001Sub000Block099Part006
    + surrogateDiagTailX0RatChunk001Sub000Block099Part007
    + surrogateDiagTailX0RatChunk001Sub000Block099Part008
    + surrogateDiagTailX0RatChunk001Sub000Block099Part009
    + surrogateDiagTailX0RatChunk001Sub000Block099Part010
    + surrogateDiagTailX0RatChunk001Sub000Block099Part011
    + surrogateDiagTailX0RatChunk001Sub000Block099Part012
    + surrogateDiagTailX0RatChunk001Sub000Block099Part013
    + surrogateDiagTailX0RatChunk001Sub000Block099Part014
    + surrogateDiagTailX0RatChunk001Sub000Block099Part015
    + surrogateDiagTailX0RatChunk001Sub000Block099Part016
    + surrogateDiagTailX0RatChunk001Sub000Block099Part017
    + surrogateDiagTailX0RatChunk001Sub000Block099Part018
    + surrogateDiagTailX0RatChunk001Sub000Block099Part019
    + surrogateDiagTailX0RatChunk001Sub000Block099Part020
    + surrogateDiagTailX0RatChunk001Sub000Block099Part021
    + surrogateDiagTailX0RatChunk001Sub000Block099Part022
    + surrogateDiagTailX0RatChunk001Sub000Block099Part023
    + surrogateDiagTailX0RatChunk001Sub000Block099Part024

theorem surrogateDiagTailX0RatChunk001Sub000Block099_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk001Sub000Block099Head + surrogateDiagTailX0RatChunk001Sub000Block099Mid + surrogateDiagTailX0RatChunk001Sub000Block099Tail =
      surrogateDiagTailX0RatChunk001Sub000Block099 := by
  unfold surrogateDiagTailX0RatChunk001Sub000Block099Head surrogateDiagTailX0RatChunk001Sub000Block099Mid surrogateDiagTailX0RatChunk001Sub000Block099Tail surrogateDiagTailX0RatChunk001Sub000Block099
  ring

def SurrogateDiagonalTailChunk001Sub000Block099HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block099HeadSum X0 = surrogateDiagTailX0RatChunk001Sub000Block099Head

def SurrogateDiagonalTailChunk001Sub000Block099MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block099MidSum X0 = surrogateDiagTailX0RatChunk001Sub000Block099Mid

def SurrogateDiagonalTailChunk001Sub000Block099TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block099TailSum X0 = surrogateDiagTailX0RatChunk001Sub000Block099Tail

theorem surrogateDiagonalTailChunk001Sub000Block099_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk001Sub000Block099HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk001Sub000Block099MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk001Sub000Block099TailCertificateAt X0) :
    surrogateDiagonalTailChunk001Sub000Block099Sum X0 = surrogateDiagTailX0RatChunk001Sub000Block099 := by
  unfold SurrogateDiagonalTailChunk001Sub000Block099HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk001Sub000Block099MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk001Sub000Block099TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk001Sub000Block099Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk001Sub000Block099_eq_head_add_mid_add_tail

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

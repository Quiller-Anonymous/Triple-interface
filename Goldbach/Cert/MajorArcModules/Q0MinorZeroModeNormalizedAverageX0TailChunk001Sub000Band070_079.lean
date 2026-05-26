import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0TailPilot25

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

open scoped BigOperators

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

/- Generated direct-term certificate blocks for tail chunk 001, subchunk 000, blocks [70,80). -/

/-- Block 070 covers tail-support indices [11750,11775) and q from 19381 to 19417. -/

def TailChunk001Sub000Block070Part000SupportExplicit : Finset ℕ :=
  ([19381] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block070Part000 : ℚ :=
  (9390579025 : ℚ) / 141091854251664672

def SurrogateDiagonalTailChunk001Sub000Block070Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19381
    = surrogateDiagTailX0RatChunk001Sub000Block070Part000

theorem surrogateDiagonalTailChunk001Sub000Block070Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block070Part000CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block070Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block070Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block070Part000CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block070Part000SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block070Part000] using hcert

def TailChunk001Sub000Block070Part001SupportExplicit : Finset ℕ :=
  ([19382] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block070Part001 : ℚ :=
  (6781194969 : ℚ) / 19993843302400000

def SurrogateDiagonalTailChunk001Sub000Block070Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19382
    = surrogateDiagTailX0RatChunk001Sub000Block070Part001

theorem surrogateDiagonalTailChunk001Sub000Block070Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block070Part001CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block070Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block070Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block070Part001CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block070Part001SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block070Part001] using hcert

def TailChunk001Sub000Block070Part002SupportExplicit : Finset ℕ :=
  ([19383] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block070Part002 : ℚ :=
  (277812825739 : ℚ) / 1032592529306419200

def SurrogateDiagonalTailChunk001Sub000Block070Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19383
    = surrogateDiagTailX0RatChunk001Sub000Block070Part002

theorem surrogateDiagonalTailChunk001Sub000Block070Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block070Part002CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block070Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block070Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block070Part002CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block070Part002SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block070Part002] using hcert

def TailChunk001Sub000Block070Part003SupportExplicit : Finset ℕ :=
  ([19385] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block070Part003 : ℚ :=
  (15965089815775 : ℚ) / 144478058753704624128

def SurrogateDiagonalTailChunk001Sub000Block070Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19385
    = surrogateDiagTailX0RatChunk001Sub000Block070Part003

theorem surrogateDiagonalTailChunk001Sub000Block070Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block070Part003CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block070Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block070Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block070Part003CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block070Part003SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block070Part003] using hcert

def TailChunk001Sub000Block070Part004SupportExplicit : Finset ℕ :=
  ([19387] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block070Part004 : ℚ :=
  (5872746390625 : ℚ) / 88291663853350318002

def SurrogateDiagonalTailChunk001Sub000Block070Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19387
    = surrogateDiagTailX0RatChunk001Sub000Block070Part004

theorem surrogateDiagonalTailChunk001Sub000Block070Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block070Part004CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block070Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block070Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block070Part004CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block070Part004SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block070Part004] using hcert

def TailChunk001Sub000Block070Part005SupportExplicit : Finset ℕ :=
  ([19389] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block070Part005 : ℚ :=
  (27590310599 : ℚ) / 164589318065356800

def SurrogateDiagonalTailChunk001Sub000Block070Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19389
    = surrogateDiagTailX0RatChunk001Sub000Block070Part005

theorem surrogateDiagonalTailChunk001Sub000Block070Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block070Part005CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block070Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block070Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block070Part005CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block070Part005SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block070Part005] using hcert

def TailChunk001Sub000Block070Part006SupportExplicit : Finset ℕ :=
  ([19390] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block070Part006 : ℚ :=
  (826804821625 : ℚ) / 1203505730918940672

def SurrogateDiagonalTailChunk001Sub000Block070Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19390
    = surrogateDiagTailX0RatChunk001Sub000Block070Part006

theorem surrogateDiagonalTailChunk001Sub000Block070Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block070Part006CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block070Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block070Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block070Part006CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block070Part006SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block070Part006] using hcert

def TailChunk001Sub000Block070Part007SupportExplicit : Finset ℕ :=
  ([19391] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block070Part007 : ℚ :=
  (9400272025 : ℚ) / 141383290982405682

def SurrogateDiagonalTailChunk001Sub000Block070Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19391
    = surrogateDiagTailX0RatChunk001Sub000Block070Part007

theorem surrogateDiagonalTailChunk001Sub000Block070Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block070Part007CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block070Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block070Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block070Part007CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block070Part007SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block070Part007] using hcert

def TailChunk001Sub000Block070Part008SupportExplicit : Finset ℕ :=
  ([19393] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block070Part008 : ℚ :=
  (29149638547 : ℚ) / 318701397934080000

def SurrogateDiagonalTailChunk001Sub000Block070Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19393
    = surrogateDiagTailX0RatChunk001Sub000Block070Part008

theorem surrogateDiagonalTailChunk001Sub000Block070Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block070Part008CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block070Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block070Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block070Part008CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block070Part008SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block070Part008] using hcert

def TailChunk001Sub000Block070Part009SupportExplicit : Finset ℕ :=
  ([19394] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block070Part009 : ℚ :=
  (1469247015625 : ℚ) / 5525063768143429632

def SurrogateDiagonalTailChunk001Sub000Block070Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19394
    = surrogateDiagTailX0RatChunk001Sub000Block070Part009

theorem surrogateDiagonalTailChunk001Sub000Block070Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block070Part009CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block070Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block070Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block070Part009CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block070Part009SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block070Part009] using hcert

def TailChunk001Sub000Block070Part010SupportExplicit : Finset ℕ :=
  ([19397] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block070Part010 : ℚ :=
  (7893107817425 : ℚ) / 73137793435019771904

def SurrogateDiagonalTailChunk001Sub000Block070Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19397
    = surrogateDiagTailX0RatChunk001Sub000Block070Part010

theorem surrogateDiagonalTailChunk001Sub000Block070Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block070Part010CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block070Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block070Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block070Part010CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block070Part010SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block070Part010] using hcert

def TailChunk001Sub000Block070Part011SupportExplicit : Finset ℕ :=
  ([19398] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block070Part011 : ℚ :=
  (62201558579 : ℚ) / 75821996054937600

def SurrogateDiagonalTailChunk001Sub000Block070Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19398
    = surrogateDiagTailX0RatChunk001Sub000Block070Part011

theorem surrogateDiagonalTailChunk001Sub000Block070Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block070Part011CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block070Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block070Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block070Part011CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block070Part011SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block070Part011] using hcert

def TailChunk001Sub000Block070Part012SupportExplicit : Finset ℕ :=
  ([19399] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block070Part012 : ℚ :=
  (94824501001 : ℚ) / 1262801381198284800

def SurrogateDiagonalTailChunk001Sub000Block070Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19399
    = surrogateDiagTailX0RatChunk001Sub000Block070Part012

theorem surrogateDiagonalTailChunk001Sub000Block070Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block070Part012CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block070Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block070Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block070Part012CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block070Part012SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block070Part012] using hcert

def TailChunk001Sub000Block070Part013SupportExplicit : Finset ℕ :=
  ([19401] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block070Part013 : ℚ :=
  (4898396009375 : ℚ) / 29864886532676665344

def SurrogateDiagonalTailChunk001Sub000Block070Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19401
    = surrogateDiagTailX0RatChunk001Sub000Block070Part013

theorem surrogateDiagonalTailChunk001Sub000Block070Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block070Part013CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block070Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block070Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block070Part013CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block070Part013SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block070Part013] using hcert

def TailChunk001Sub000Block070Part014SupportExplicit : Finset ℕ :=
  ([19402] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block070Part014 : ℚ :=
  (5706466077925 : ℚ) / 20401052310663856128

def SurrogateDiagonalTailChunk001Sub000Block070Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19402
    = surrogateDiagTailX0RatChunk001Sub000Block070Part014

theorem surrogateDiagonalTailChunk001Sub000Block070Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block070Part014CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block070Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block070Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block070Part014CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block070Part014SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block070Part014] using hcert

def TailChunk001Sub000Block070Part015SupportExplicit : Finset ℕ :=
  ([19403] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block070Part015 : ℚ :=
  (5882443890625 : ℚ) / 88583506724501167602

def SurrogateDiagonalTailChunk001Sub000Block070Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19403
    = surrogateDiagTailX0RatChunk001Sub000Block070Part015

theorem surrogateDiagonalTailChunk001Sub000Block070Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block070Part015CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block070Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block070Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block070Part015CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block070Part015SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block070Part015] using hcert

def TailChunk001Sub000Block070Part016SupportExplicit : Finset ℕ :=
  ([19405] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block070Part016 : ℚ :=
  (639922236739 : ℚ) / 5803015330607923200

def SurrogateDiagonalTailChunk001Sub000Block070Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19405
    = surrogateDiagTailX0RatChunk001Sub000Block070Part016

theorem surrogateDiagonalTailChunk001Sub000Block070Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block070Part016CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block070Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block070Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block070Part016CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block070Part016SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block070Part016] using hcert

def TailChunk001Sub000Block070Part017SupportExplicit : Finset ℕ :=
  ([19406] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block070Part017 : ℚ :=
  (2788500041 : ℚ) / 9596221375703040

def SurrogateDiagonalTailChunk001Sub000Block070Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19406
    = surrogateDiagTailX0RatChunk001Sub000Block070Part017

theorem surrogateDiagonalTailChunk001Sub000Block070Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block070Part017CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block070Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block070Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block070Part017CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block070Part017SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block070Part017] using hcert

def TailChunk001Sub000Block070Part018SupportExplicit : Finset ℕ :=
  ([19407] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block070Part018 : ℚ :=
  (950852759375 : ℚ) / 6365524607007971328

def SurrogateDiagonalTailChunk001Sub000Block070Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19407
    = surrogateDiagTailX0RatChunk001Sub000Block070Part018

theorem surrogateDiagonalTailChunk001Sub000Block070Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block070Part018CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block070Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block070Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block070Part018CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block070Part018SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block070Part018] using hcert

def TailChunk001Sub000Block070Part019SupportExplicit : Finset ℕ :=
  ([19409] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block070Part019 : ℚ :=
  (10228771442675 : ℚ) / 128468643951000305664

def SurrogateDiagonalTailChunk001Sub000Block070Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19409
    = surrogateDiagTailX0RatChunk001Sub000Block070Part019

theorem surrogateDiagonalTailChunk001Sub000Block070Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block070Part019CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block070Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block070Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block070Part019CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block070Part019SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block070Part019] using hcert

def TailChunk001Sub000Block070Part020SupportExplicit : Finset ℕ :=
  ([19410] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block070Part020 : ℚ :=
  (800819139075 : ℚ) / 594559912566685696

def SurrogateDiagonalTailChunk001Sub000Block070Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19410
    = surrogateDiagTailX0RatChunk001Sub000Block070Part020

theorem surrogateDiagonalTailChunk001Sub000Block070Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block070Part020CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block070Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block070Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block070Part020CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block070Part020SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block070Part020] using hcert

def TailChunk001Sub000Block070Part021SupportExplicit : Finset ℕ :=
  ([19411] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block070Part021 : ℚ :=
  (308158173475 : ℚ) / 3040754804205530112

def SurrogateDiagonalTailChunk001Sub000Block070Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19411
    = surrogateDiagTailX0RatChunk001Sub000Block070Part021

theorem surrogateDiagonalTailChunk001Sub000Block070Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block070Part021CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block070Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block070Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block070Part021CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block070Part021SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block070Part021] using hcert

def TailChunk001Sub000Block070Part022SupportExplicit : Finset ℕ :=
  ([19414] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block070Part022 : ℚ :=
  (214665747133 : ℚ) / 691936441152307200

def SurrogateDiagonalTailChunk001Sub000Block070Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19414
    = surrogateDiagTailX0RatChunk001Sub000Block070Part022

theorem surrogateDiagonalTailChunk001Sub000Block070Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block070Part022CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block070Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block070Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block070Part022CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block070Part022SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block070Part022] using hcert

def TailChunk001Sub000Block070Part023SupportExplicit : Finset ℕ :=
  ([19415] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block070Part023 : ℚ :=
  (540142229611 : ℚ) / 3930949543998259200

def SurrogateDiagonalTailChunk001Sub000Block070Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19415
    = surrogateDiagTailX0RatChunk001Sub000Block070Part023

theorem surrogateDiagonalTailChunk001Sub000Block070Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block070Part023CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block070Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block070Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block070Part023CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block070Part023SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block070Part023] using hcert

def TailChunk001Sub000Block070Part024SupportExplicit : Finset ℕ :=
  ([19417] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block070Part024 : ℚ :=
  (5890935765625 : ℚ) / 88839462203869819392

def SurrogateDiagonalTailChunk001Sub000Block070Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19417
    = surrogateDiagTailX0RatChunk001Sub000Block070Part024

theorem surrogateDiagonalTailChunk001Sub000Block070Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block070Part024CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block070Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block070Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block070Part024CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block070Part024SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block070Part024] using hcert

def surrogateDiagonalTailChunk001Sub000Block070HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block070Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block070Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block070Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block070Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block070Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block070Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block070Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block070Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block070Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block070Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block070Head : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block070Part000
    + surrogateDiagTailX0RatChunk001Sub000Block070Part001
    + surrogateDiagTailX0RatChunk001Sub000Block070Part002
    + surrogateDiagTailX0RatChunk001Sub000Block070Part003
    + surrogateDiagTailX0RatChunk001Sub000Block070Part004
    + surrogateDiagTailX0RatChunk001Sub000Block070Part005
    + surrogateDiagTailX0RatChunk001Sub000Block070Part006
    + surrogateDiagTailX0RatChunk001Sub000Block070Part007
    + surrogateDiagTailX0RatChunk001Sub000Block070Part008
    + surrogateDiagTailX0RatChunk001Sub000Block070Part009

def surrogateDiagonalTailChunk001Sub000Block070MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block070Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block070Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block070Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block070Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block070Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block070Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block070Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block070Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block070Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block070Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block070Mid : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block070Part010
    + surrogateDiagTailX0RatChunk001Sub000Block070Part011
    + surrogateDiagTailX0RatChunk001Sub000Block070Part012
    + surrogateDiagTailX0RatChunk001Sub000Block070Part013
    + surrogateDiagTailX0RatChunk001Sub000Block070Part014
    + surrogateDiagTailX0RatChunk001Sub000Block070Part015
    + surrogateDiagTailX0RatChunk001Sub000Block070Part016
    + surrogateDiagTailX0RatChunk001Sub000Block070Part017
    + surrogateDiagTailX0RatChunk001Sub000Block070Part018
    + surrogateDiagTailX0RatChunk001Sub000Block070Part019

def surrogateDiagonalTailChunk001Sub000Block070TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block070Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block070Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block070Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block070Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block070Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block070Tail : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block070Part020
    + surrogateDiagTailX0RatChunk001Sub000Block070Part021
    + surrogateDiagTailX0RatChunk001Sub000Block070Part022
    + surrogateDiagTailX0RatChunk001Sub000Block070Part023
    + surrogateDiagTailX0RatChunk001Sub000Block070Part024

def surrogateDiagonalTailChunk001Sub000Block070Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk001Sub000Block070HeadSum X0
    + surrogateDiagonalTailChunk001Sub000Block070MidSum X0
    + surrogateDiagonalTailChunk001Sub000Block070TailSum X0

def surrogateDiagTailX0RatChunk001Sub000Block070 : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block070Part000
    + surrogateDiagTailX0RatChunk001Sub000Block070Part001
    + surrogateDiagTailX0RatChunk001Sub000Block070Part002
    + surrogateDiagTailX0RatChunk001Sub000Block070Part003
    + surrogateDiagTailX0RatChunk001Sub000Block070Part004
    + surrogateDiagTailX0RatChunk001Sub000Block070Part005
    + surrogateDiagTailX0RatChunk001Sub000Block070Part006
    + surrogateDiagTailX0RatChunk001Sub000Block070Part007
    + surrogateDiagTailX0RatChunk001Sub000Block070Part008
    + surrogateDiagTailX0RatChunk001Sub000Block070Part009
    + surrogateDiagTailX0RatChunk001Sub000Block070Part010
    + surrogateDiagTailX0RatChunk001Sub000Block070Part011
    + surrogateDiagTailX0RatChunk001Sub000Block070Part012
    + surrogateDiagTailX0RatChunk001Sub000Block070Part013
    + surrogateDiagTailX0RatChunk001Sub000Block070Part014
    + surrogateDiagTailX0RatChunk001Sub000Block070Part015
    + surrogateDiagTailX0RatChunk001Sub000Block070Part016
    + surrogateDiagTailX0RatChunk001Sub000Block070Part017
    + surrogateDiagTailX0RatChunk001Sub000Block070Part018
    + surrogateDiagTailX0RatChunk001Sub000Block070Part019
    + surrogateDiagTailX0RatChunk001Sub000Block070Part020
    + surrogateDiagTailX0RatChunk001Sub000Block070Part021
    + surrogateDiagTailX0RatChunk001Sub000Block070Part022
    + surrogateDiagTailX0RatChunk001Sub000Block070Part023
    + surrogateDiagTailX0RatChunk001Sub000Block070Part024

theorem surrogateDiagTailX0RatChunk001Sub000Block070_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk001Sub000Block070Head + surrogateDiagTailX0RatChunk001Sub000Block070Mid + surrogateDiagTailX0RatChunk001Sub000Block070Tail =
      surrogateDiagTailX0RatChunk001Sub000Block070 := by
  unfold surrogateDiagTailX0RatChunk001Sub000Block070Head surrogateDiagTailX0RatChunk001Sub000Block070Mid surrogateDiagTailX0RatChunk001Sub000Block070Tail surrogateDiagTailX0RatChunk001Sub000Block070
  ring

def SurrogateDiagonalTailChunk001Sub000Block070HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block070HeadSum X0 = surrogateDiagTailX0RatChunk001Sub000Block070Head

def SurrogateDiagonalTailChunk001Sub000Block070MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block070MidSum X0 = surrogateDiagTailX0RatChunk001Sub000Block070Mid

def SurrogateDiagonalTailChunk001Sub000Block070TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block070TailSum X0 = surrogateDiagTailX0RatChunk001Sub000Block070Tail

theorem surrogateDiagonalTailChunk001Sub000Block070_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk001Sub000Block070HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk001Sub000Block070MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk001Sub000Block070TailCertificateAt X0) :
    surrogateDiagonalTailChunk001Sub000Block070Sum X0 = surrogateDiagTailX0RatChunk001Sub000Block070 := by
  unfold SurrogateDiagonalTailChunk001Sub000Block070HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk001Sub000Block070MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk001Sub000Block070TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk001Sub000Block070Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk001Sub000Block070_eq_head_add_mid_add_tail

/-- Block 071 covers tail-support indices [11775,11800) and q from 19418 to 19461. -/

def TailChunk001Sub000Block071Part000SupportExplicit : Finset ℕ :=
  ([19418] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block071Part000 : ℚ :=
  (4250014102825 : ℚ) / 9142224179377471488

def SurrogateDiagonalTailChunk001Sub000Block071Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19418
    = surrogateDiagTailX0RatChunk001Sub000Block071Part000

theorem surrogateDiagonalTailChunk001Sub000Block071Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block071Part000CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block071Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block071Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block071Part000CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block071Part000SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block071Part000] using hcert

def TailChunk001Sub000Block071Part001SupportExplicit : Finset ℕ :=
  ([19419] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block071Part001 : ℚ :=
  (10472320352725 : ℚ) / 70194142975897141248

def SurrogateDiagonalTailChunk001Sub000Block071Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19419
    = surrogateDiagTailX0RatChunk001Sub000Block071Part001

theorem surrogateDiagonalTailChunk001Sub000Block071Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block071Part001CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block071Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block071Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block071Part001CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block071Part001SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block071Part001] using hcert

def TailChunk001Sub000Block071Part002SupportExplicit : Finset ℕ :=
  ([19421] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block071Part002 : ℚ :=
  (9429381025 : ℚ) / 142260310577800992

def SurrogateDiagonalTailChunk001Sub000Block071Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19421
    = surrogateDiagTailX0RatChunk001Sub000Block071Part002

theorem surrogateDiagonalTailChunk001Sub000Block071Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block071Part002CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block071Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block071Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block071Part002CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block071Part002SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block071Part002] using hcert

def TailChunk001Sub000Block071Part003SupportExplicit : Finset ℕ :=
  ([19423] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block071Part003 : ℚ :=
  (5894577015625 : ℚ) / 88949327038120404882

def SurrogateDiagonalTailChunk001Sub000Block071Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19423
    = surrogateDiagTailX0RatChunk001Sub000Block071Part003

theorem surrogateDiagonalTailChunk001Sub000Block071Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block071Part003CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block071Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block071Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block071Part003CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block071Part003SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block071Part003] using hcert

def TailChunk001Sub000Block071Part004SupportExplicit : Finset ℕ :=
  ([19426] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block071Part004 : ℚ :=
  (65609057 : ℚ) / 4035245219506368

def SurrogateDiagonalTailChunk001Sub000Block071Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19426
    = surrogateDiagTailX0RatChunk001Sub000Block071Part004

theorem surrogateDiagonalTailChunk001Sub000Block071Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block071Part004CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block071Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block071Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block071Part004CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block071Part004SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block071Part004] using hcert

def TailChunk001Sub000Block071Part005SupportExplicit : Finset ℕ :=
  ([19427] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block071Part005 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block071Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19427
    = surrogateDiagTailX0RatChunk001Sub000Block071Part005

theorem surrogateDiagonalTailChunk001Sub000Block071Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block071Part005CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block071Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block071Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block071Part005CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block071Part005SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block071Part005] using hcert

def TailChunk001Sub000Block071Part006SupportExplicit : Finset ℕ :=
  ([19429] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block071Part006 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block071Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19429
    = surrogateDiagTailX0RatChunk001Sub000Block071Part006

theorem surrogateDiagonalTailChunk001Sub000Block071Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block071Part006CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block071Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block071Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block071Part006CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block071Part006SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block071Part006] using hcert

def TailChunk001Sub000Block071Part007SupportExplicit : Finset ℕ :=
  ([19430] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block071Part007 : ℚ :=
  (271226984225 : ℚ) / 3732885733722292224

def SurrogateDiagonalTailChunk001Sub000Block071Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19430
    = surrogateDiagTailX0RatChunk001Sub000Block071Part007

theorem surrogateDiagonalTailChunk001Sub000Block071Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block071Part007CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block071Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block071Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block071Part007CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block071Part007SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block071Part007] using hcert

def TailChunk001Sub000Block071Part008SupportExplicit : Finset ℕ :=
  ([19433] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block071Part008 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block071Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19433
    = surrogateDiagTailX0RatChunk001Sub000Block071Part008

theorem surrogateDiagonalTailChunk001Sub000Block071Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block071Part008CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block071Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block071Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block071Part008CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block071Part008SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block071Part008] using hcert

def TailChunk001Sub000Block071Part009SupportExplicit : Finset ℕ :=
  ([19434] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block071Part009 : ℚ :=
  (27225799243 : ℚ) / 151643992109875200

def SurrogateDiagonalTailChunk001Sub000Block071Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19434
    = surrogateDiagTailX0RatChunk001Sub000Block071Part009

theorem surrogateDiagonalTailChunk001Sub000Block071Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block071Part009CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block071Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block071Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block071Part009CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block071Part009SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block071Part009] using hcert

def TailChunk001Sub000Block071Part010SupportExplicit : Finset ℕ :=
  ([19437] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block071Part010 : ℚ :=
  (495273251 : ℚ) / 27215221155840000

def SurrogateDiagonalTailChunk001Sub000Block071Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19437
    = surrogateDiagTailX0RatChunk001Sub000Block071Part010

theorem surrogateDiagonalTailChunk001Sub000Block071Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block071Part010CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block071Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block071Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block071Part010CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block071Part010SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block071Part010] using hcert

def TailChunk001Sub000Block071Part011SupportExplicit : Finset ℕ :=
  ([19438] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block071Part011 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block071Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19438
    = surrogateDiagTailX0RatChunk001Sub000Block071Part011

theorem surrogateDiagonalTailChunk001Sub000Block071Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block071Part011CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block071Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block071Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block071Part011CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block071Part011SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block071Part011] using hcert

def TailChunk001Sub000Block071Part012SupportExplicit : Finset ℕ :=
  ([19439] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block071Part012 : ℚ :=
  (483510888625 : ℚ) / 192446362855498088448

def SurrogateDiagonalTailChunk001Sub000Block071Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19439
    = surrogateDiagTailX0RatChunk001Sub000Block071Part012

theorem surrogateDiagonalTailChunk001Sub000Block071Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block071Part012CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block071Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block071Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block071Part012CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block071Part012SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block071Part012] using hcert

def TailChunk001Sub000Block071Part013SupportExplicit : Finset ℕ :=
  ([19441] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block071Part013 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block071Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19441
    = surrogateDiagTailX0RatChunk001Sub000Block071Part013

theorem surrogateDiagonalTailChunk001Sub000Block071Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block071Part013CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block071Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block071Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block071Part013CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block071Part013SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block071Part013] using hcert

def TailChunk001Sub000Block071Part014SupportExplicit : Finset ℕ :=
  ([19442] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block071Part014 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block071Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19442
    = surrogateDiagTailX0RatChunk001Sub000Block071Part014

theorem surrogateDiagonalTailChunk001Sub000Block071Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block071Part014CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block071Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block071Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block071Part014CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block071Part014SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block071Part014] using hcert

def TailChunk001Sub000Block071Part015SupportExplicit : Finset ℕ :=
  ([19443] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block071Part015 : ℚ :=
  (1667 : ℚ) / 188073993830400

def SurrogateDiagonalTailChunk001Sub000Block071Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19443
    = surrogateDiagTailX0RatChunk001Sub000Block071Part015

theorem surrogateDiagonalTailChunk001Sub000Block071Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block071Part015CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block071Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block071Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block071Part015CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block071Part015SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block071Part015] using hcert

def TailChunk001Sub000Block071Part016SupportExplicit : Finset ℕ :=
  ([19445] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block071Part016 : ℚ :=
  (946034701375 : ℚ) / 146275586870039543808

def SurrogateDiagonalTailChunk001Sub000Block071Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19445
    = surrogateDiagTailX0RatChunk001Sub000Block071Part016

theorem surrogateDiagonalTailChunk001Sub000Block071Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block071Part016CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block071Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block071Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block071Part016CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block071Part016SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block071Part016] using hcert

def TailChunk001Sub000Block071Part017SupportExplicit : Finset ℕ :=
  ([19446] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block071Part017 : ℚ :=
  (388731875375 : ℚ) / 1181108376685569024

def SurrogateDiagonalTailChunk001Sub000Block071Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19446
    = surrogateDiagTailX0RatChunk001Sub000Block071Part017

theorem surrogateDiagonalTailChunk001Sub000Block071Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block071Part017CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block071Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block071Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block071Part017CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block071Part017SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block071Part017] using hcert

def TailChunk001Sub000Block071Part018SupportExplicit : Finset ℕ :=
  ([19447] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block071Part018 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block071Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19447
    = surrogateDiagTailX0RatChunk001Sub000Block071Part018

theorem surrogateDiagonalTailChunk001Sub000Block071Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block071Part018CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block071Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block071Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block071Part018CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block071Part018SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block071Part018] using hcert

def TailChunk001Sub000Block071Part019SupportExplicit : Finset ℕ :=
  ([19451] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block071Part019 : ℚ :=
  (22210765775 : ℚ) / 54678088629129858048

def SurrogateDiagonalTailChunk001Sub000Block071Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19451
    = surrogateDiagTailX0RatChunk001Sub000Block071Part019

theorem surrogateDiagonalTailChunk001Sub000Block071Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block071Part019CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block071Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block071Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block071Part019CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block071Part019SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block071Part019] using hcert

def TailChunk001Sub000Block071Part020SupportExplicit : Finset ℕ :=
  ([19454] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block071Part020 : ℚ :=
  (2568440401 : ℚ) / 821551217804083200

def SurrogateDiagonalTailChunk001Sub000Block071Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19454
    = surrogateDiagTailX0RatChunk001Sub000Block071Part020

theorem surrogateDiagonalTailChunk001Sub000Block071Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block071Part020CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block071Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block071Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block071Part020CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block071Part020SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block071Part020] using hcert

def TailChunk001Sub000Block071Part021SupportExplicit : Finset ℕ :=
  ([19455] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block071Part021 : ℚ :=
  (737457800725 : ℚ) / 28893943085439909888

def SurrogateDiagonalTailChunk001Sub000Block071Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19455
    = surrogateDiagTailX0RatChunk001Sub000Block071Part021

theorem surrogateDiagonalTailChunk001Sub000Block071Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block071Part021CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block071Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block071Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block071Part021CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block071Part021SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block071Part021] using hcert

def TailChunk001Sub000Block071Part022SupportExplicit : Finset ℕ :=
  ([19457] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block071Part022 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block071Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19457
    = surrogateDiagTailX0RatChunk001Sub000Block071Part022

theorem surrogateDiagonalTailChunk001Sub000Block071Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block071Part022CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block071Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block071Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block071Part022CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block071Part022SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block071Part022] using hcert

def TailChunk001Sub000Block071Part023SupportExplicit : Finset ℕ :=
  ([19459] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block071Part023 : ℚ :=
  (31663932637 : ℚ) / 7967534948352000000

def SurrogateDiagonalTailChunk001Sub000Block071Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19459
    = surrogateDiagTailX0RatChunk001Sub000Block071Part023

theorem surrogateDiagonalTailChunk001Sub000Block071Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block071Part023CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block071Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block071Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block071Part023CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block071Part023SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block071Part023] using hcert

def TailChunk001Sub000Block071Part024SupportExplicit : Finset ℕ :=
  ([19461] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block071Part024 : ℚ :=
  (302058748525 : ℚ) / 51025726486907486208

def SurrogateDiagonalTailChunk001Sub000Block071Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19461
    = surrogateDiagTailX0RatChunk001Sub000Block071Part024

theorem surrogateDiagonalTailChunk001Sub000Block071Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block071Part024CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block071Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block071Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block071Part024CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block071Part024SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block071Part024] using hcert

def surrogateDiagonalTailChunk001Sub000Block071HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block071Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block071Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block071Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block071Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block071Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block071Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block071Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block071Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block071Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block071Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block071Head : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block071Part000
    + surrogateDiagTailX0RatChunk001Sub000Block071Part001
    + surrogateDiagTailX0RatChunk001Sub000Block071Part002
    + surrogateDiagTailX0RatChunk001Sub000Block071Part003
    + surrogateDiagTailX0RatChunk001Sub000Block071Part004
    + surrogateDiagTailX0RatChunk001Sub000Block071Part005
    + surrogateDiagTailX0RatChunk001Sub000Block071Part006
    + surrogateDiagTailX0RatChunk001Sub000Block071Part007
    + surrogateDiagTailX0RatChunk001Sub000Block071Part008
    + surrogateDiagTailX0RatChunk001Sub000Block071Part009

def surrogateDiagonalTailChunk001Sub000Block071MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block071Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block071Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block071Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block071Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block071Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block071Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block071Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block071Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block071Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block071Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block071Mid : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block071Part010
    + surrogateDiagTailX0RatChunk001Sub000Block071Part011
    + surrogateDiagTailX0RatChunk001Sub000Block071Part012
    + surrogateDiagTailX0RatChunk001Sub000Block071Part013
    + surrogateDiagTailX0RatChunk001Sub000Block071Part014
    + surrogateDiagTailX0RatChunk001Sub000Block071Part015
    + surrogateDiagTailX0RatChunk001Sub000Block071Part016
    + surrogateDiagTailX0RatChunk001Sub000Block071Part017
    + surrogateDiagTailX0RatChunk001Sub000Block071Part018
    + surrogateDiagTailX0RatChunk001Sub000Block071Part019

def surrogateDiagonalTailChunk001Sub000Block071TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block071Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block071Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block071Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block071Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block071Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block071Tail : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block071Part020
    + surrogateDiagTailX0RatChunk001Sub000Block071Part021
    + surrogateDiagTailX0RatChunk001Sub000Block071Part022
    + surrogateDiagTailX0RatChunk001Sub000Block071Part023
    + surrogateDiagTailX0RatChunk001Sub000Block071Part024

def surrogateDiagonalTailChunk001Sub000Block071Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk001Sub000Block071HeadSum X0
    + surrogateDiagonalTailChunk001Sub000Block071MidSum X0
    + surrogateDiagonalTailChunk001Sub000Block071TailSum X0

def surrogateDiagTailX0RatChunk001Sub000Block071 : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block071Part000
    + surrogateDiagTailX0RatChunk001Sub000Block071Part001
    + surrogateDiagTailX0RatChunk001Sub000Block071Part002
    + surrogateDiagTailX0RatChunk001Sub000Block071Part003
    + surrogateDiagTailX0RatChunk001Sub000Block071Part004
    + surrogateDiagTailX0RatChunk001Sub000Block071Part005
    + surrogateDiagTailX0RatChunk001Sub000Block071Part006
    + surrogateDiagTailX0RatChunk001Sub000Block071Part007
    + surrogateDiagTailX0RatChunk001Sub000Block071Part008
    + surrogateDiagTailX0RatChunk001Sub000Block071Part009
    + surrogateDiagTailX0RatChunk001Sub000Block071Part010
    + surrogateDiagTailX0RatChunk001Sub000Block071Part011
    + surrogateDiagTailX0RatChunk001Sub000Block071Part012
    + surrogateDiagTailX0RatChunk001Sub000Block071Part013
    + surrogateDiagTailX0RatChunk001Sub000Block071Part014
    + surrogateDiagTailX0RatChunk001Sub000Block071Part015
    + surrogateDiagTailX0RatChunk001Sub000Block071Part016
    + surrogateDiagTailX0RatChunk001Sub000Block071Part017
    + surrogateDiagTailX0RatChunk001Sub000Block071Part018
    + surrogateDiagTailX0RatChunk001Sub000Block071Part019
    + surrogateDiagTailX0RatChunk001Sub000Block071Part020
    + surrogateDiagTailX0RatChunk001Sub000Block071Part021
    + surrogateDiagTailX0RatChunk001Sub000Block071Part022
    + surrogateDiagTailX0RatChunk001Sub000Block071Part023
    + surrogateDiagTailX0RatChunk001Sub000Block071Part024

theorem surrogateDiagTailX0RatChunk001Sub000Block071_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk001Sub000Block071Head + surrogateDiagTailX0RatChunk001Sub000Block071Mid + surrogateDiagTailX0RatChunk001Sub000Block071Tail =
      surrogateDiagTailX0RatChunk001Sub000Block071 := by
  unfold surrogateDiagTailX0RatChunk001Sub000Block071Head surrogateDiagTailX0RatChunk001Sub000Block071Mid surrogateDiagTailX0RatChunk001Sub000Block071Tail surrogateDiagTailX0RatChunk001Sub000Block071
  ring

def SurrogateDiagonalTailChunk001Sub000Block071HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block071HeadSum X0 = surrogateDiagTailX0RatChunk001Sub000Block071Head

def SurrogateDiagonalTailChunk001Sub000Block071MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block071MidSum X0 = surrogateDiagTailX0RatChunk001Sub000Block071Mid

def SurrogateDiagonalTailChunk001Sub000Block071TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block071TailSum X0 = surrogateDiagTailX0RatChunk001Sub000Block071Tail

theorem surrogateDiagonalTailChunk001Sub000Block071_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk001Sub000Block071HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk001Sub000Block071MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk001Sub000Block071TailCertificateAt X0) :
    surrogateDiagonalTailChunk001Sub000Block071Sum X0 = surrogateDiagTailX0RatChunk001Sub000Block071 := by
  unfold SurrogateDiagonalTailChunk001Sub000Block071HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk001Sub000Block071MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk001Sub000Block071TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk001Sub000Block071Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk001Sub000Block071_eq_head_add_mid_add_tail

/-- Block 072 covers tail-support indices [11800,11825) and q from 19462 to 19501. -/

def TailChunk001Sub000Block072Part000SupportExplicit : Finset ℕ :=
  ([19462] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block072Part000 : ℚ :=
  (92459862025 : ℚ) / 19789828346647922688

def SurrogateDiagonalTailChunk001Sub000Block072Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19462
    = surrogateDiagTailX0RatChunk001Sub000Block072Part000

theorem surrogateDiagonalTailChunk001Sub000Block072Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block072Part000CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block072Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block072Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block072Part000CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block072Part000SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block072Part000] using hcert

def TailChunk001Sub000Block072Part001SupportExplicit : Finset ℕ :=
  ([19463] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block072Part001 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block072Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19463
    = surrogateDiagTailX0RatChunk001Sub000Block072Part001

theorem surrogateDiagonalTailChunk001Sub000Block072Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block072Part001CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block072Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block072Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block072Part001CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block072Part001SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block072Part001] using hcert

def TailChunk001Sub000Block072Part002SupportExplicit : Finset ℕ :=
  ([19465] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block072Part002 : ℚ :=
  (193939391725 : ℚ) / 18894477753065668608

def SurrogateDiagonalTailChunk001Sub000Block072Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19465
    = surrogateDiagTailX0RatChunk001Sub000Block072Part002

theorem surrogateDiagonalTailChunk001Sub000Block072Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block072Part002CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block072Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block072Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block072Part002CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block072Part002SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block072Part002] using hcert

def TailChunk001Sub000Block072Part003SupportExplicit : Finset ℕ :=
  ([19466] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block072Part003 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block072Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19466
    = surrogateDiagTailX0RatChunk001Sub000Block072Part003

theorem surrogateDiagonalTailChunk001Sub000Block072Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block072Part003CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block072Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block072Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block072Part003CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block072Part003SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block072Part003] using hcert

def TailChunk001Sub000Block072Part004SupportExplicit : Finset ℕ :=
  ([19469] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block072Part004 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block072Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19469
    = surrogateDiagTailX0RatChunk001Sub000Block072Part004

theorem surrogateDiagonalTailChunk001Sub000Block072Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block072Part004CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block072Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block072Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block072Part004CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block072Part004SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block072Part004] using hcert

def TailChunk001Sub000Block072Part005SupportExplicit : Finset ℕ :=
  ([19470] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block072Part005 : ℚ :=
  (33491065873 : ℚ) / 46361638089523200

def SurrogateDiagonalTailChunk001Sub000Block072Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19470
    = surrogateDiagTailX0RatChunk001Sub000Block072Part005

theorem surrogateDiagonalTailChunk001Sub000Block072Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block072Part005CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block072Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block072Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block072Part005CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block072Part005SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block072Part005] using hcert

def TailChunk001Sub000Block072Part006SupportExplicit : Finset ℕ :=
  ([19471] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block072Part006 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block072Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19471
    = surrogateDiagTailX0RatChunk001Sub000Block072Part006

theorem surrogateDiagonalTailChunk001Sub000Block072Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block072Part006CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block072Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block072Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block072Part006CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block072Part006SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block072Part006] using hcert

def TailChunk001Sub000Block072Part007SupportExplicit : Finset ℕ :=
  ([19473] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block072Part007 : ℚ :=
  (5001 : ℚ) / 567712903683200

def SurrogateDiagonalTailChunk001Sub000Block072Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19473
    = surrogateDiagTailX0RatChunk001Sub000Block072Part007

theorem surrogateDiagonalTailChunk001Sub000Block072Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block072Part007CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block072Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block072Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block072Part007CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block072Part007SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block072Part007] using hcert

def TailChunk001Sub000Block072Part008SupportExplicit : Finset ℕ :=
  ([19474] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block072Part008 : ℚ :=
  (2911658125 : ℚ) / 39275936980512768

def SurrogateDiagonalTailChunk001Sub000Block072Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19474
    = surrogateDiagTailX0RatChunk001Sub000Block072Part008

theorem surrogateDiagonalTailChunk001Sub000Block072Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block072Part008CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block072Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block072Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block072Part008CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block072Part008SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block072Part008] using hcert

def TailChunk001Sub000Block072Part009SupportExplicit : Finset ℕ :=
  ([19477] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block072Part009 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block072Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19477
    = surrogateDiagTailX0RatChunk001Sub000Block072Part009

theorem surrogateDiagonalTailChunk001Sub000Block072Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block072Part009CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block072Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block072Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block072Part009CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block072Part009SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block072Part009] using hcert

def TailChunk001Sub000Block072Part010SupportExplicit : Finset ℕ :=
  ([19478] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block072Part010 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block072Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19478
    = surrogateDiagTailX0RatChunk001Sub000Block072Part010

theorem surrogateDiagonalTailChunk001Sub000Block072Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block072Part010CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block072Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block072Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block072Part010CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block072Part010SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block072Part010] using hcert

def TailChunk001Sub000Block072Part011SupportExplicit : Finset ℕ :=
  ([19479] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block072Part011 : ℚ :=
  (105971 : ℚ) / 56010528000000

def SurrogateDiagonalTailChunk001Sub000Block072Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19479
    = surrogateDiagTailX0RatChunk001Sub000Block072Part011

theorem surrogateDiagonalTailChunk001Sub000Block072Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block072Part011CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block072Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block072Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block072Part011CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block072Part011SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block072Part011] using hcert

def TailChunk001Sub000Block072Part012SupportExplicit : Finset ℕ :=
  ([19482] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block072Part012 : ℚ :=
  (141820207 : ℚ) / 378611643187200

def SurrogateDiagonalTailChunk001Sub000Block072Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19482
    = surrogateDiagTailX0RatChunk001Sub000Block072Part012

theorem surrogateDiagonalTailChunk001Sub000Block072Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block072Part012CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block072Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block072Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block072Part012CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block072Part012SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block072Part012] using hcert

def TailChunk001Sub000Block072Part013SupportExplicit : Finset ℕ :=
  ([19483] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block072Part013 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block072Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19483
    = surrogateDiagTailX0RatChunk001Sub000Block072Part013

theorem surrogateDiagonalTailChunk001Sub000Block072Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block072Part013CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block072Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block072Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block072Part013CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block072Part013SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block072Part013] using hcert

def TailChunk001Sub000Block072Part014SupportExplicit : Finset ℕ :=
  ([19486] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block072Part014 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block072Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19486
    = surrogateDiagTailX0RatChunk001Sub000Block072Part014

theorem surrogateDiagonalTailChunk001Sub000Block072Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block072Part014CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block072Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block072Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block072Part014CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block072Part014SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block072Part014] using hcert

def TailChunk001Sub000Block072Part015SupportExplicit : Finset ℕ :=
  ([19487] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block072Part015 : ℚ :=
  (7577423675 : ℚ) / 4662416526712213248

def SurrogateDiagonalTailChunk001Sub000Block072Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19487
    = surrogateDiagTailX0RatChunk001Sub000Block072Part015

theorem surrogateDiagonalTailChunk001Sub000Block072Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block072Part015CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block072Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block072Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block072Part015CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block072Part015SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block072Part015] using hcert

def TailChunk001Sub000Block072Part016SupportExplicit : Finset ℕ :=
  ([19489] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block072Part016 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block072Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19489
    = surrogateDiagTailX0RatChunk001Sub000Block072Part016

theorem surrogateDiagonalTailChunk001Sub000Block072Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block072Part016CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block072Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block072Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block072Part016CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block072Part016SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block072Part016] using hcert

def TailChunk001Sub000Block072Part017SupportExplicit : Finset ℕ :=
  ([19490] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block072Part017 : ℚ :=
  (356236218275 : ℚ) / 4608850689057767424

def SurrogateDiagonalTailChunk001Sub000Block072Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19490
    = surrogateDiagTailX0RatChunk001Sub000Block072Part017

theorem surrogateDiagonalTailChunk001Sub000Block072Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block072Part017CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block072Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block072Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block072Part017CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block072Part017SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block072Part017] using hcert

def TailChunk001Sub000Block072Part018SupportExplicit : Finset ℕ :=
  ([19491] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block072Part018 : ℚ :=
  (869155662475 : ℚ) / 21492466631810482176

def SurrogateDiagonalTailChunk001Sub000Block072Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19491
    = surrogateDiagTailX0RatChunk001Sub000Block072Part018

theorem surrogateDiagonalTailChunk001Sub000Block072Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block072Part018CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block072Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block072Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block072Part018CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block072Part018SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block072Part018] using hcert

def TailChunk001Sub000Block072Part019SupportExplicit : Finset ℕ :=
  ([19493] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block072Part019 : ℚ :=
  (24309113 : ℚ) / 90615085793280000

def SurrogateDiagonalTailChunk001Sub000Block072Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19493
    = surrogateDiagTailX0RatChunk001Sub000Block072Part019

theorem surrogateDiagonalTailChunk001Sub000Block072Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block072Part019CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block072Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block072Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block072Part019CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block072Part019SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block072Part019] using hcert

def TailChunk001Sub000Block072Part020SupportExplicit : Finset ℕ :=
  ([19495] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block072Part020 : ℚ :=
  (1437293354875 : ℚ) / 79281341852193128448

def SurrogateDiagonalTailChunk001Sub000Block072Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19495
    = surrogateDiagTailX0RatChunk001Sub000Block072Part020

theorem surrogateDiagonalTailChunk001Sub000Block072Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block072Part020CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block072Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block072Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block072Part020CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block072Part020SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block072Part020] using hcert

def TailChunk001Sub000Block072Part021SupportExplicit : Finset ℕ :=
  ([19497] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block072Part021 : ℚ :=
  (289888011275 : ℚ) / 7164155543936827392

def SurrogateDiagonalTailChunk001Sub000Block072Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19497
    = surrogateDiagTailX0RatChunk001Sub000Block072Part021

theorem surrogateDiagonalTailChunk001Sub000Block072Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block072Part021CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block072Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block072Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block072Part021CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block072Part021SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block072Part021] using hcert

def TailChunk001Sub000Block072Part022SupportExplicit : Finset ℕ :=
  ([19498] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block072Part022 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block072Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19498
    = surrogateDiagTailX0RatChunk001Sub000Block072Part022

theorem surrogateDiagonalTailChunk001Sub000Block072Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block072Part022CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block072Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block072Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block072Part022CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block072Part022SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block072Part022] using hcert

def TailChunk001Sub000Block072Part023SupportExplicit : Finset ℕ :=
  ([19499] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block072Part023 : ℚ :=
  (3097141883 : ℚ) / 990875963149516800

def SurrogateDiagonalTailChunk001Sub000Block072Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19499
    = surrogateDiagTailX0RatChunk001Sub000Block072Part023

theorem surrogateDiagonalTailChunk001Sub000Block072Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block072Part023CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block072Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block072Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block072Part023CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block072Part023SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block072Part023] using hcert

def TailChunk001Sub000Block072Part024SupportExplicit : Finset ℕ :=
  ([19501] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block072Part024 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block072Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19501
    = surrogateDiagTailX0RatChunk001Sub000Block072Part024

theorem surrogateDiagonalTailChunk001Sub000Block072Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block072Part024CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block072Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block072Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block072Part024CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block072Part024SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block072Part024] using hcert

def surrogateDiagonalTailChunk001Sub000Block072HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block072Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block072Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block072Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block072Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block072Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block072Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block072Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block072Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block072Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block072Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block072Head : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block072Part000
    + surrogateDiagTailX0RatChunk001Sub000Block072Part001
    + surrogateDiagTailX0RatChunk001Sub000Block072Part002
    + surrogateDiagTailX0RatChunk001Sub000Block072Part003
    + surrogateDiagTailX0RatChunk001Sub000Block072Part004
    + surrogateDiagTailX0RatChunk001Sub000Block072Part005
    + surrogateDiagTailX0RatChunk001Sub000Block072Part006
    + surrogateDiagTailX0RatChunk001Sub000Block072Part007
    + surrogateDiagTailX0RatChunk001Sub000Block072Part008
    + surrogateDiagTailX0RatChunk001Sub000Block072Part009

def surrogateDiagonalTailChunk001Sub000Block072MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block072Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block072Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block072Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block072Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block072Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block072Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block072Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block072Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block072Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block072Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block072Mid : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block072Part010
    + surrogateDiagTailX0RatChunk001Sub000Block072Part011
    + surrogateDiagTailX0RatChunk001Sub000Block072Part012
    + surrogateDiagTailX0RatChunk001Sub000Block072Part013
    + surrogateDiagTailX0RatChunk001Sub000Block072Part014
    + surrogateDiagTailX0RatChunk001Sub000Block072Part015
    + surrogateDiagTailX0RatChunk001Sub000Block072Part016
    + surrogateDiagTailX0RatChunk001Sub000Block072Part017
    + surrogateDiagTailX0RatChunk001Sub000Block072Part018
    + surrogateDiagTailX0RatChunk001Sub000Block072Part019

def surrogateDiagonalTailChunk001Sub000Block072TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block072Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block072Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block072Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block072Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block072Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block072Tail : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block072Part020
    + surrogateDiagTailX0RatChunk001Sub000Block072Part021
    + surrogateDiagTailX0RatChunk001Sub000Block072Part022
    + surrogateDiagTailX0RatChunk001Sub000Block072Part023
    + surrogateDiagTailX0RatChunk001Sub000Block072Part024

def surrogateDiagonalTailChunk001Sub000Block072Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk001Sub000Block072HeadSum X0
    + surrogateDiagonalTailChunk001Sub000Block072MidSum X0
    + surrogateDiagonalTailChunk001Sub000Block072TailSum X0

def surrogateDiagTailX0RatChunk001Sub000Block072 : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block072Part000
    + surrogateDiagTailX0RatChunk001Sub000Block072Part001
    + surrogateDiagTailX0RatChunk001Sub000Block072Part002
    + surrogateDiagTailX0RatChunk001Sub000Block072Part003
    + surrogateDiagTailX0RatChunk001Sub000Block072Part004
    + surrogateDiagTailX0RatChunk001Sub000Block072Part005
    + surrogateDiagTailX0RatChunk001Sub000Block072Part006
    + surrogateDiagTailX0RatChunk001Sub000Block072Part007
    + surrogateDiagTailX0RatChunk001Sub000Block072Part008
    + surrogateDiagTailX0RatChunk001Sub000Block072Part009
    + surrogateDiagTailX0RatChunk001Sub000Block072Part010
    + surrogateDiagTailX0RatChunk001Sub000Block072Part011
    + surrogateDiagTailX0RatChunk001Sub000Block072Part012
    + surrogateDiagTailX0RatChunk001Sub000Block072Part013
    + surrogateDiagTailX0RatChunk001Sub000Block072Part014
    + surrogateDiagTailX0RatChunk001Sub000Block072Part015
    + surrogateDiagTailX0RatChunk001Sub000Block072Part016
    + surrogateDiagTailX0RatChunk001Sub000Block072Part017
    + surrogateDiagTailX0RatChunk001Sub000Block072Part018
    + surrogateDiagTailX0RatChunk001Sub000Block072Part019
    + surrogateDiagTailX0RatChunk001Sub000Block072Part020
    + surrogateDiagTailX0RatChunk001Sub000Block072Part021
    + surrogateDiagTailX0RatChunk001Sub000Block072Part022
    + surrogateDiagTailX0RatChunk001Sub000Block072Part023
    + surrogateDiagTailX0RatChunk001Sub000Block072Part024

theorem surrogateDiagTailX0RatChunk001Sub000Block072_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk001Sub000Block072Head + surrogateDiagTailX0RatChunk001Sub000Block072Mid + surrogateDiagTailX0RatChunk001Sub000Block072Tail =
      surrogateDiagTailX0RatChunk001Sub000Block072 := by
  unfold surrogateDiagTailX0RatChunk001Sub000Block072Head surrogateDiagTailX0RatChunk001Sub000Block072Mid surrogateDiagTailX0RatChunk001Sub000Block072Tail surrogateDiagTailX0RatChunk001Sub000Block072
  ring

def SurrogateDiagonalTailChunk001Sub000Block072HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block072HeadSum X0 = surrogateDiagTailX0RatChunk001Sub000Block072Head

def SurrogateDiagonalTailChunk001Sub000Block072MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block072MidSum X0 = surrogateDiagTailX0RatChunk001Sub000Block072Mid

def SurrogateDiagonalTailChunk001Sub000Block072TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block072TailSum X0 = surrogateDiagTailX0RatChunk001Sub000Block072Tail

theorem surrogateDiagonalTailChunk001Sub000Block072_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk001Sub000Block072HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk001Sub000Block072MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk001Sub000Block072TailCertificateAt X0) :
    surrogateDiagonalTailChunk001Sub000Block072Sum X0 = surrogateDiagTailX0RatChunk001Sub000Block072 := by
  unfold SurrogateDiagonalTailChunk001Sub000Block072HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk001Sub000Block072MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk001Sub000Block072TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk001Sub000Block072Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk001Sub000Block072_eq_head_add_mid_add_tail

/-- Block 073 covers tail-support indices [11825,11850) and q from 19505 to 19542. -/

def TailChunk001Sub000Block073Part000SupportExplicit : Finset ℕ :=
  ([19505] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block073Part000 : ℚ :=
  (523233753725 : ℚ) / 64792325059198992384

def SurrogateDiagonalTailChunk001Sub000Block073Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19505
    = surrogateDiagTailX0RatChunk001Sub000Block073Part000

theorem surrogateDiagonalTailChunk001Sub000Block073Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block073Part000CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block073Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block073Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block073Part000CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block073Part000SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block073Part000] using hcert

def TailChunk001Sub000Block073Part001SupportExplicit : Finset ℕ :=
  ([19506] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block073Part001 : ℚ :=
  (26413464749 : ℚ) / 89270975625000000

def SurrogateDiagonalTailChunk001Sub000Block073Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19506
    = surrogateDiagTailX0RatChunk001Sub000Block073Part001

theorem surrogateDiagonalTailChunk001Sub000Block073Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block073Part001CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block073Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block073Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block073Part001CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block073Part001SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block073Part001] using hcert

def TailChunk001Sub000Block073Part002SupportExplicit : Finset ℕ :=
  ([19507] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block073Part002 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block073Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19507
    = surrogateDiagTailX0RatChunk001Sub000Block073Part002

theorem surrogateDiagonalTailChunk001Sub000Block073Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block073Part002CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block073Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block073Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block073Part002CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block073Part002SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block073Part002] using hcert

def TailChunk001Sub000Block073Part003SupportExplicit : Finset ℕ :=
  ([19509] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block073Part003 : ℚ :=
  (154965968575 : ℚ) / 2403387318560882688

def SurrogateDiagonalTailChunk001Sub000Block073Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19509
    = surrogateDiagTailX0RatChunk001Sub000Block073Part003

theorem surrogateDiagonalTailChunk001Sub000Block073Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block073Part003CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block073Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block073Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block073Part003CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block073Part003SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block073Part003] using hcert

def TailChunk001Sub000Block073Part004SupportExplicit : Finset ℕ :=
  ([19510] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block073Part004 : ℚ :=
  (6352906363 : ℚ) / 123408196704000000

def SurrogateDiagonalTailChunk001Sub000Block073Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19510
    = surrogateDiagTailX0RatChunk001Sub000Block073Part004

theorem surrogateDiagonalTailChunk001Sub000Block073Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block073Part004CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block073Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block073Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block073Part004CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block073Part004SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block073Part004] using hcert

def TailChunk001Sub000Block073Part005SupportExplicit : Finset ℕ :=
  ([19511] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block073Part005 : ℚ :=
  (29663720825 : ℚ) / 113836264308534122496

def SurrogateDiagonalTailChunk001Sub000Block073Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19511
    = surrogateDiagTailX0RatChunk001Sub000Block073Part005

theorem surrogateDiagonalTailChunk001Sub000Block073Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block073Part005CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block073Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block073Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block073Part005CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block073Part005SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block073Part005] using hcert

def TailChunk001Sub000Block073Part006SupportExplicit : Finset ℕ :=
  ([19513] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block073Part006 : ℚ :=
  (730868322325 : ℚ) / 201474587027160465408

def SurrogateDiagonalTailChunk001Sub000Block073Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19513
    = surrogateDiagTailX0RatChunk001Sub000Block073Part006

theorem surrogateDiagonalTailChunk001Sub000Block073Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block073Part006CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block073Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block073Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block073Part006CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block073Part006SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block073Part006] using hcert

def TailChunk001Sub000Block073Part007SupportExplicit : Finset ℕ :=
  ([19514] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block073Part007 : ℚ :=
  (1188823687 : ℚ) / 61634196376000320

def SurrogateDiagonalTailChunk001Sub000Block073Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19514
    = surrogateDiagTailX0RatChunk001Sub000Block073Part007

theorem surrogateDiagonalTailChunk001Sub000Block073Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block073Part007CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block073Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block073Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block073Part007CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block073Part007SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block073Part007] using hcert

def TailChunk001Sub000Block073Part008SupportExplicit : Finset ℕ :=
  ([19515] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block073Part008 : ℚ :=
  (23263767793 : ℚ) / 292523132928000000

def SurrogateDiagonalTailChunk001Sub000Block073Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19515
    = surrogateDiagTailX0RatChunk001Sub000Block073Part008

theorem surrogateDiagonalTailChunk001Sub000Block073Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block073Part008CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block073Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block073Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block073Part008CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block073Part008SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block073Part008] using hcert

def TailChunk001Sub000Block073Part009SupportExplicit : Finset ℕ :=
  ([19517] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block073Part009 : ℚ :=
  (117103810625 : ℚ) / 156713381158855901184

def SurrogateDiagonalTailChunk001Sub000Block073Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19517
    = surrogateDiagTailX0RatChunk001Sub000Block073Part009

theorem surrogateDiagonalTailChunk001Sub000Block073Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block073Part009CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block073Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block073Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block073Part009CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block073Part009SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block073Part009] using hcert

def TailChunk001Sub000Block073Part010SupportExplicit : Finset ℕ :=
  ([19518] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block073Part010 : ℚ :=
  (661149206075 : ℚ) / 2237273062219736064

def SurrogateDiagonalTailChunk001Sub000Block073Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19518
    = surrogateDiagTailX0RatChunk001Sub000Block073Part010

theorem surrogateDiagonalTailChunk001Sub000Block073Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block073Part010CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block073Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block073Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block073Part010CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block073Part010SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block073Part010] using hcert

def TailChunk001Sub000Block073Part011SupportExplicit : Finset ℕ :=
  ([19519] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block073Part011 : ℚ :=
  (288970209 : ℚ) / 1142157181940569600

def SurrogateDiagonalTailChunk001Sub000Block073Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19519
    = surrogateDiagTailX0RatChunk001Sub000Block073Part011

theorem surrogateDiagonalTailChunk001Sub000Block073Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block073Part011CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block073Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block073Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block073Part011CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block073Part011SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block073Part011] using hcert

def TailChunk001Sub000Block073Part012SupportExplicit : Finset ℕ :=
  ([19522] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block073Part012 : ℚ :=
  (83133804325 : ℚ) / 20298211671938514048

def SurrogateDiagonalTailChunk001Sub000Block073Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19522
    = surrogateDiagTailX0RatChunk001Sub000Block073Part012

theorem surrogateDiagonalTailChunk001Sub000Block073Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block073Part012CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block073Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block073Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block073Part012CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block073Part012SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block073Part012] using hcert

def TailChunk001Sub000Block073Part013SupportExplicit : Finset ℕ :=
  ([19523] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block073Part013 : ℚ :=
  (486649251575 : ℚ) / 97897802297290712064

def SurrogateDiagonalTailChunk001Sub000Block073Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19523
    = surrogateDiagTailX0RatChunk001Sub000Block073Part013

theorem surrogateDiagonalTailChunk001Sub000Block073Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block073Part013CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block073Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block073Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block073Part013CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block073Part013SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block073Part013] using hcert

def TailChunk001Sub000Block073Part014SupportExplicit : Finset ℕ :=
  ([19526] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block073Part014 : ℚ :=
  (4991016107 : ℚ) / 328115610000000000

def SurrogateDiagonalTailChunk001Sub000Block073Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19526
    = surrogateDiagTailX0RatChunk001Sub000Block073Part014

theorem surrogateDiagonalTailChunk001Sub000Block073Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block073Part014CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block073Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block073Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block073Part014CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block073Part014SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block073Part014] using hcert

def TailChunk001Sub000Block073Part015SupportExplicit : Finset ℕ :=
  ([19527] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block073Part015 : ℚ :=
  (26194105225 : ℚ) / 598685587852695552

def SurrogateDiagonalTailChunk001Sub000Block073Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19527
    = surrogateDiagTailX0RatChunk001Sub000Block073Part015

theorem surrogateDiagonalTailChunk001Sub000Block073Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block073Part015CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block073Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block073Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block073Part015CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block073Part015SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block073Part015] using hcert

def TailChunk001Sub000Block073Part016SupportExplicit : Finset ℕ :=
  ([19529] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block073Part016 : ℚ :=
  (95988389 : ℚ) / 268463086937331264

def SurrogateDiagonalTailChunk001Sub000Block073Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19529
    = surrogateDiagTailX0RatChunk001Sub000Block073Part016

theorem surrogateDiagonalTailChunk001Sub000Block073Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block073Part016CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block073Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block073Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block073Part016CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block073Part016SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block073Part016] using hcert

def TailChunk001Sub000Block073Part017SupportExplicit : Finset ℕ :=
  ([19531] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block073Part017 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block073Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19531
    = surrogateDiagTailX0RatChunk001Sub000Block073Part017

theorem surrogateDiagonalTailChunk001Sub000Block073Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block073Part017CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block073Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block073Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block073Part017CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block073Part017SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block073Part017] using hcert

def TailChunk001Sub000Block073Part018SupportExplicit : Finset ℕ :=
  ([19533] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block073Part018 : ℚ :=
  (2563692199975 : ℚ) / 55831619275994431488

def SurrogateDiagonalTailChunk001Sub000Block073Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19533
    = surrogateDiagTailX0RatChunk001Sub000Block073Part018

theorem surrogateDiagonalTailChunk001Sub000Block073Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block073Part018CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block073Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block073Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block073Part018CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block073Part018SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block073Part018] using hcert

def TailChunk001Sub000Block073Part019SupportExplicit : Finset ℕ :=
  ([19534] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block073Part019 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block073Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19534
    = surrogateDiagTailX0RatChunk001Sub000Block073Part019

theorem surrogateDiagonalTailChunk001Sub000Block073Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block073Part019CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block073Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block073Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block073Part019CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block073Part019SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block073Part019] using hcert

def TailChunk001Sub000Block073Part020SupportExplicit : Finset ℕ :=
  ([19535] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block073Part020 : ℚ :=
  (635991010675 : ℚ) / 49667754440499664896

def SurrogateDiagonalTailChunk001Sub000Block073Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19535
    = surrogateDiagTailX0RatChunk001Sub000Block073Part020

theorem surrogateDiagonalTailChunk001Sub000Block073Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block073Part020CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block073Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block073Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block073Part020CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block073Part020SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block073Part020] using hcert

def TailChunk001Sub000Block073Part021SupportExplicit : Finset ℕ :=
  ([19537] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block073Part021 : ℚ :=
  (19535245573 : ℚ) / 7854321330332035200

def SurrogateDiagonalTailChunk001Sub000Block073Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19537
    = surrogateDiagTailX0RatChunk001Sub000Block073Part021

theorem surrogateDiagonalTailChunk001Sub000Block073Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block073Part021CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block073Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block073Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block073Part021CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block073Part021SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block073Part021] using hcert

def TailChunk001Sub000Block073Part022SupportExplicit : Finset ℕ :=
  ([19538] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block073Part022 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block073Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19538
    = surrogateDiagTailX0RatChunk001Sub000Block073Part022

theorem surrogateDiagonalTailChunk001Sub000Block073Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block073Part022CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block073Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block073Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block073Part022CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block073Part022SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block073Part022] using hcert

def TailChunk001Sub000Block073Part023SupportExplicit : Finset ℕ :=
  ([19541] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block073Part023 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block073Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19541
    = surrogateDiagTailX0RatChunk001Sub000Block073Part023

theorem surrogateDiagonalTailChunk001Sub000Block073Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block073Part023CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block073Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block073Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block073Part023CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block073Part023SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block073Part023] using hcert

def TailChunk001Sub000Block073Part024SupportExplicit : Finset ℕ :=
  ([19542] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block073Part024 : ℚ :=
  (662775880475 : ℚ) / 2248300881448157184

def SurrogateDiagonalTailChunk001Sub000Block073Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19542
    = surrogateDiagTailX0RatChunk001Sub000Block073Part024

theorem surrogateDiagonalTailChunk001Sub000Block073Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block073Part024CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block073Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block073Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block073Part024CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block073Part024SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block073Part024] using hcert

def surrogateDiagonalTailChunk001Sub000Block073HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block073Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block073Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block073Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block073Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block073Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block073Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block073Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block073Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block073Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block073Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block073Head : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block073Part000
    + surrogateDiagTailX0RatChunk001Sub000Block073Part001
    + surrogateDiagTailX0RatChunk001Sub000Block073Part002
    + surrogateDiagTailX0RatChunk001Sub000Block073Part003
    + surrogateDiagTailX0RatChunk001Sub000Block073Part004
    + surrogateDiagTailX0RatChunk001Sub000Block073Part005
    + surrogateDiagTailX0RatChunk001Sub000Block073Part006
    + surrogateDiagTailX0RatChunk001Sub000Block073Part007
    + surrogateDiagTailX0RatChunk001Sub000Block073Part008
    + surrogateDiagTailX0RatChunk001Sub000Block073Part009

def surrogateDiagonalTailChunk001Sub000Block073MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block073Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block073Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block073Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block073Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block073Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block073Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block073Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block073Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block073Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block073Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block073Mid : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block073Part010
    + surrogateDiagTailX0RatChunk001Sub000Block073Part011
    + surrogateDiagTailX0RatChunk001Sub000Block073Part012
    + surrogateDiagTailX0RatChunk001Sub000Block073Part013
    + surrogateDiagTailX0RatChunk001Sub000Block073Part014
    + surrogateDiagTailX0RatChunk001Sub000Block073Part015
    + surrogateDiagTailX0RatChunk001Sub000Block073Part016
    + surrogateDiagTailX0RatChunk001Sub000Block073Part017
    + surrogateDiagTailX0RatChunk001Sub000Block073Part018
    + surrogateDiagTailX0RatChunk001Sub000Block073Part019

def surrogateDiagonalTailChunk001Sub000Block073TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block073Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block073Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block073Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block073Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block073Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block073Tail : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block073Part020
    + surrogateDiagTailX0RatChunk001Sub000Block073Part021
    + surrogateDiagTailX0RatChunk001Sub000Block073Part022
    + surrogateDiagTailX0RatChunk001Sub000Block073Part023
    + surrogateDiagTailX0RatChunk001Sub000Block073Part024

def surrogateDiagonalTailChunk001Sub000Block073Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk001Sub000Block073HeadSum X0
    + surrogateDiagonalTailChunk001Sub000Block073MidSum X0
    + surrogateDiagonalTailChunk001Sub000Block073TailSum X0

def surrogateDiagTailX0RatChunk001Sub000Block073 : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block073Part000
    + surrogateDiagTailX0RatChunk001Sub000Block073Part001
    + surrogateDiagTailX0RatChunk001Sub000Block073Part002
    + surrogateDiagTailX0RatChunk001Sub000Block073Part003
    + surrogateDiagTailX0RatChunk001Sub000Block073Part004
    + surrogateDiagTailX0RatChunk001Sub000Block073Part005
    + surrogateDiagTailX0RatChunk001Sub000Block073Part006
    + surrogateDiagTailX0RatChunk001Sub000Block073Part007
    + surrogateDiagTailX0RatChunk001Sub000Block073Part008
    + surrogateDiagTailX0RatChunk001Sub000Block073Part009
    + surrogateDiagTailX0RatChunk001Sub000Block073Part010
    + surrogateDiagTailX0RatChunk001Sub000Block073Part011
    + surrogateDiagTailX0RatChunk001Sub000Block073Part012
    + surrogateDiagTailX0RatChunk001Sub000Block073Part013
    + surrogateDiagTailX0RatChunk001Sub000Block073Part014
    + surrogateDiagTailX0RatChunk001Sub000Block073Part015
    + surrogateDiagTailX0RatChunk001Sub000Block073Part016
    + surrogateDiagTailX0RatChunk001Sub000Block073Part017
    + surrogateDiagTailX0RatChunk001Sub000Block073Part018
    + surrogateDiagTailX0RatChunk001Sub000Block073Part019
    + surrogateDiagTailX0RatChunk001Sub000Block073Part020
    + surrogateDiagTailX0RatChunk001Sub000Block073Part021
    + surrogateDiagTailX0RatChunk001Sub000Block073Part022
    + surrogateDiagTailX0RatChunk001Sub000Block073Part023
    + surrogateDiagTailX0RatChunk001Sub000Block073Part024

theorem surrogateDiagTailX0RatChunk001Sub000Block073_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk001Sub000Block073Head + surrogateDiagTailX0RatChunk001Sub000Block073Mid + surrogateDiagTailX0RatChunk001Sub000Block073Tail =
      surrogateDiagTailX0RatChunk001Sub000Block073 := by
  unfold surrogateDiagTailX0RatChunk001Sub000Block073Head surrogateDiagTailX0RatChunk001Sub000Block073Mid surrogateDiagTailX0RatChunk001Sub000Block073Tail surrogateDiagTailX0RatChunk001Sub000Block073
  ring

def SurrogateDiagonalTailChunk001Sub000Block073HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block073HeadSum X0 = surrogateDiagTailX0RatChunk001Sub000Block073Head

def SurrogateDiagonalTailChunk001Sub000Block073MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block073MidSum X0 = surrogateDiagTailX0RatChunk001Sub000Block073Mid

def SurrogateDiagonalTailChunk001Sub000Block073TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block073TailSum X0 = surrogateDiagTailX0RatChunk001Sub000Block073Tail

theorem surrogateDiagonalTailChunk001Sub000Block073_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk001Sub000Block073HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk001Sub000Block073MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk001Sub000Block073TailCertificateAt X0) :
    surrogateDiagonalTailChunk001Sub000Block073Sum X0 = surrogateDiagTailX0RatChunk001Sub000Block073 := by
  unfold SurrogateDiagonalTailChunk001Sub000Block073HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk001Sub000Block073MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk001Sub000Block073TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk001Sub000Block073Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk001Sub000Block073_eq_head_add_mid_add_tail

/-- Block 074 covers tail-support indices [11850,11875) and q from 19543 to 19583. -/

def TailChunk001Sub000Block074Part000SupportExplicit : Finset ℕ :=
  ([19543] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block074Part000 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block074Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19543
    = surrogateDiagTailX0RatChunk001Sub000Block074Part000

theorem surrogateDiagonalTailChunk001Sub000Block074Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block074Part000CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block074Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block074Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block074Part000CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block074Part000SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block074Part000] using hcert

def TailChunk001Sub000Block074Part001SupportExplicit : Finset ℕ :=
  ([19545] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block074Part001 : ℚ :=
  (441791239075 : ℚ) / 4905457228691324928

def SurrogateDiagonalTailChunk001Sub000Block074Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19545
    = surrogateDiagTailX0RatChunk001Sub000Block074Part001

theorem surrogateDiagonalTailChunk001Sub000Block074Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block074Part001CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block074Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block074Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block074Part001CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block074Part001SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block074Part001] using hcert

def TailChunk001Sub000Block074Part002SupportExplicit : Finset ℕ :=
  ([19546] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block074Part002 : ℚ :=
  (114274016725 : ℚ) / 19589172644856987648

def SurrogateDiagonalTailChunk001Sub000Block074Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19546
    = surrogateDiagTailX0RatChunk001Sub000Block074Part002

theorem surrogateDiagonalTailChunk001Sub000Block074Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block074Part002CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block074Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block074Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block074Part002CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block074Part002SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block074Part002] using hcert

def TailChunk001Sub000Block074Part003SupportExplicit : Finset ℕ :=
  ([19547] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block074Part003 : ℚ :=
  (23771952673 : ℚ) / 9950816004223795200

def SurrogateDiagonalTailChunk001Sub000Block074Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19547
    = surrogateDiagTailX0RatChunk001Sub000Block074Part003

theorem surrogateDiagonalTailChunk001Sub000Block074Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block074Part003CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block074Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block074Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block074Part003CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block074Part003SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block074Part003] using hcert

def TailChunk001Sub000Block074Part004SupportExplicit : Finset ℕ :=
  ([19549] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block074Part004 : ℚ :=
  (88901526775 : ℚ) / 344360030169578078208

def SurrogateDiagonalTailChunk001Sub000Block074Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19549
    = surrogateDiagTailX0RatChunk001Sub000Block074Part004

theorem surrogateDiagonalTailChunk001Sub000Block074Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block074Part004CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block074Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block074Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block074Part004CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block074Part004SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block074Part004] using hcert

def TailChunk001Sub000Block074Part005SupportExplicit : Finset ℕ :=
  ([19553] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block074Part005 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block074Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19553
    = surrogateDiagTailX0RatChunk001Sub000Block074Part005

theorem surrogateDiagonalTailChunk001Sub000Block074Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block074Part005CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block074Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block074Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block074Part005CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block074Part005SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block074Part005] using hcert

def TailChunk001Sub000Block074Part006SupportExplicit : Finset ℕ :=
  ([19554] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block074Part006 : ℚ :=
  (332017678025 : ℚ) / 2253830054077560384

def SurrogateDiagonalTailChunk001Sub000Block074Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19554
    = surrogateDiagTailX0RatChunk001Sub000Block074Part006

theorem surrogateDiagonalTailChunk001Sub000Block074Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block074Part006CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block074Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block074Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block074Part006CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block074Part006SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block074Part006] using hcert

def TailChunk001Sub000Block074Part007SupportExplicit : Finset ℕ :=
  ([19555] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block074Part007 : ℚ :=
  (76475209969 : ℚ) / 5984582318344243200

def SurrogateDiagonalTailChunk001Sub000Block074Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19555
    = surrogateDiagTailX0RatChunk001Sub000Block074Part007

theorem surrogateDiagonalTailChunk001Sub000Block074Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block074Part007CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block074Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block074Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block074Part007CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block074Part007SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block074Part007] using hcert

def TailChunk001Sub000Block074Part008SupportExplicit : Finset ℕ :=
  ([19558] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block074Part008 : ℚ :=
  (13168263713 : ℚ) / 163359364987929600

def SurrogateDiagonalTailChunk001Sub000Block074Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19558
    = surrogateDiagTailX0RatChunk001Sub000Block074Part008

theorem surrogateDiagonalTailChunk001Sub000Block074Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block074Part008CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block074Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block074Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block074Part008CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block074Part008SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block074Part008] using hcert

def TailChunk001Sub000Block074Part009SupportExplicit : Finset ℕ :=
  ([19559] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block074Part009 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block074Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19559
    = surrogateDiagTailX0RatChunk001Sub000Block074Part009

theorem surrogateDiagonalTailChunk001Sub000Block074Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block074Part009CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block074Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block074Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block074Part009CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block074Part009SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block074Part009] using hcert

def TailChunk001Sub000Block074Part010SupportExplicit : Finset ℕ :=
  ([19561] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block074Part010 : ℚ :=
  (518831359 : ℚ) / 797653149355125000

def SurrogateDiagonalTailChunk001Sub000Block074Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19561
    = surrogateDiagTailX0RatChunk001Sub000Block074Part010

theorem surrogateDiagonalTailChunk001Sub000Block074Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block074Part010CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block074Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block074Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block074Part010CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block074Part010SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block074Part010] using hcert

def TailChunk001Sub000Block074Part011SupportExplicit : Finset ℕ :=
  ([19562] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block074Part011 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block074Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19562
    = surrogateDiagTailX0RatChunk001Sub000Block074Part011

theorem surrogateDiagonalTailChunk001Sub000Block074Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block074Part011CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block074Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block074Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block074Part011CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block074Part011SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block074Part011] using hcert

def TailChunk001Sub000Block074Part012SupportExplicit : Finset ℕ :=
  ([19563] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block074Part012 : ℚ :=
  (5315050049 : ℚ) / 144599642798530560

def SurrogateDiagonalTailChunk001Sub000Block074Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19563
    = surrogateDiagTailX0RatChunk001Sub000Block074Part012

theorem surrogateDiagonalTailChunk001Sub000Block074Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block074Part012CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block074Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block074Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block074Part012CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block074Part012SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block074Part012] using hcert

def TailChunk001Sub000Block074Part013SupportExplicit : Finset ℕ :=
  ([19565] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block074Part013 : ℚ :=
  (523330515325 : ℚ) / 13382399179811192832

def SurrogateDiagonalTailChunk001Sub000Block074Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19565
    = surrogateDiagTailX0RatChunk001Sub000Block074Part013

theorem surrogateDiagonalTailChunk001Sub000Block074Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block074Part013CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block074Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block074Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block074Part013CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block074Part013SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block074Part013] using hcert

def TailChunk001Sub000Block074Part014SupportExplicit : Finset ℕ :=
  ([19567] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block074Part014 : ℚ :=
  (13417017883 : ℚ) / 11464579817472000000

def SurrogateDiagonalTailChunk001Sub000Block074Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19567
    = surrogateDiagTailX0RatChunk001Sub000Block074Part014

theorem surrogateDiagonalTailChunk001Sub000Block074Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block074Part014CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block074Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block074Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block074Part014CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block074Part014SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block074Part014] using hcert

def TailChunk001Sub000Block074Part015SupportExplicit : Finset ℕ :=
  ([19569] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block074Part015 : ℚ :=
  (99261825703 : ℚ) / 1965593284784947200

def SurrogateDiagonalTailChunk001Sub000Block074Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19569
    = surrogateDiagTailX0RatChunk001Sub000Block074Part015

theorem surrogateDiagonalTailChunk001Sub000Block074Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block074Part015CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block074Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block074Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block074Part015CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block074Part015SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block074Part015] using hcert

def TailChunk001Sub000Block074Part016SupportExplicit : Finset ℕ :=
  ([19570] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block074Part016 : ℚ :=
  (780779186875 : ℚ) / 7273735955702120448

def SurrogateDiagonalTailChunk001Sub000Block074Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19570
    = surrogateDiagTailX0RatChunk001Sub000Block074Part016

theorem surrogateDiagonalTailChunk001Sub000Block074Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block074Part016CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block074Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block074Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block074Part016CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block074Part016SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block074Part016] using hcert

def TailChunk001Sub000Block074Part017SupportExplicit : Finset ℕ :=
  ([19571] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block074Part017 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block074Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19571
    = surrogateDiagTailX0RatChunk001Sub000Block074Part017

theorem surrogateDiagonalTailChunk001Sub000Block074Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block074Part017CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block074Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block074Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block074Part017CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block074Part017SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block074Part017] using hcert

def TailChunk001Sub000Block074Part018SupportExplicit : Finset ℕ :=
  ([19574] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block074Part018 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block074Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19574
    = surrogateDiagTailX0RatChunk001Sub000Block074Part018

theorem surrogateDiagonalTailChunk001Sub000Block074Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block074Part018CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block074Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block074Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block074Part018CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block074Part018SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block074Part018] using hcert

def TailChunk001Sub000Block074Part019SupportExplicit : Finset ℕ :=
  ([19577] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block074Part019 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block074Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19577
    = surrogateDiagTailX0RatChunk001Sub000Block074Part019

theorem surrogateDiagonalTailChunk001Sub000Block074Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block074Part019CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block074Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block074Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block074Part019CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block074Part019SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block074Part019] using hcert

def TailChunk001Sub000Block074Part020SupportExplicit : Finset ℕ :=
  ([19578] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block074Part020 : ℚ :=
  (14212830197 : ℚ) / 64812960000000000

def SurrogateDiagonalTailChunk001Sub000Block074Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19578
    = surrogateDiagTailX0RatChunk001Sub000Block074Part020

theorem surrogateDiagonalTailChunk001Sub000Block074Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block074Part020CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block074Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block074Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block074Part020CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block074Part020SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block074Part020] using hcert

def TailChunk001Sub000Block074Part021SupportExplicit : Finset ℕ :=
  ([19579] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block074Part021 : ℚ :=
  (489440693375 : ℚ) / 99026295574853919744

def SurrogateDiagonalTailChunk001Sub000Block074Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19579
    = surrogateDiagTailX0RatChunk001Sub000Block074Part021

theorem surrogateDiagonalTailChunk001Sub000Block074Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block074Part021CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block074Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block074Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block074Part021CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block074Part021SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block074Part021] using hcert

def TailChunk001Sub000Block074Part022SupportExplicit : Finset ℕ :=
  ([19581] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block074Part022 : ℚ :=
  (350820899 : ℚ) / 8727985995669504

def SurrogateDiagonalTailChunk001Sub000Block074Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19581
    = surrogateDiagTailX0RatChunk001Sub000Block074Part022

theorem surrogateDiagonalTailChunk001Sub000Block074Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block074Part022CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block074Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block074Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block074Part022CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block074Part022SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block074Part022] using hcert

def TailChunk001Sub000Block074Part023SupportExplicit : Finset ℕ :=
  ([19582] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block074Part023 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block074Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19582
    = surrogateDiagTailX0RatChunk001Sub000Block074Part023

theorem surrogateDiagonalTailChunk001Sub000Block074Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block074Part023CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block074Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block074Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block074Part023CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block074Part023SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block074Part023] using hcert

def TailChunk001Sub000Block074Part024SupportExplicit : Finset ℕ :=
  ([19583] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block074Part024 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block074Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19583
    = surrogateDiagTailX0RatChunk001Sub000Block074Part024

theorem surrogateDiagonalTailChunk001Sub000Block074Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block074Part024CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block074Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block074Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block074Part024CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block074Part024SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block074Part024] using hcert

def surrogateDiagonalTailChunk001Sub000Block074HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block074Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block074Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block074Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block074Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block074Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block074Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block074Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block074Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block074Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block074Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block074Head : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block074Part000
    + surrogateDiagTailX0RatChunk001Sub000Block074Part001
    + surrogateDiagTailX0RatChunk001Sub000Block074Part002
    + surrogateDiagTailX0RatChunk001Sub000Block074Part003
    + surrogateDiagTailX0RatChunk001Sub000Block074Part004
    + surrogateDiagTailX0RatChunk001Sub000Block074Part005
    + surrogateDiagTailX0RatChunk001Sub000Block074Part006
    + surrogateDiagTailX0RatChunk001Sub000Block074Part007
    + surrogateDiagTailX0RatChunk001Sub000Block074Part008
    + surrogateDiagTailX0RatChunk001Sub000Block074Part009

def surrogateDiagonalTailChunk001Sub000Block074MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block074Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block074Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block074Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block074Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block074Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block074Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block074Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block074Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block074Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block074Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block074Mid : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block074Part010
    + surrogateDiagTailX0RatChunk001Sub000Block074Part011
    + surrogateDiagTailX0RatChunk001Sub000Block074Part012
    + surrogateDiagTailX0RatChunk001Sub000Block074Part013
    + surrogateDiagTailX0RatChunk001Sub000Block074Part014
    + surrogateDiagTailX0RatChunk001Sub000Block074Part015
    + surrogateDiagTailX0RatChunk001Sub000Block074Part016
    + surrogateDiagTailX0RatChunk001Sub000Block074Part017
    + surrogateDiagTailX0RatChunk001Sub000Block074Part018
    + surrogateDiagTailX0RatChunk001Sub000Block074Part019

def surrogateDiagonalTailChunk001Sub000Block074TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block074Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block074Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block074Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block074Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block074Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block074Tail : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block074Part020
    + surrogateDiagTailX0RatChunk001Sub000Block074Part021
    + surrogateDiagTailX0RatChunk001Sub000Block074Part022
    + surrogateDiagTailX0RatChunk001Sub000Block074Part023
    + surrogateDiagTailX0RatChunk001Sub000Block074Part024

def surrogateDiagonalTailChunk001Sub000Block074Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk001Sub000Block074HeadSum X0
    + surrogateDiagonalTailChunk001Sub000Block074MidSum X0
    + surrogateDiagonalTailChunk001Sub000Block074TailSum X0

def surrogateDiagTailX0RatChunk001Sub000Block074 : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block074Part000
    + surrogateDiagTailX0RatChunk001Sub000Block074Part001
    + surrogateDiagTailX0RatChunk001Sub000Block074Part002
    + surrogateDiagTailX0RatChunk001Sub000Block074Part003
    + surrogateDiagTailX0RatChunk001Sub000Block074Part004
    + surrogateDiagTailX0RatChunk001Sub000Block074Part005
    + surrogateDiagTailX0RatChunk001Sub000Block074Part006
    + surrogateDiagTailX0RatChunk001Sub000Block074Part007
    + surrogateDiagTailX0RatChunk001Sub000Block074Part008
    + surrogateDiagTailX0RatChunk001Sub000Block074Part009
    + surrogateDiagTailX0RatChunk001Sub000Block074Part010
    + surrogateDiagTailX0RatChunk001Sub000Block074Part011
    + surrogateDiagTailX0RatChunk001Sub000Block074Part012
    + surrogateDiagTailX0RatChunk001Sub000Block074Part013
    + surrogateDiagTailX0RatChunk001Sub000Block074Part014
    + surrogateDiagTailX0RatChunk001Sub000Block074Part015
    + surrogateDiagTailX0RatChunk001Sub000Block074Part016
    + surrogateDiagTailX0RatChunk001Sub000Block074Part017
    + surrogateDiagTailX0RatChunk001Sub000Block074Part018
    + surrogateDiagTailX0RatChunk001Sub000Block074Part019
    + surrogateDiagTailX0RatChunk001Sub000Block074Part020
    + surrogateDiagTailX0RatChunk001Sub000Block074Part021
    + surrogateDiagTailX0RatChunk001Sub000Block074Part022
    + surrogateDiagTailX0RatChunk001Sub000Block074Part023
    + surrogateDiagTailX0RatChunk001Sub000Block074Part024

theorem surrogateDiagTailX0RatChunk001Sub000Block074_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk001Sub000Block074Head + surrogateDiagTailX0RatChunk001Sub000Block074Mid + surrogateDiagTailX0RatChunk001Sub000Block074Tail =
      surrogateDiagTailX0RatChunk001Sub000Block074 := by
  unfold surrogateDiagTailX0RatChunk001Sub000Block074Head surrogateDiagTailX0RatChunk001Sub000Block074Mid surrogateDiagTailX0RatChunk001Sub000Block074Tail surrogateDiagTailX0RatChunk001Sub000Block074
  ring

def SurrogateDiagonalTailChunk001Sub000Block074HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block074HeadSum X0 = surrogateDiagTailX0RatChunk001Sub000Block074Head

def SurrogateDiagonalTailChunk001Sub000Block074MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block074MidSum X0 = surrogateDiagTailX0RatChunk001Sub000Block074Mid

def SurrogateDiagonalTailChunk001Sub000Block074TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block074TailSum X0 = surrogateDiagTailX0RatChunk001Sub000Block074Tail

theorem surrogateDiagonalTailChunk001Sub000Block074_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk001Sub000Block074HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk001Sub000Block074MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk001Sub000Block074TailCertificateAt X0) :
    surrogateDiagonalTailChunk001Sub000Block074Sum X0 = surrogateDiagTailX0RatChunk001Sub000Block074 := by
  unfold SurrogateDiagonalTailChunk001Sub000Block074HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk001Sub000Block074MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk001Sub000Block074TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk001Sub000Block074Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk001Sub000Block074_eq_head_add_mid_add_tail

/-- Block 075 covers tail-support indices [11875,11900) and q from 19585 to 19621. -/

def TailChunk001Sub000Block075Part000SupportExplicit : Finset ℕ :=
  ([19585] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block075Part000 : ℚ :=
  (319897232625 : ℚ) / 50178341399816667136

def SurrogateDiagonalTailChunk001Sub000Block075Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19585
    = surrogateDiagTailX0RatChunk001Sub000Block075Part000

theorem surrogateDiagonalTailChunk001Sub000Block075Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block075Part000CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block075Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block075Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block075Part000CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block075Part000SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block075Part000] using hcert

def TailChunk001Sub000Block075Part001SupportExplicit : Finset ℕ :=
  ([19586] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block075Part001 : ℚ :=
  (6818125825 : ℚ) / 229227536052902592

def SurrogateDiagonalTailChunk001Sub000Block075Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19586
    = surrogateDiagTailX0RatChunk001Sub000Block075Part001

theorem surrogateDiagonalTailChunk001Sub000Block075Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block075Part001CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block075Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block075Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block075Part001CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block075Part001SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block075Part001] using hcert

def TailChunk001Sub000Block075Part002SupportExplicit : Finset ℕ :=
  ([19587] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block075Part002 : ℚ :=
  (666012256075 : ℚ) / 18163830193297293312

def SurrogateDiagonalTailChunk001Sub000Block075Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19587
    = surrogateDiagTailX0RatChunk001Sub000Block075Part002

theorem surrogateDiagonalTailChunk001Sub000Block075Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block075Part002CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block075Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block075Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block075Part002CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block075Part002SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block075Part002] using hcert

def TailChunk001Sub000Block075Part003SupportExplicit : Finset ℕ :=
  ([19589] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block075Part003 : ℚ :=
  (2245923887 : ℚ) / 1969584052018795200

def SurrogateDiagonalTailChunk001Sub000Block075Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19589
    = surrogateDiagTailX0RatChunk001Sub000Block075Part003

theorem surrogateDiagonalTailChunk001Sub000Block075Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block075Part003CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block075Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block075Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block075Part003CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block075Part003SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block075Part003] using hcert

def TailChunk001Sub000Block075Part004SupportExplicit : Finset ℕ :=
  ([19590] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block075Part004 : ℚ :=
  (386553214925 : ℚ) / 925437713910595584

def SurrogateDiagonalTailChunk001Sub000Block075Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19590
    = surrogateDiagTailX0RatChunk001Sub000Block075Part004

theorem surrogateDiagonalTailChunk001Sub000Block075Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block075Part004CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block075Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block075Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block075Part004CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block075Part004SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block075Part004] using hcert

def TailChunk001Sub000Block075Part005SupportExplicit : Finset ℕ :=
  ([19591] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block075Part005 : ℚ :=
  (41346654241 : ℚ) / 7095246169256755200

def SurrogateDiagonalTailChunk001Sub000Block075Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19591
    = surrogateDiagTailX0RatChunk001Sub000Block075Part005

theorem surrogateDiagonalTailChunk001Sub000Block075Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block075Part005CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block075Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block075Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block075Part005CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block075Part005SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block075Part005] using hcert

def TailChunk001Sub000Block075Part006SupportExplicit : Finset ℕ :=
  ([19594] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block075Part006 : ℚ :=
  (2447850241 : ℚ) / 849516429312000000

def SurrogateDiagonalTailChunk001Sub000Block075Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19594
    = surrogateDiagTailX0RatChunk001Sub000Block075Part006

theorem surrogateDiagonalTailChunk001Sub000Block075Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block075Part006CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block075Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block075Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block075Part006CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block075Part006SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block075Part006] using hcert

def TailChunk001Sub000Block075Part007SupportExplicit : Finset ℕ :=
  ([19595] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block075Part007 : ℚ :=
  (960670947625 : ℚ) / 150842788012570134528

def SurrogateDiagonalTailChunk001Sub000Block075Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19595
    = surrogateDiagTailX0RatChunk001Sub000Block075Part007

theorem surrogateDiagonalTailChunk001Sub000Block075Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block075Part007CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block075Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block075Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block075Part007CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block075Part007SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block075Part007] using hcert

def TailChunk001Sub000Block075Part008SupportExplicit : Finset ℕ :=
  ([19597] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block075Part008 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block075Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19597
    = surrogateDiagTailX0RatChunk001Sub000Block075Part008

theorem surrogateDiagonalTailChunk001Sub000Block075Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block075Part008CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block075Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block075Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block075Part008CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block075Part008SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block075Part008] using hcert

def TailChunk001Sub000Block075Part009SupportExplicit : Finset ℕ :=
  ([19598] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block075Part009 : ℚ :=
  (3321584989 : ℚ) / 821551217804083200

def SurrogateDiagonalTailChunk001Sub000Block075Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19598
    = surrogateDiagTailX0RatChunk001Sub000Block075Part009

theorem surrogateDiagonalTailChunk001Sub000Block075Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block075Part009CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block075Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block075Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block075Part009CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block075Part009SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block075Part009] using hcert

def TailChunk001Sub000Block075Part010SupportExplicit : Finset ℕ :=
  ([19599] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block075Part010 : ℚ :=
  (73096033025 : ℚ) / 1804645957894414848

def SurrogateDiagonalTailChunk001Sub000Block075Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19599
    = surrogateDiagTailX0RatChunk001Sub000Block075Part010

theorem surrogateDiagonalTailChunk001Sub000Block075Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block075Part010CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block075Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block075Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block075Part010CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block075Part010SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block075Part010] using hcert

def TailChunk001Sub000Block075Part011SupportExplicit : Finset ℕ :=
  ([19601] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block075Part011 : ℚ :=
  (336575756275 : ℚ) / 288613542759852146688

def SurrogateDiagonalTailChunk001Sub000Block075Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19601
    = surrogateDiagTailX0RatChunk001Sub000Block075Part011

theorem surrogateDiagonalTailChunk001Sub000Block075Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block075Part011CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block075Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block075Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block075Part011CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block075Part011SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block075Part011] using hcert

def TailChunk001Sub000Block075Part012SupportExplicit : Finset ℕ :=
  ([19603] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block075Part012 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block075Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19603
    = surrogateDiagTailX0RatChunk001Sub000Block075Part012

theorem surrogateDiagonalTailChunk001Sub000Block075Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block075Part012CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block075Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block075Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block075Part012CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block075Part012SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block075Part012] using hcert

def TailChunk001Sub000Block075Part013SupportExplicit : Finset ℕ :=
  ([19605] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block075Part013 : ℚ :=
  (146742340975 : ℚ) / 1862256642130495488

def SurrogateDiagonalTailChunk001Sub000Block075Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19605
    = surrogateDiagTailX0RatChunk001Sub000Block075Part013

theorem surrogateDiagonalTailChunk001Sub000Block075Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block075Part013CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block075Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block075Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block075Part013CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block075Part013SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block075Part013] using hcert

def TailChunk001Sub000Block075Part014SupportExplicit : Finset ℕ :=
  ([19606] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block075Part014 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block075Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19606
    = surrogateDiagTailX0RatChunk001Sub000Block075Part014

theorem surrogateDiagonalTailChunk001Sub000Block075Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block075Part014CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block075Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block075Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block075Part014CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block075Part014SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block075Part014] using hcert

def TailChunk001Sub000Block075Part015SupportExplicit : Finset ℕ :=
  ([19607] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block075Part015 : ℚ :=
  (19633576547 : ℚ) / 3983767474176000000

def SurrogateDiagonalTailChunk001Sub000Block075Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19607
    = surrogateDiagTailX0RatChunk001Sub000Block075Part015

theorem surrogateDiagonalTailChunk001Sub000Block075Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block075Part015CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block075Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block075Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block075Part015CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block075Part015SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block075Part015] using hcert

def TailChunk001Sub000Block075Part016SupportExplicit : Finset ℕ :=
  ([19609] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block075Part016 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block075Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19609
    = surrogateDiagTailX0RatChunk001Sub000Block075Part016

theorem surrogateDiagonalTailChunk001Sub000Block075Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block075Part016CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block075Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block075Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block075Part016CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block075Part016SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block075Part016] using hcert

def TailChunk001Sub000Block075Part017SupportExplicit : Finset ℕ :=
  ([19610] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block075Part017 : ℚ :=
  (4047703373875 : ℚ) / 7861224550975930368

def SurrogateDiagonalTailChunk001Sub000Block075Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19610
    = surrogateDiagTailX0RatChunk001Sub000Block075Part017

theorem surrogateDiagonalTailChunk001Sub000Block075Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block075Part017CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block075Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block075Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block075Part017CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block075Part017SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block075Part017] using hcert

def TailChunk001Sub000Block075Part018SupportExplicit : Finset ℕ :=
  ([19613] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block075Part018 : ℚ :=
  (23931998503 : ℚ) / 10085969465110915200

def SurrogateDiagonalTailChunk001Sub000Block075Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19613
    = surrogateDiagTailX0RatChunk001Sub000Block075Part018

theorem surrogateDiagonalTailChunk001Sub000Block075Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block075Part018CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block075Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block075Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block075Part018CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block075Part018SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block075Part018] using hcert

def TailChunk001Sub000Block075Part019SupportExplicit : Finset ℕ :=
  ([19614] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block075Part019 : ℚ :=
  (49842260525 : ℚ) / 45279513294400512

def SurrogateDiagonalTailChunk001Sub000Block075Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19614
    = surrogateDiagTailX0RatChunk001Sub000Block075Part019

theorem surrogateDiagonalTailChunk001Sub000Block075Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block075Part019CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block075Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block075Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block075Part019CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block075Part019SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block075Part019] using hcert

def TailChunk001Sub000Block075Part020SupportExplicit : Finset ℕ :=
  ([19615] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block075Part020 : ℚ :=
  (8672350875 : ℚ) / 1364502082218047488

def SurrogateDiagonalTailChunk001Sub000Block075Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19615
    = surrogateDiagTailX0RatChunk001Sub000Block075Part020

theorem surrogateDiagonalTailChunk001Sub000Block075Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block075Part020CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block075Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block075Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block075Part020CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block075Part020SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block075Part020] using hcert

def TailChunk001Sub000Block075Part021SupportExplicit : Finset ℕ :=
  ([19617] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block075Part021 : ℚ :=
  (9934588075 : ℚ) / 205800643790218368

def SurrogateDiagonalTailChunk001Sub000Block075Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19617
    = surrogateDiagTailX0RatChunk001Sub000Block075Part021

theorem surrogateDiagonalTailChunk001Sub000Block075Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block075Part021CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block075Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block075Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block075Part021CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block075Part021SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block075Part021] using hcert

def TailChunk001Sub000Block075Part022SupportExplicit : Finset ℕ :=
  ([19618] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block075Part022 : ℚ :=
  (5480114855125 : ℚ) / 18038346422490759168

def SurrogateDiagonalTailChunk001Sub000Block075Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19618
    = surrogateDiagTailX0RatChunk001Sub000Block075Part022

theorem surrogateDiagonalTailChunk001Sub000Block075Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block075Part022CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block075Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block075Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block075Part022CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block075Part022SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block075Part022] using hcert

def TailChunk001Sub000Block075Part023SupportExplicit : Finset ℕ :=
  ([19619] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block075Part023 : ℚ :=
  (278806544575 : ℚ) / 308656879538479515648

def SurrogateDiagonalTailChunk001Sub000Block075Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19619
    = surrogateDiagTailX0RatChunk001Sub000Block075Part023

theorem surrogateDiagonalTailChunk001Sub000Block075Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block075Part023CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block075Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block075Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block075Part023CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block075Part023SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block075Part023] using hcert

def TailChunk001Sub000Block075Part024SupportExplicit : Finset ℕ :=
  ([19621] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block075Part024 : ℚ :=
  (491539523675 : ℚ) / 99879046699354795584

def SurrogateDiagonalTailChunk001Sub000Block075Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19621
    = surrogateDiagTailX0RatChunk001Sub000Block075Part024

theorem surrogateDiagonalTailChunk001Sub000Block075Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block075Part024CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block075Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block075Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block075Part024CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block075Part024SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block075Part024] using hcert

def surrogateDiagonalTailChunk001Sub000Block075HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block075Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block075Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block075Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block075Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block075Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block075Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block075Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block075Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block075Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block075Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block075Head : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block075Part000
    + surrogateDiagTailX0RatChunk001Sub000Block075Part001
    + surrogateDiagTailX0RatChunk001Sub000Block075Part002
    + surrogateDiagTailX0RatChunk001Sub000Block075Part003
    + surrogateDiagTailX0RatChunk001Sub000Block075Part004
    + surrogateDiagTailX0RatChunk001Sub000Block075Part005
    + surrogateDiagTailX0RatChunk001Sub000Block075Part006
    + surrogateDiagTailX0RatChunk001Sub000Block075Part007
    + surrogateDiagTailX0RatChunk001Sub000Block075Part008
    + surrogateDiagTailX0RatChunk001Sub000Block075Part009

def surrogateDiagonalTailChunk001Sub000Block075MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block075Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block075Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block075Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block075Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block075Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block075Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block075Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block075Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block075Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block075Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block075Mid : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block075Part010
    + surrogateDiagTailX0RatChunk001Sub000Block075Part011
    + surrogateDiagTailX0RatChunk001Sub000Block075Part012
    + surrogateDiagTailX0RatChunk001Sub000Block075Part013
    + surrogateDiagTailX0RatChunk001Sub000Block075Part014
    + surrogateDiagTailX0RatChunk001Sub000Block075Part015
    + surrogateDiagTailX0RatChunk001Sub000Block075Part016
    + surrogateDiagTailX0RatChunk001Sub000Block075Part017
    + surrogateDiagTailX0RatChunk001Sub000Block075Part018
    + surrogateDiagTailX0RatChunk001Sub000Block075Part019

def surrogateDiagonalTailChunk001Sub000Block075TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block075Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block075Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block075Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block075Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block075Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block075Tail : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block075Part020
    + surrogateDiagTailX0RatChunk001Sub000Block075Part021
    + surrogateDiagTailX0RatChunk001Sub000Block075Part022
    + surrogateDiagTailX0RatChunk001Sub000Block075Part023
    + surrogateDiagTailX0RatChunk001Sub000Block075Part024

def surrogateDiagonalTailChunk001Sub000Block075Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk001Sub000Block075HeadSum X0
    + surrogateDiagonalTailChunk001Sub000Block075MidSum X0
    + surrogateDiagonalTailChunk001Sub000Block075TailSum X0

def surrogateDiagTailX0RatChunk001Sub000Block075 : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block075Part000
    + surrogateDiagTailX0RatChunk001Sub000Block075Part001
    + surrogateDiagTailX0RatChunk001Sub000Block075Part002
    + surrogateDiagTailX0RatChunk001Sub000Block075Part003
    + surrogateDiagTailX0RatChunk001Sub000Block075Part004
    + surrogateDiagTailX0RatChunk001Sub000Block075Part005
    + surrogateDiagTailX0RatChunk001Sub000Block075Part006
    + surrogateDiagTailX0RatChunk001Sub000Block075Part007
    + surrogateDiagTailX0RatChunk001Sub000Block075Part008
    + surrogateDiagTailX0RatChunk001Sub000Block075Part009
    + surrogateDiagTailX0RatChunk001Sub000Block075Part010
    + surrogateDiagTailX0RatChunk001Sub000Block075Part011
    + surrogateDiagTailX0RatChunk001Sub000Block075Part012
    + surrogateDiagTailX0RatChunk001Sub000Block075Part013
    + surrogateDiagTailX0RatChunk001Sub000Block075Part014
    + surrogateDiagTailX0RatChunk001Sub000Block075Part015
    + surrogateDiagTailX0RatChunk001Sub000Block075Part016
    + surrogateDiagTailX0RatChunk001Sub000Block075Part017
    + surrogateDiagTailX0RatChunk001Sub000Block075Part018
    + surrogateDiagTailX0RatChunk001Sub000Block075Part019
    + surrogateDiagTailX0RatChunk001Sub000Block075Part020
    + surrogateDiagTailX0RatChunk001Sub000Block075Part021
    + surrogateDiagTailX0RatChunk001Sub000Block075Part022
    + surrogateDiagTailX0RatChunk001Sub000Block075Part023
    + surrogateDiagTailX0RatChunk001Sub000Block075Part024

theorem surrogateDiagTailX0RatChunk001Sub000Block075_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk001Sub000Block075Head + surrogateDiagTailX0RatChunk001Sub000Block075Mid + surrogateDiagTailX0RatChunk001Sub000Block075Tail =
      surrogateDiagTailX0RatChunk001Sub000Block075 := by
  unfold surrogateDiagTailX0RatChunk001Sub000Block075Head surrogateDiagTailX0RatChunk001Sub000Block075Mid surrogateDiagTailX0RatChunk001Sub000Block075Tail surrogateDiagTailX0RatChunk001Sub000Block075
  ring

def SurrogateDiagonalTailChunk001Sub000Block075HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block075HeadSum X0 = surrogateDiagTailX0RatChunk001Sub000Block075Head

def SurrogateDiagonalTailChunk001Sub000Block075MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block075MidSum X0 = surrogateDiagTailX0RatChunk001Sub000Block075Mid

def SurrogateDiagonalTailChunk001Sub000Block075TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block075TailSum X0 = surrogateDiagTailX0RatChunk001Sub000Block075Tail

theorem surrogateDiagonalTailChunk001Sub000Block075_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk001Sub000Block075HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk001Sub000Block075MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk001Sub000Block075TailCertificateAt X0) :
    surrogateDiagonalTailChunk001Sub000Block075Sum X0 = surrogateDiagTailX0RatChunk001Sub000Block075 := by
  unfold SurrogateDiagonalTailChunk001Sub000Block075HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk001Sub000Block075MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk001Sub000Block075TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk001Sub000Block075Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk001Sub000Block075_eq_head_add_mid_add_tail

/-- Block 076 covers tail-support indices [11900,11925) and q from 19622 to 19662. -/

def TailChunk001Sub000Block076Part000SupportExplicit : Finset ℕ :=
  ([19622] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block076Part000 : ℚ :=
  (2406393025 : ℚ) / 9263239220598642

def SurrogateDiagonalTailChunk001Sub000Block076Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19622
    = surrogateDiagTailX0RatChunk001Sub000Block076Part000

theorem surrogateDiagonalTailChunk001Sub000Block076Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block076Part000CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block076Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block076Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block076Part000CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block076Part000SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block076Part000] using hcert

def TailChunk001Sub000Block076Part001SupportExplicit : Finset ℕ :=
  ([19623] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block076Part001 : ℚ :=
  (52577382737 : ℚ) / 1260488927376000000

def SurrogateDiagonalTailChunk001Sub000Block076Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19623
    = surrogateDiagTailX0RatChunk001Sub000Block076Part001

theorem surrogateDiagonalTailChunk001Sub000Block076Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block076Part001CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block076Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block076Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block076Part001CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block076Part001SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block076Part001] using hcert

def TailChunk001Sub000Block076Part002SupportExplicit : Finset ℕ :=
  ([19626] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block076Part002 : ℚ :=
  (33426907507 : ℚ) / 45744391212832800

def SurrogateDiagonalTailChunk001Sub000Block076Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19626
    = surrogateDiagTailX0RatChunk001Sub000Block076Part002

theorem surrogateDiagonalTailChunk001Sub000Block076Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block076Part002CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block076Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block076Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block076Part002CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block076Part002SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block076Part002] using hcert

def TailChunk001Sub000Block076Part003SupportExplicit : Finset ℕ :=
  ([19627] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block076Part003 : ℚ :=
  (30190999525 : ℚ) / 33082106774331359232

def SurrogateDiagonalTailChunk001Sub000Block076Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19627
    = surrogateDiagTailX0RatChunk001Sub000Block076Part003

theorem surrogateDiagonalTailChunk001Sub000Block076Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block076Part003CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block076Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block076Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block076Part003CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block076Part003SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block076Part003] using hcert

def TailChunk001Sub000Block076Part004SupportExplicit : Finset ℕ :=
  ([19630] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block076Part004 : ℚ :=
  (2030946029 : ℚ) / 3583897436160000

def SurrogateDiagonalTailChunk001Sub000Block076Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19630
    = surrogateDiagTailX0RatChunk001Sub000Block076Part004

theorem surrogateDiagonalTailChunk001Sub000Block076Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block076Part004CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block076Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block076Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block076Part004CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block076Part004SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block076Part004] using hcert

def TailChunk001Sub000Block076Part005SupportExplicit : Finset ℕ :=
  ([19631] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block076Part005 : ℚ :=
  (27756925225 : ℚ) / 86233103306327020032

def SurrogateDiagonalTailChunk001Sub000Block076Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19631
    = surrogateDiagTailX0RatChunk001Sub000Block076Part005

theorem surrogateDiagonalTailChunk001Sub000Block076Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block076Part005CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block076Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block076Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block076Part005CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block076Part005SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block076Part005] using hcert

def TailChunk001Sub000Block076Part006SupportExplicit : Finset ℕ :=
  ([19633] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block076Part006 : ℚ :=
  (208418917825 : ℚ) / 320956198914166652928

def SurrogateDiagonalTailChunk001Sub000Block076Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19633
    = surrogateDiagTailX0RatChunk001Sub000Block076Part006

theorem surrogateDiagonalTailChunk001Sub000Block076Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block076Part006CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block076Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block076Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block076Part006CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block076Part006SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block076Part006] using hcert

def TailChunk001Sub000Block076Part007SupportExplicit : Finset ℕ :=
  ([19634] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block076Part007 : ℚ :=
  (1505835765625 : ℚ) / 5803701486988718592

def SurrogateDiagonalTailChunk001Sub000Block076Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19634
    = surrogateDiagTailX0RatChunk001Sub000Block076Part007

theorem surrogateDiagonalTailChunk001Sub000Block076Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block076Part007CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block076Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block076Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block076Part007CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block076Part007SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block076Part007] using hcert

def TailChunk001Sub000Block076Part008SupportExplicit : Finset ℕ :=
  ([19635] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block076Part008 : ℚ :=
  (77714341633 : ℚ) / 347961929446195200

def SurrogateDiagonalTailChunk001Sub000Block076Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19635
    = surrogateDiagTailX0RatChunk001Sub000Block076Part008

theorem surrogateDiagonalTailChunk001Sub000Block076Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block076Part008CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block076Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block076Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block076Part008CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block076Part008SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block076Part008] using hcert

def TailChunk001Sub000Block076Part009SupportExplicit : Finset ℕ :=
  ([19637] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block076Part009 : ℚ :=
  (107329832575 : ℚ) / 346653844260719689728

def SurrogateDiagonalTailChunk001Sub000Block076Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19637
    = surrogateDiagTailX0RatChunk001Sub000Block076Part009

theorem surrogateDiagonalTailChunk001Sub000Block076Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block076Part009CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block076Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block076Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block076Part009CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block076Part009SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block076Part009] using hcert

def TailChunk001Sub000Block076Part010SupportExplicit : Finset ℕ :=
  ([19639] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block076Part010 : ℚ :=
  (3385475123 : ℚ) / 6683568543187353600

def SurrogateDiagonalTailChunk001Sub000Block076Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19639
    = surrogateDiagTailX0RatChunk001Sub000Block076Part010

theorem surrogateDiagonalTailChunk001Sub000Block076Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block076Part010CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block076Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block076Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block076Part010CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block076Part010SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block076Part010] using hcert

def TailChunk001Sub000Block076Part011SupportExplicit : Finset ℕ :=
  ([19641] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block076Part011 : ℚ :=
  (1339378636925 : ℚ) / 36729993354033973824

def SurrogateDiagonalTailChunk001Sub000Block076Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19641
    = surrogateDiagTailX0RatChunk001Sub000Block076Part011

theorem surrogateDiagonalTailChunk001Sub000Block076Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block076Part011CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block076Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block076Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block076Part011CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block076Part011SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block076Part011] using hcert

def TailChunk001Sub000Block076Part012SupportExplicit : Finset ℕ :=
  ([19642] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block076Part012 : ℚ :=
  (14276934143 : ℚ) / 32794901476761600

def SurrogateDiagonalTailChunk001Sub000Block076Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19642
    = surrogateDiagTailX0RatChunk001Sub000Block076Part012

theorem surrogateDiagonalTailChunk001Sub000Block076Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block076Part012CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block076Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block076Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block076Part012CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block076Part012SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block076Part012] using hcert

def TailChunk001Sub000Block076Part013SupportExplicit : Finset ℕ :=
  ([19643] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block076Part013 : ℚ :=
  (3822905179 : ℚ) / 1797083981983411200

def SurrogateDiagonalTailChunk001Sub000Block076Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19643
    = surrogateDiagTailX0RatChunk001Sub000Block076Part013

theorem surrogateDiagonalTailChunk001Sub000Block076Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block076Part013CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block076Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block076Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block076Part013CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block076Part013SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block076Part013] using hcert

def TailChunk001Sub000Block076Part014SupportExplicit : Finset ℕ :=
  ([19645] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block076Part014 : ℚ :=
  (321858232125 : ℚ) / 50796230581255929856

def SurrogateDiagonalTailChunk001Sub000Block076Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19645
    = surrogateDiagTailX0RatChunk001Sub000Block076Part014

theorem surrogateDiagonalTailChunk001Sub000Block076Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block076Part014CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block076Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block076Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block076Part014CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block076Part014SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block076Part014] using hcert

def TailChunk001Sub000Block076Part015SupportExplicit : Finset ℕ :=
  ([19646] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block076Part015 : ℚ :=
  (62293086247 : ℚ) / 156706475380070400

def SurrogateDiagonalTailChunk001Sub000Block076Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19646
    = surrogateDiagTailX0RatChunk001Sub000Block076Part015

theorem surrogateDiagonalTailChunk001Sub000Block076Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block076Part015CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block076Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block076Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block076Part015CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block076Part015SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block076Part015] using hcert

def TailChunk001Sub000Block076Part016SupportExplicit : Finset ℕ :=
  ([19651] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block076Part016 : ℚ :=
  (77935689425 : ℚ) / 168210613764677320704

def SurrogateDiagonalTailChunk001Sub000Block076Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19651
    = surrogateDiagTailX0RatChunk001Sub000Block076Part016

theorem surrogateDiagonalTailChunk001Sub000Block076Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block076Part016CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block076Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block076Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block076Part016CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block076Part016SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block076Part016] using hcert

def TailChunk001Sub000Block076Part017SupportExplicit : Finset ℕ :=
  ([19653] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block076Part017 : ℚ :=
  (2145625019 : ℚ) / 58911764196840000

def SurrogateDiagonalTailChunk001Sub000Block076Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19653
    = surrogateDiagTailX0RatChunk001Sub000Block076Part017

theorem surrogateDiagonalTailChunk001Sub000Block076Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block076Part017CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block076Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block076Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block076Part017CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block076Part017SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block076Part017] using hcert

def TailChunk001Sub000Block076Part018SupportExplicit : Finset ℕ :=
  ([19654] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block076Part018 : ℚ :=
  (11441353421 : ℚ) / 40391520669596160

def SurrogateDiagonalTailChunk001Sub000Block076Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19654
    = surrogateDiagTailX0RatChunk001Sub000Block076Part018

theorem surrogateDiagonalTailChunk001Sub000Block076Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block076Part018CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block076Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block076Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block076Part018CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block076Part018SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block076Part018] using hcert

def TailChunk001Sub000Block076Part019SupportExplicit : Finset ℕ :=
  ([19655] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block076Part019 : ℚ :=
  (7732455569 : ℚ) / 1221594342385674240

def SurrogateDiagonalTailChunk001Sub000Block076Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19655
    = surrogateDiagTailX0RatChunk001Sub000Block076Part019

theorem surrogateDiagonalTailChunk001Sub000Block076Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block076Part019CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block076Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block076Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block076Part019CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block076Part019SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block076Part019] using hcert

def TailChunk001Sub000Block076Part020SupportExplicit : Finset ℕ :=
  ([19657] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block076Part020 : ℚ :=
  (24038995603 : ℚ) / 10176833481320323200

def SurrogateDiagonalTailChunk001Sub000Block076Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19657
    = surrogateDiagTailX0RatChunk001Sub000Block076Part020

theorem surrogateDiagonalTailChunk001Sub000Block076Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block076Part020CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block076Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block076Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block076Part020CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block076Part020SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block076Part020] using hcert

def TailChunk001Sub000Block076Part021SupportExplicit : Finset ℕ :=
  ([19658] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block076Part021 : ℚ :=
  (1509519390625 : ℚ) / 5832133529275321632

def SurrogateDiagonalTailChunk001Sub000Block076Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19658
    = surrogateDiagTailX0RatChunk001Sub000Block076Part021

theorem surrogateDiagonalTailChunk001Sub000Block076Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block076Part021CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block076Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block076Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block076Part021CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block076Part021SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block076Part021] using hcert

def TailChunk001Sub000Block076Part022SupportExplicit : Finset ℕ :=
  ([19659] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block076Part022 : ℚ :=
  (95845322275 : ℚ) / 2633203145492914176

def SurrogateDiagonalTailChunk001Sub000Block076Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19659
    = surrogateDiagTailX0RatChunk001Sub000Block076Part022

theorem surrogateDiagonalTailChunk001Sub000Block076Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block076Part022CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block076Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block076Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block076Part022CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block076Part022SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block076Part022] using hcert

def TailChunk001Sub000Block076Part023SupportExplicit : Finset ℕ :=
  ([19661] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block076Part023 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block076Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19661
    = surrogateDiagTailX0RatChunk001Sub000Block076Part023

theorem surrogateDiagonalTailChunk001Sub000Block076Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block076Part023CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block076Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block076Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block076Part023CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block076Part023SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block076Part023] using hcert

def TailChunk001Sub000Block076Part024SupportExplicit : Finset ℕ :=
  ([19662] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block076Part024 : ℚ :=
  (1052525056875 : ℚ) / 1289822067151077376

def SurrogateDiagonalTailChunk001Sub000Block076Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19662
    = surrogateDiagTailX0RatChunk001Sub000Block076Part024

theorem surrogateDiagonalTailChunk001Sub000Block076Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block076Part024CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block076Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block076Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block076Part024CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block076Part024SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block076Part024] using hcert

def surrogateDiagonalTailChunk001Sub000Block076HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block076Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block076Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block076Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block076Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block076Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block076Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block076Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block076Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block076Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block076Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block076Head : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block076Part000
    + surrogateDiagTailX0RatChunk001Sub000Block076Part001
    + surrogateDiagTailX0RatChunk001Sub000Block076Part002
    + surrogateDiagTailX0RatChunk001Sub000Block076Part003
    + surrogateDiagTailX0RatChunk001Sub000Block076Part004
    + surrogateDiagTailX0RatChunk001Sub000Block076Part005
    + surrogateDiagTailX0RatChunk001Sub000Block076Part006
    + surrogateDiagTailX0RatChunk001Sub000Block076Part007
    + surrogateDiagTailX0RatChunk001Sub000Block076Part008
    + surrogateDiagTailX0RatChunk001Sub000Block076Part009

def surrogateDiagonalTailChunk001Sub000Block076MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block076Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block076Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block076Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block076Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block076Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block076Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block076Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block076Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block076Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block076Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block076Mid : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block076Part010
    + surrogateDiagTailX0RatChunk001Sub000Block076Part011
    + surrogateDiagTailX0RatChunk001Sub000Block076Part012
    + surrogateDiagTailX0RatChunk001Sub000Block076Part013
    + surrogateDiagTailX0RatChunk001Sub000Block076Part014
    + surrogateDiagTailX0RatChunk001Sub000Block076Part015
    + surrogateDiagTailX0RatChunk001Sub000Block076Part016
    + surrogateDiagTailX0RatChunk001Sub000Block076Part017
    + surrogateDiagTailX0RatChunk001Sub000Block076Part018
    + surrogateDiagTailX0RatChunk001Sub000Block076Part019

def surrogateDiagonalTailChunk001Sub000Block076TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block076Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block076Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block076Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block076Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block076Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block076Tail : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block076Part020
    + surrogateDiagTailX0RatChunk001Sub000Block076Part021
    + surrogateDiagTailX0RatChunk001Sub000Block076Part022
    + surrogateDiagTailX0RatChunk001Sub000Block076Part023
    + surrogateDiagTailX0RatChunk001Sub000Block076Part024

def surrogateDiagonalTailChunk001Sub000Block076Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk001Sub000Block076HeadSum X0
    + surrogateDiagonalTailChunk001Sub000Block076MidSum X0
    + surrogateDiagonalTailChunk001Sub000Block076TailSum X0

def surrogateDiagTailX0RatChunk001Sub000Block076 : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block076Part000
    + surrogateDiagTailX0RatChunk001Sub000Block076Part001
    + surrogateDiagTailX0RatChunk001Sub000Block076Part002
    + surrogateDiagTailX0RatChunk001Sub000Block076Part003
    + surrogateDiagTailX0RatChunk001Sub000Block076Part004
    + surrogateDiagTailX0RatChunk001Sub000Block076Part005
    + surrogateDiagTailX0RatChunk001Sub000Block076Part006
    + surrogateDiagTailX0RatChunk001Sub000Block076Part007
    + surrogateDiagTailX0RatChunk001Sub000Block076Part008
    + surrogateDiagTailX0RatChunk001Sub000Block076Part009
    + surrogateDiagTailX0RatChunk001Sub000Block076Part010
    + surrogateDiagTailX0RatChunk001Sub000Block076Part011
    + surrogateDiagTailX0RatChunk001Sub000Block076Part012
    + surrogateDiagTailX0RatChunk001Sub000Block076Part013
    + surrogateDiagTailX0RatChunk001Sub000Block076Part014
    + surrogateDiagTailX0RatChunk001Sub000Block076Part015
    + surrogateDiagTailX0RatChunk001Sub000Block076Part016
    + surrogateDiagTailX0RatChunk001Sub000Block076Part017
    + surrogateDiagTailX0RatChunk001Sub000Block076Part018
    + surrogateDiagTailX0RatChunk001Sub000Block076Part019
    + surrogateDiagTailX0RatChunk001Sub000Block076Part020
    + surrogateDiagTailX0RatChunk001Sub000Block076Part021
    + surrogateDiagTailX0RatChunk001Sub000Block076Part022
    + surrogateDiagTailX0RatChunk001Sub000Block076Part023
    + surrogateDiagTailX0RatChunk001Sub000Block076Part024

theorem surrogateDiagTailX0RatChunk001Sub000Block076_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk001Sub000Block076Head + surrogateDiagTailX0RatChunk001Sub000Block076Mid + surrogateDiagTailX0RatChunk001Sub000Block076Tail =
      surrogateDiagTailX0RatChunk001Sub000Block076 := by
  unfold surrogateDiagTailX0RatChunk001Sub000Block076Head surrogateDiagTailX0RatChunk001Sub000Block076Mid surrogateDiagTailX0RatChunk001Sub000Block076Tail surrogateDiagTailX0RatChunk001Sub000Block076
  ring

def SurrogateDiagonalTailChunk001Sub000Block076HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block076HeadSum X0 = surrogateDiagTailX0RatChunk001Sub000Block076Head

def SurrogateDiagonalTailChunk001Sub000Block076MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block076MidSum X0 = surrogateDiagTailX0RatChunk001Sub000Block076Mid

def SurrogateDiagonalTailChunk001Sub000Block076TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block076TailSum X0 = surrogateDiagTailX0RatChunk001Sub000Block076Tail

theorem surrogateDiagonalTailChunk001Sub000Block076_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk001Sub000Block076HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk001Sub000Block076MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk001Sub000Block076TailCertificateAt X0) :
    surrogateDiagonalTailChunk001Sub000Block076Sum X0 = surrogateDiagTailX0RatChunk001Sub000Block076 := by
  unfold SurrogateDiagonalTailChunk001Sub000Block076HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk001Sub000Block076MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk001Sub000Block076TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk001Sub000Block076Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk001Sub000Block076_eq_head_add_mid_add_tail

/-- Block 077 covers tail-support indices [11925,11950) and q from 19666 to 19705. -/

def TailChunk001Sub000Block077Part000SupportExplicit : Finset ℕ :=
  ([19666] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block077Part000 : ℚ :=
  (1510748265625 : ℚ) / 5841634050262774272

def SurrogateDiagonalTailChunk001Sub000Block077Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19666
    = surrogateDiagTailX0RatChunk001Sub000Block077Part000

theorem surrogateDiagonalTailChunk001Sub000Block077Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block077Part000CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block077Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block077Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block077Part000CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block077Part000SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block077Part000] using hcert

def TailChunk001Sub000Block077Part001SupportExplicit : Finset ℕ :=
  ([19667] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block077Part001 : ℚ :=
  (1071571507 : ℚ) / 3483817105440268800

def SurrogateDiagonalTailChunk001Sub000Block077Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19667
    = surrogateDiagTailX0RatChunk001Sub000Block077Part001

theorem surrogateDiagonalTailChunk001Sub000Block077Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block077Part001CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block077Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block077Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block077Part001CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block077Part001SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block077Part001] using hcert

def TailChunk001Sub000Block077Part002SupportExplicit : Finset ℕ :=
  ([19669] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block077Part002 : ℚ :=
  (735395647975 : ℚ) / 203780424360869756928

def SurrogateDiagonalTailChunk001Sub000Block077Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19669
    = surrogateDiagTailX0RatChunk001Sub000Block077Part002

theorem surrogateDiagonalTailChunk001Sub000Block077Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block077Part002CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block077Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block077Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block077Part002CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block077Part002SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block077Part002] using hcert

def TailChunk001Sub000Block077Part003SupportExplicit : Finset ℕ :=
  ([19670] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block077Part003 : ℚ :=
  (16527340607 : ℚ) / 25496111834726400

def SurrogateDiagonalTailChunk001Sub000Block077Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19670
    = surrogateDiagTailX0RatChunk001Sub000Block077Part003

theorem surrogateDiagonalTailChunk001Sub000Block077Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block077Part003CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block077Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block077Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block077Part003CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block077Part003SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block077Part003] using hcert

def TailChunk001Sub000Block077Part004SupportExplicit : Finset ℕ :=
  ([19671] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block077Part004 : ℚ :=
  (1327472687375 : ℚ) / 33477318655343207424

def SurrogateDiagonalTailChunk001Sub000Block077Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19671
    = surrogateDiagTailX0RatChunk001Sub000Block077Part004

theorem surrogateDiagonalTailChunk001Sub000Block077Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block077Part004CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block077Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block077Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block077Part004CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block077Part004SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block077Part004] using hcert

def TailChunk001Sub000Block077Part005SupportExplicit : Finset ℕ :=
  ([19673] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block077Part005 : ℚ :=
  (3595969819 : ℚ) / 14109185425166467200

def SurrogateDiagonalTailChunk001Sub000Block077Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19673
    = surrogateDiagTailX0RatChunk001Sub000Block077Part005

theorem surrogateDiagonalTailChunk001Sub000Block077Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block077Part005CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block077Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block077Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block077Part005CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block077Part005SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block077Part005] using hcert

def TailChunk001Sub000Block077Part006SupportExplicit : Finset ℕ :=
  ([19677] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block077Part006 : ℚ :=
  (606174425725 : ℚ) / 39797449289315647488

def SurrogateDiagonalTailChunk001Sub000Block077Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19677
    = surrogateDiagTailX0RatChunk001Sub000Block077Part006

theorem surrogateDiagonalTailChunk001Sub000Block077Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block077Part006CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block077Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block077Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block077Part006CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block077Part006SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block077Part006] using hcert

def TailChunk001Sub000Block077Part007SupportExplicit : Finset ℕ :=
  ([19678] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block077Part007 : ℚ :=
  (1512592515625 : ℚ) / 5855906589395663442

def SurrogateDiagonalTailChunk001Sub000Block077Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19678
    = surrogateDiagTailX0RatChunk001Sub000Block077Part007

theorem surrogateDiagonalTailChunk001Sub000Block077Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block077Part007CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block077Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block077Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block077Part007CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block077Part007SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block077Part007] using hcert

def TailChunk001Sub000Block077Part008SupportExplicit : Finset ℕ :=
  ([19679] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block077Part008 : ℚ :=
  (24092584117 : ℚ) / 10222495029323827200

def SurrogateDiagonalTailChunk001Sub000Block077Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19679
    = surrogateDiagTailX0RatChunk001Sub000Block077Part008

theorem surrogateDiagonalTailChunk001Sub000Block077Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block077Part008CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block077Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block077Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block077Part008CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block077Part008SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block077Part008] using hcert

def TailChunk001Sub000Block077Part009SupportExplicit : Finset ℕ :=
  ([19681] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block077Part009 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block077Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19681
    = surrogateDiagTailX0RatChunk001Sub000Block077Part009

theorem surrogateDiagonalTailChunk001Sub000Block077Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block077Part009CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block077Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block077Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block077Part009CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block077Part009SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block077Part009] using hcert

def TailChunk001Sub000Block077Part010SupportExplicit : Finset ℕ :=
  ([19682] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block077Part010 : ℚ :=
  (5362709085775 : ℚ) / 16937098961948540928

def SurrogateDiagonalTailChunk001Sub000Block077Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19682
    = surrogateDiagTailX0RatChunk001Sub000Block077Part010

theorem surrogateDiagonalTailChunk001Sub000Block077Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block077Part010CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block077Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block077Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block077Part010CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block077Part010SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block077Part010] using hcert

def TailChunk001Sub000Block077Part011SupportExplicit : Finset ℕ :=
  ([19685] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block077Part011 : ℚ :=
  (43513724827 : ℚ) / 5227499679613747200

def SurrogateDiagonalTailChunk001Sub000Block077Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19685
    = surrogateDiagTailX0RatChunk001Sub000Block077Part011

theorem surrogateDiagonalTailChunk001Sub000Block077Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block077Part011CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block077Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block077Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block077Part011CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block077Part011SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block077Part011] using hcert

def TailChunk001Sub000Block077Part012SupportExplicit : Finset ℕ :=
  ([19686] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block077Part012 : ℚ :=
  (413685114125 : ℚ) / 593855026254839808

def SurrogateDiagonalTailChunk001Sub000Block077Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19686
    = surrogateDiagTailX0RatChunk001Sub000Block077Part012

theorem surrogateDiagonalTailChunk001Sub000Block077Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block077Part012CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block077Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block077Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block077Part012CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block077Part012SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block077Part012] using hcert

def TailChunk001Sub000Block077Part013SupportExplicit : Finset ℕ :=
  ([19687] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block077Part013 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block077Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19687
    = surrogateDiagTailX0RatChunk001Sub000Block077Part013

theorem surrogateDiagonalTailChunk001Sub000Block077Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block077Part013CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block077Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block077Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block077Part013CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block077Part013SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block077Part013] using hcert

def TailChunk001Sub000Block077Part014SupportExplicit : Finset ℕ :=
  ([19689] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block077Part014 : ℚ :=
  (125025 : ℚ) / 14833201322434688

def SurrogateDiagonalTailChunk001Sub000Block077Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19689
    = surrogateDiagTailX0RatChunk001Sub000Block077Part014

theorem surrogateDiagonalTailChunk001Sub000Block077Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block077Part014CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block077Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block077Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block077Part014CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block077Part014SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block077Part014] using hcert

def TailChunk001Sub000Block077Part015SupportExplicit : Finset ℕ :=
  ([19690] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block077Part015 : ℚ :=
  (7550925821 : ℚ) / 12852180878991360

def SurrogateDiagonalTailChunk001Sub000Block077Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19690
    = surrogateDiagTailX0RatChunk001Sub000Block077Part015

theorem surrogateDiagonalTailChunk001Sub000Block077Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block077Part015CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block077Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block077Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block077Part015CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block077Part015SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block077Part015] using hcert

def TailChunk001Sub000Block077Part016SupportExplicit : Finset ℕ :=
  ([19691] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block077Part016 : ℚ :=
  (281063689525 : ℚ) / 42294990000390930432

def SurrogateDiagonalTailChunk001Sub000Block077Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19691
    = surrogateDiagTailX0RatChunk001Sub000Block077Part016

theorem surrogateDiagonalTailChunk001Sub000Block077Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block077Part016CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block077Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block077Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block077Part016CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block077Part016SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block077Part016] using hcert

def TailChunk001Sub000Block077Part017SupportExplicit : Finset ℕ :=
  ([19693] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block077Part017 : ℚ :=
  (145082134825 : ℚ) / 341793117017133184128

def SurrogateDiagonalTailChunk001Sub000Block077Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19693
    = surrogateDiagTailX0RatChunk001Sub000Block077Part017

theorem surrogateDiagonalTailChunk001Sub000Block077Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block077Part017CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block077Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block077Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block077Part017CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block077Part017SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block077Part017] using hcert

def TailChunk001Sub000Block077Part018SupportExplicit : Finset ℕ :=
  ([19694] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block077Part018 : ℚ :=
  (645937218175 : ℚ) / 2336258524509407232

def SurrogateDiagonalTailChunk001Sub000Block077Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19694
    = surrogateDiagTailX0RatChunk001Sub000Block077Part018

theorem surrogateDiagonalTailChunk001Sub000Block077Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block077Part018CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block077Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block077Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block077Part018CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block077Part018SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block077Part018] using hcert

def TailChunk001Sub000Block077Part019SupportExplicit : Finset ℕ :=
  ([19695] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block077Part019 : ℚ :=
  (4651733677 : ℚ) / 84951642931200000

def SurrogateDiagonalTailChunk001Sub000Block077Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19695
    = surrogateDiagTailX0RatChunk001Sub000Block077Part019

theorem surrogateDiagonalTailChunk001Sub000Block077Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block077Part019CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block077Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block077Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block077Part019CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block077Part019SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block077Part019] using hcert

def TailChunk001Sub000Block077Part020SupportExplicit : Finset ℕ :=
  ([19697] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block077Part020 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block077Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19697
    = surrogateDiagTailX0RatChunk001Sub000Block077Part020

theorem surrogateDiagonalTailChunk001Sub000Block077Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block077Part020CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block077Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block077Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block077Part020CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block077Part020SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block077Part020] using hcert

def TailChunk001Sub000Block077Part021SupportExplicit : Finset ℕ :=
  ([19699] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block077Part021 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block077Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19699
    = surrogateDiagTailX0RatChunk001Sub000Block077Part021

theorem surrogateDiagonalTailChunk001Sub000Block077Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block077Part021CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block077Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block077Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block077Part021CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block077Part021SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block077Part021] using hcert

def TailChunk001Sub000Block077Part022SupportExplicit : Finset ℕ :=
  ([19702] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block077Part022 : ℚ :=
  (97042201 : ℚ) / 376609927174050

def SurrogateDiagonalTailChunk001Sub000Block077Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19702
    = surrogateDiagTailX0RatChunk001Sub000Block077Part022

theorem surrogateDiagonalTailChunk001Sub000Block077Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block077Part022CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block077Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block077Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block077Part022CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block077Part022SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block077Part022] using hcert

def TailChunk001Sub000Block077Part023SupportExplicit : Finset ℕ :=
  ([19703] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block077Part023 : ℚ :=
  (5048827883 : ℚ) / 1783576733669130240

def SurrogateDiagonalTailChunk001Sub000Block077Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19703
    = surrogateDiagTailX0RatChunk001Sub000Block077Part023

theorem surrogateDiagonalTailChunk001Sub000Block077Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block077Part023CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block077Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block077Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block077Part023CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block077Part023SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block077Part023] using hcert

def TailChunk001Sub000Block077Part024SupportExplicit : Finset ℕ :=
  ([19705] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block077Part024 : ℚ :=
  (1069429112525 : ℚ) / 41379676618853597184

def SurrogateDiagonalTailChunk001Sub000Block077Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19705
    = surrogateDiagTailX0RatChunk001Sub000Block077Part024

theorem surrogateDiagonalTailChunk001Sub000Block077Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block077Part024CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block077Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block077Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block077Part024CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block077Part024SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block077Part024] using hcert

def surrogateDiagonalTailChunk001Sub000Block077HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block077Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block077Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block077Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block077Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block077Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block077Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block077Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block077Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block077Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block077Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block077Head : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block077Part000
    + surrogateDiagTailX0RatChunk001Sub000Block077Part001
    + surrogateDiagTailX0RatChunk001Sub000Block077Part002
    + surrogateDiagTailX0RatChunk001Sub000Block077Part003
    + surrogateDiagTailX0RatChunk001Sub000Block077Part004
    + surrogateDiagTailX0RatChunk001Sub000Block077Part005
    + surrogateDiagTailX0RatChunk001Sub000Block077Part006
    + surrogateDiagTailX0RatChunk001Sub000Block077Part007
    + surrogateDiagTailX0RatChunk001Sub000Block077Part008
    + surrogateDiagTailX0RatChunk001Sub000Block077Part009

def surrogateDiagonalTailChunk001Sub000Block077MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block077Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block077Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block077Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block077Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block077Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block077Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block077Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block077Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block077Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block077Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block077Mid : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block077Part010
    + surrogateDiagTailX0RatChunk001Sub000Block077Part011
    + surrogateDiagTailX0RatChunk001Sub000Block077Part012
    + surrogateDiagTailX0RatChunk001Sub000Block077Part013
    + surrogateDiagTailX0RatChunk001Sub000Block077Part014
    + surrogateDiagTailX0RatChunk001Sub000Block077Part015
    + surrogateDiagTailX0RatChunk001Sub000Block077Part016
    + surrogateDiagTailX0RatChunk001Sub000Block077Part017
    + surrogateDiagTailX0RatChunk001Sub000Block077Part018
    + surrogateDiagTailX0RatChunk001Sub000Block077Part019

def surrogateDiagonalTailChunk001Sub000Block077TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block077Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block077Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block077Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block077Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block077Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block077Tail : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block077Part020
    + surrogateDiagTailX0RatChunk001Sub000Block077Part021
    + surrogateDiagTailX0RatChunk001Sub000Block077Part022
    + surrogateDiagTailX0RatChunk001Sub000Block077Part023
    + surrogateDiagTailX0RatChunk001Sub000Block077Part024

def surrogateDiagonalTailChunk001Sub000Block077Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk001Sub000Block077HeadSum X0
    + surrogateDiagonalTailChunk001Sub000Block077MidSum X0
    + surrogateDiagonalTailChunk001Sub000Block077TailSum X0

def surrogateDiagTailX0RatChunk001Sub000Block077 : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block077Part000
    + surrogateDiagTailX0RatChunk001Sub000Block077Part001
    + surrogateDiagTailX0RatChunk001Sub000Block077Part002
    + surrogateDiagTailX0RatChunk001Sub000Block077Part003
    + surrogateDiagTailX0RatChunk001Sub000Block077Part004
    + surrogateDiagTailX0RatChunk001Sub000Block077Part005
    + surrogateDiagTailX0RatChunk001Sub000Block077Part006
    + surrogateDiagTailX0RatChunk001Sub000Block077Part007
    + surrogateDiagTailX0RatChunk001Sub000Block077Part008
    + surrogateDiagTailX0RatChunk001Sub000Block077Part009
    + surrogateDiagTailX0RatChunk001Sub000Block077Part010
    + surrogateDiagTailX0RatChunk001Sub000Block077Part011
    + surrogateDiagTailX0RatChunk001Sub000Block077Part012
    + surrogateDiagTailX0RatChunk001Sub000Block077Part013
    + surrogateDiagTailX0RatChunk001Sub000Block077Part014
    + surrogateDiagTailX0RatChunk001Sub000Block077Part015
    + surrogateDiagTailX0RatChunk001Sub000Block077Part016
    + surrogateDiagTailX0RatChunk001Sub000Block077Part017
    + surrogateDiagTailX0RatChunk001Sub000Block077Part018
    + surrogateDiagTailX0RatChunk001Sub000Block077Part019
    + surrogateDiagTailX0RatChunk001Sub000Block077Part020
    + surrogateDiagTailX0RatChunk001Sub000Block077Part021
    + surrogateDiagTailX0RatChunk001Sub000Block077Part022
    + surrogateDiagTailX0RatChunk001Sub000Block077Part023
    + surrogateDiagTailX0RatChunk001Sub000Block077Part024

theorem surrogateDiagTailX0RatChunk001Sub000Block077_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk001Sub000Block077Head + surrogateDiagTailX0RatChunk001Sub000Block077Mid + surrogateDiagTailX0RatChunk001Sub000Block077Tail =
      surrogateDiagTailX0RatChunk001Sub000Block077 := by
  unfold surrogateDiagTailX0RatChunk001Sub000Block077Head surrogateDiagTailX0RatChunk001Sub000Block077Mid surrogateDiagTailX0RatChunk001Sub000Block077Tail surrogateDiagTailX0RatChunk001Sub000Block077
  ring

def SurrogateDiagonalTailChunk001Sub000Block077HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block077HeadSum X0 = surrogateDiagTailX0RatChunk001Sub000Block077Head

def SurrogateDiagonalTailChunk001Sub000Block077MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block077MidSum X0 = surrogateDiagTailX0RatChunk001Sub000Block077Mid

def SurrogateDiagonalTailChunk001Sub000Block077TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block077TailSum X0 = surrogateDiagTailX0RatChunk001Sub000Block077Tail

theorem surrogateDiagonalTailChunk001Sub000Block077_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk001Sub000Block077HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk001Sub000Block077MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk001Sub000Block077TailCertificateAt X0) :
    surrogateDiagonalTailChunk001Sub000Block077Sum X0 = surrogateDiagTailX0RatChunk001Sub000Block077 := by
  unfold SurrogateDiagonalTailChunk001Sub000Block077HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk001Sub000Block077MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk001Sub000Block077TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk001Sub000Block077Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk001Sub000Block077_eq_head_add_mid_add_tail

/-- Block 078 covers tail-support indices [11950,11975) and q from 19706 to 19745. -/

def TailChunk001Sub000Block078Part000SupportExplicit : Finset ℕ :=
  ([19706] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block078Part000 : ℚ :=
  (1465174616875 : ℚ) / 5371693121431686432

def SurrogateDiagonalTailChunk001Sub000Block078Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19706
    = surrogateDiagTailX0RatChunk001Sub000Block078Part000

theorem surrogateDiagonalTailChunk001Sub000Block078Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block078Part000CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block078Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block078Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block078Part000CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block078Part000SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block078Part000] using hcert

def TailChunk001Sub000Block078Part001SupportExplicit : Finset ℕ :=
  ([19707] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block078Part001 : ℚ :=
  (125025 : ℚ) / 14887527044907008

def SurrogateDiagonalTailChunk001Sub000Block078Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19707
    = surrogateDiagTailX0RatChunk001Sub000Block078Part001

theorem surrogateDiagonalTailChunk001Sub000Block078Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block078Part001CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block078Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block078Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block078Part001CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block078Part001SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block078Part001] using hcert

def TailChunk001Sub000Block078Part002SupportExplicit : Finset ℕ :=
  ([19709] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block078Part002 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block078Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19709
    = surrogateDiagTailX0RatChunk001Sub000Block078Part002

theorem surrogateDiagonalTailChunk001Sub000Block078Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block078Part002CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block078Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block078Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block078Part002CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block078Part002SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block078Part002] using hcert

def TailChunk001Sub000Block078Part003SupportExplicit : Finset ℕ :=
  ([19711] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block078Part003 : ℚ :=
  (281365984975 : ℚ) / 314494200304213721088

def SurrogateDiagonalTailChunk001Sub000Block078Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19711
    = surrogateDiagTailX0RatChunk001Sub000Block078Part003

theorem surrogateDiagonalTailChunk001Sub000Block078Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block078Part003CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block078Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block078Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block078Part003CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block078Part003SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block078Part003] using hcert

def TailChunk001Sub000Block078Part004SupportExplicit : Finset ℕ :=
  ([19713] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block078Part004 : ℚ :=
  (1667 : ℚ) / 198742249814400

def SurrogateDiagonalTailChunk001Sub000Block078Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19713
    = surrogateDiagTailX0RatChunk001Sub000Block078Part004

theorem surrogateDiagonalTailChunk001Sub000Block078Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block078Part004CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block078Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block078Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block078Part004CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block078Part004SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block078Part004] using hcert

def TailChunk001Sub000Block078Part005SupportExplicit : Finset ℕ :=
  ([19714] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block078Part005 : ℚ :=
  (1518132015625 : ℚ) / 5898881159462387712

def SurrogateDiagonalTailChunk001Sub000Block078Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19714
    = surrogateDiagTailX0RatChunk001Sub000Block078Part005

theorem surrogateDiagonalTailChunk001Sub000Block078Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block078Part005CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block078Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block078Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block078Part005CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block078Part005SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block078Part005] using hcert

def TailChunk001Sub000Block078Part006SupportExplicit : Finset ℕ :=
  ([19715] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block078Part006 : ℚ :=
  (647760652675 : ℚ) / 51524293950122858496

def SurrogateDiagonalTailChunk001Sub000Block078Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19715
    = surrogateDiagTailX0RatChunk001Sub000Block078Part006

theorem surrogateDiagonalTailChunk001Sub000Block078Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block078Part006CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block078Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block078Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block078Part006CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block078Part006SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block078Part006] using hcert

def TailChunk001Sub000Block078Part007SupportExplicit : Finset ℕ :=
  ([19717] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block078Part007 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block078Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19717
    = surrogateDiagTailX0RatChunk001Sub000Block078Part007

theorem surrogateDiagonalTailChunk001Sub000Block078Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block078Part007CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block078Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block078Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block078Part007CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block078Part007SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block078Part007] using hcert

def TailChunk001Sub000Block078Part008SupportExplicit : Finset ℕ :=
  ([19718] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block078Part008 : ℚ :=
  (1518748140625 : ℚ) / 5903670669951193362

def SurrogateDiagonalTailChunk001Sub000Block078Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19718
    = surrogateDiagTailX0RatChunk001Sub000Block078Part008

theorem surrogateDiagonalTailChunk001Sub000Block078Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block078Part008CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block078Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block078Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block078Part008CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block078Part008SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block078Part008] using hcert

def TailChunk001Sub000Block078Part009SupportExplicit : Finset ℕ :=
  ([19721] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block078Part009 : ℚ :=
  (13188114047 : ℚ) / 4458941834172825600

def SurrogateDiagonalTailChunk001Sub000Block078Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19721
    = surrogateDiagTailX0RatChunk001Sub000Block078Part009

theorem surrogateDiagonalTailChunk001Sub000Block078Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block078Part009CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block078Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block078Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block078Part009CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block078Part009SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block078Part009] using hcert

def TailChunk001Sub000Block078Part010SupportExplicit : Finset ℕ :=
  ([19722] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block078Part010 : ℚ :=
  (1254585605825 : ℚ) / 1837894820796186624

def SurrogateDiagonalTailChunk001Sub000Block078Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19722
    = surrogateDiagTailX0RatChunk001Sub000Block078Part010

theorem surrogateDiagonalTailChunk001Sub000Block078Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block078Part010CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block078Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block078Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block078Part010CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block078Part010SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block078Part010] using hcert

def TailChunk001Sub000Block078Part011SupportExplicit : Finset ℕ :=
  ([19726] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block078Part011 : ℚ :=
  (268603953575 : ℚ) / 707570917919686656

def SurrogateDiagonalTailChunk001Sub000Block078Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19726
    = surrogateDiagTailX0RatChunk001Sub000Block078Part011

theorem surrogateDiagonalTailChunk001Sub000Block078Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block078Part011CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block078Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block078Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block078Part011CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block078Part011SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block078Part011] using hcert

def TailChunk001Sub000Block078Part012SupportExplicit : Finset ℕ :=
  ([19727] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block078Part012 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block078Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19727
    = surrogateDiagTailX0RatChunk001Sub000Block078Part012

theorem surrogateDiagonalTailChunk001Sub000Block078Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block078Part012CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block078Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block078Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block078Part012CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block078Part012SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block078Part012] using hcert

def TailChunk001Sub000Block078Part013SupportExplicit : Finset ℕ :=
  ([19729] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block078Part013 : ℚ :=
  (721898711 : ℚ) / 2856945056055459840

def SurrogateDiagonalTailChunk001Sub000Block078Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19729
    = surrogateDiagTailX0RatChunk001Sub000Block078Part013

theorem surrogateDiagonalTailChunk001Sub000Block078Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block078Part013CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block078Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block078Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block078Part013CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block078Part013SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block078Part013] using hcert

def TailChunk001Sub000Block078Part014SupportExplicit : Finset ℕ :=
  ([19730] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block078Part014 : ℚ :=
  (4133472213775 : ℚ) / 9680425937187667968

def SurrogateDiagonalTailChunk001Sub000Block078Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19730
    = surrogateDiagTailX0RatChunk001Sub000Block078Part014

theorem surrogateDiagonalTailChunk001Sub000Block078Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block078Part014CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block078Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block078Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block078Part014CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block078Part014SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block078Part014] using hcert

def TailChunk001Sub000Block078Part015SupportExplicit : Finset ℕ :=
  ([19731] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block078Part015 : ℚ :=
  (41675 : ℚ) / 4986731100635136

def SurrogateDiagonalTailChunk001Sub000Block078Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19731
    = surrogateDiagTailX0RatChunk001Sub000Block078Part015

theorem surrogateDiagonalTailChunk001Sub000Block078Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block078Part015CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block078Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block078Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block078Part015CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block078Part015SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block078Part015] using hcert

def TailChunk001Sub000Block078Part016SupportExplicit : Finset ℕ :=
  ([19733] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block078Part016 : ℚ :=
  (497158400075 : ℚ) / 102179981530993333824

def SurrogateDiagonalTailChunk001Sub000Block078Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19733
    = surrogateDiagTailX0RatChunk001Sub000Block078Part016

theorem surrogateDiagonalTailChunk001Sub000Block078Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block078Part016CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block078Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block078Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block078Part016CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block078Part016SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block078Part016] using hcert

def TailChunk001Sub000Block078Part017SupportExplicit : Finset ℕ :=
  ([19734] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block078Part017 : ℚ :=
  (13698184789 : ℚ) / 12956010459955200

def SurrogateDiagonalTailChunk001Sub000Block078Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19734
    = surrogateDiagTailX0RatChunk001Sub000Block078Part017

theorem surrogateDiagonalTailChunk001Sub000Block078Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block078Part017CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block078Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block078Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block078Part017CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block078Part017SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block078Part017] using hcert

def TailChunk001Sub000Block078Part018SupportExplicit : Finset ℕ :=
  ([19735] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block078Part018 : ℚ :=
  (324810981375 : ℚ) / 51733742029668653056

def SurrogateDiagonalTailChunk001Sub000Block078Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19735
    = surrogateDiagTailX0RatChunk001Sub000Block078Part018

theorem surrogateDiagonalTailChunk001Sub000Block078Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block078Part018CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block078Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block078Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block078Part018CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block078Part018SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block078Part018] using hcert

def TailChunk001Sub000Block078Part019SupportExplicit : Finset ℕ :=
  ([19738] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block078Part019 : ℚ :=
  (13370069 : ℚ) / 49373825190480

def SurrogateDiagonalTailChunk001Sub000Block078Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19738
    = surrogateDiagTailX0RatChunk001Sub000Block078Part019

theorem surrogateDiagonalTailChunk001Sub000Block078Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block078Part019CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block078Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block078Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block078Part019CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block078Part019SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block078Part019] using hcert

def TailChunk001Sub000Block078Part020SupportExplicit : Finset ℕ :=
  ([19739] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block078Part020 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block078Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19739
    = surrogateDiagTailX0RatChunk001Sub000Block078Part020

theorem surrogateDiagonalTailChunk001Sub000Block078Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block078Part020CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block078Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block078Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block078Part020CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block078Part020SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block078Part020] using hcert

def TailChunk001Sub000Block078Part021SupportExplicit : Finset ℕ :=
  ([19741] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block078Part021 : ℚ :=
  (171027223025 : ℚ) / 152361871187887301184

def SurrogateDiagonalTailChunk001Sub000Block078Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19741
    = surrogateDiagTailX0RatChunk001Sub000Block078Part021

theorem surrogateDiagonalTailChunk001Sub000Block078Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block078Part021CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block078Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block078Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block078Part021CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block078Part021SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block078Part021] using hcert

def TailChunk001Sub000Block078Part022SupportExplicit : Finset ℕ :=
  ([19742] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block078Part022 : ℚ :=
  (2435916025 : ℚ) / 9491950416091122

def SurrogateDiagonalTailChunk001Sub000Block078Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19742
    = surrogateDiagTailX0RatChunk001Sub000Block078Part022

theorem surrogateDiagonalTailChunk001Sub000Block078Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block078Part022CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block078Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block078Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block078Part022CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block078Part022SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block078Part022] using hcert

def TailChunk001Sub000Block078Part023SupportExplicit : Finset ℕ :=
  ([19743] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block078Part023 : ℚ :=
  (386664289 : ℚ) / 10714018106346240

def SurrogateDiagonalTailChunk001Sub000Block078Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19743
    = surrogateDiagTailX0RatChunk001Sub000Block078Part023

theorem surrogateDiagonalTailChunk001Sub000Block078Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block078Part023CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block078Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block078Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block078Part023CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block078Part023SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block078Part023] using hcert

def TailChunk001Sub000Block078Part024SupportExplicit : Finset ℕ :=
  ([19745] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block078Part024 : ℚ :=
  (51125837767 : ℚ) / 4205899801133875200

def SurrogateDiagonalTailChunk001Sub000Block078Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19745
    = surrogateDiagTailX0RatChunk001Sub000Block078Part024

theorem surrogateDiagonalTailChunk001Sub000Block078Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block078Part024CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block078Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block078Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block078Part024CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block078Part024SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block078Part024] using hcert

def surrogateDiagonalTailChunk001Sub000Block078HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block078Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block078Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block078Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block078Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block078Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block078Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block078Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block078Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block078Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block078Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block078Head : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block078Part000
    + surrogateDiagTailX0RatChunk001Sub000Block078Part001
    + surrogateDiagTailX0RatChunk001Sub000Block078Part002
    + surrogateDiagTailX0RatChunk001Sub000Block078Part003
    + surrogateDiagTailX0RatChunk001Sub000Block078Part004
    + surrogateDiagTailX0RatChunk001Sub000Block078Part005
    + surrogateDiagTailX0RatChunk001Sub000Block078Part006
    + surrogateDiagTailX0RatChunk001Sub000Block078Part007
    + surrogateDiagTailX0RatChunk001Sub000Block078Part008
    + surrogateDiagTailX0RatChunk001Sub000Block078Part009

def surrogateDiagonalTailChunk001Sub000Block078MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block078Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block078Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block078Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block078Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block078Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block078Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block078Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block078Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block078Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block078Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block078Mid : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block078Part010
    + surrogateDiagTailX0RatChunk001Sub000Block078Part011
    + surrogateDiagTailX0RatChunk001Sub000Block078Part012
    + surrogateDiagTailX0RatChunk001Sub000Block078Part013
    + surrogateDiagTailX0RatChunk001Sub000Block078Part014
    + surrogateDiagTailX0RatChunk001Sub000Block078Part015
    + surrogateDiagTailX0RatChunk001Sub000Block078Part016
    + surrogateDiagTailX0RatChunk001Sub000Block078Part017
    + surrogateDiagTailX0RatChunk001Sub000Block078Part018
    + surrogateDiagTailX0RatChunk001Sub000Block078Part019

def surrogateDiagonalTailChunk001Sub000Block078TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block078Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block078Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block078Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block078Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block078Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block078Tail : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block078Part020
    + surrogateDiagTailX0RatChunk001Sub000Block078Part021
    + surrogateDiagTailX0RatChunk001Sub000Block078Part022
    + surrogateDiagTailX0RatChunk001Sub000Block078Part023
    + surrogateDiagTailX0RatChunk001Sub000Block078Part024

def surrogateDiagonalTailChunk001Sub000Block078Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk001Sub000Block078HeadSum X0
    + surrogateDiagonalTailChunk001Sub000Block078MidSum X0
    + surrogateDiagonalTailChunk001Sub000Block078TailSum X0

def surrogateDiagTailX0RatChunk001Sub000Block078 : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block078Part000
    + surrogateDiagTailX0RatChunk001Sub000Block078Part001
    + surrogateDiagTailX0RatChunk001Sub000Block078Part002
    + surrogateDiagTailX0RatChunk001Sub000Block078Part003
    + surrogateDiagTailX0RatChunk001Sub000Block078Part004
    + surrogateDiagTailX0RatChunk001Sub000Block078Part005
    + surrogateDiagTailX0RatChunk001Sub000Block078Part006
    + surrogateDiagTailX0RatChunk001Sub000Block078Part007
    + surrogateDiagTailX0RatChunk001Sub000Block078Part008
    + surrogateDiagTailX0RatChunk001Sub000Block078Part009
    + surrogateDiagTailX0RatChunk001Sub000Block078Part010
    + surrogateDiagTailX0RatChunk001Sub000Block078Part011
    + surrogateDiagTailX0RatChunk001Sub000Block078Part012
    + surrogateDiagTailX0RatChunk001Sub000Block078Part013
    + surrogateDiagTailX0RatChunk001Sub000Block078Part014
    + surrogateDiagTailX0RatChunk001Sub000Block078Part015
    + surrogateDiagTailX0RatChunk001Sub000Block078Part016
    + surrogateDiagTailX0RatChunk001Sub000Block078Part017
    + surrogateDiagTailX0RatChunk001Sub000Block078Part018
    + surrogateDiagTailX0RatChunk001Sub000Block078Part019
    + surrogateDiagTailX0RatChunk001Sub000Block078Part020
    + surrogateDiagTailX0RatChunk001Sub000Block078Part021
    + surrogateDiagTailX0RatChunk001Sub000Block078Part022
    + surrogateDiagTailX0RatChunk001Sub000Block078Part023
    + surrogateDiagTailX0RatChunk001Sub000Block078Part024

theorem surrogateDiagTailX0RatChunk001Sub000Block078_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk001Sub000Block078Head + surrogateDiagTailX0RatChunk001Sub000Block078Mid + surrogateDiagTailX0RatChunk001Sub000Block078Tail =
      surrogateDiagTailX0RatChunk001Sub000Block078 := by
  unfold surrogateDiagTailX0RatChunk001Sub000Block078Head surrogateDiagTailX0RatChunk001Sub000Block078Mid surrogateDiagTailX0RatChunk001Sub000Block078Tail surrogateDiagTailX0RatChunk001Sub000Block078
  ring

def SurrogateDiagonalTailChunk001Sub000Block078HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block078HeadSum X0 = surrogateDiagTailX0RatChunk001Sub000Block078Head

def SurrogateDiagonalTailChunk001Sub000Block078MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block078MidSum X0 = surrogateDiagTailX0RatChunk001Sub000Block078Mid

def SurrogateDiagonalTailChunk001Sub000Block078TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block078TailSum X0 = surrogateDiagTailX0RatChunk001Sub000Block078Tail

theorem surrogateDiagonalTailChunk001Sub000Block078_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk001Sub000Block078HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk001Sub000Block078MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk001Sub000Block078TailCertificateAt X0) :
    surrogateDiagonalTailChunk001Sub000Block078Sum X0 = surrogateDiagTailX0RatChunk001Sub000Block078 := by
  unfold SurrogateDiagonalTailChunk001Sub000Block078HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk001Sub000Block078MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk001Sub000Block078TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk001Sub000Block078Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk001Sub000Block078_eq_head_add_mid_add_tail

/-- Block 079 covers tail-support indices [11975,12000) and q from 19749 to 19787. -/

def TailChunk001Sub000Block079Part000SupportExplicit : Finset ℕ :=
  ([19749] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block079Part000 : ℚ :=
  (110591166975 : ℚ) / 2673015528814948352

def SurrogateDiagonalTailChunk001Sub000Block079Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19749
    = surrogateDiagTailX0RatChunk001Sub000Block079Part000

theorem surrogateDiagonalTailChunk001Sub000Block079Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block079Part000CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block079Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block079Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block079Part000CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block079Part000SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block079Part000] using hcert

def TailChunk001Sub000Block079Part001SupportExplicit : Finset ℕ :=
  ([19751] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block079Part001 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block079Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19751
    = surrogateDiagTailX0RatChunk001Sub000Block079Part001

theorem surrogateDiagonalTailChunk001Sub000Block079Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block079Part001CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block079Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block079Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block079Part001CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block079Part001SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block079Part001] using hcert

def TailChunk001Sub000Block079Part002SupportExplicit : Finset ℕ :=
  ([19753] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block079Part002 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block079Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19753
    = surrogateDiagTailX0RatChunk001Sub000Block079Part002

theorem surrogateDiagonalTailChunk001Sub000Block079Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block079Part002CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block079Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block079Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block079Part002CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block079Part002SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block079Part002] using hcert

def TailChunk001Sub000Block079Part003SupportExplicit : Finset ℕ :=
  ([19754] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block079Part003 : ℚ :=
  (4259663789275 : ℚ) / 9602121579236425728

def SurrogateDiagonalTailChunk001Sub000Block079Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19754
    = surrogateDiagTailX0RatChunk001Sub000Block079Part003

theorem surrogateDiagonalTailChunk001Sub000Block079Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block079Part003CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block079Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block079Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block079Part003CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block079Part003SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block079Part003] using hcert

def TailChunk001Sub000Block079Part004SupportExplicit : Finset ℕ :=
  ([19757] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block079Part004 : ℚ :=
  (236732055025 : ℚ) / 317443715420367938688

def SurrogateDiagonalTailChunk001Sub000Block079Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19757
    = surrogateDiagTailX0RatChunk001Sub000Block079Part004

theorem surrogateDiagonalTailChunk001Sub000Block079Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block079Part004CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block079Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block079Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block079Part004CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block079Part004SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block079Part004] using hcert

def TailChunk001Sub000Block079Part005SupportExplicit : Finset ℕ :=
  ([19758] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block079Part005 : ℚ :=
  (291968101625 : ℚ) / 366348863042224128

def SurrogateDiagonalTailChunk001Sub000Block079Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19758
    = surrogateDiagTailX0RatChunk001Sub000Block079Part005

theorem surrogateDiagonalTailChunk001Sub000Block079Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block079Part005CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block079Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block079Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block079Part005CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block079Part005SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block079Part005] using hcert

def TailChunk001Sub000Block079Part006SupportExplicit : Finset ℕ :=
  ([19759] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block079Part006 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block079Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19759
    = surrogateDiagTailX0RatChunk001Sub000Block079Part006

theorem surrogateDiagonalTailChunk001Sub000Block079Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block079Part006CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block079Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block079Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block079Part006CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block079Part006SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block079Part006] using hcert

def TailChunk001Sub000Block079Part007SupportExplicit : Finset ℕ :=
  ([19761] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block079Part007 : ℚ :=
  (95144806357 : ℚ) / 1619284835664691200

def SurrogateDiagonalTailChunk001Sub000Block079Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19761
    = surrogateDiagTailX0RatChunk001Sub000Block079Part007

theorem surrogateDiagonalTailChunk001Sub000Block079Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block079Part007CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block079Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block079Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block079Part007CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block079Part007SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block079Part007] using hcert

def TailChunk001Sub000Block079Part008SupportExplicit : Finset ℕ :=
  ([19762] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block079Part008 : ℚ :=
  (233811291349 : ℚ) / 849516429312000000

def SurrogateDiagonalTailChunk001Sub000Block079Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19762
    = surrogateDiagTailX0RatChunk001Sub000Block079Part008

theorem surrogateDiagonalTailChunk001Sub000Block079Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block079Part008CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block079Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block079Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block079Part008CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block079Part008SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block079Part008] using hcert

def TailChunk001Sub000Block079Part009SupportExplicit : Finset ℕ :=
  ([19763] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block079Part009 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block079Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19763
    = surrogateDiagTailX0RatChunk001Sub000Block079Part009

theorem surrogateDiagonalTailChunk001Sub000Block079Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block079Part009CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block079Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block079Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block079Part009CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block079Part009SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block079Part009] using hcert

def TailChunk001Sub000Block079Part010SupportExplicit : Finset ℕ :=
  ([19765] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block079Part010 : ℚ :=
  (267439144375 : ℚ) / 34363275127978401792

def SurrogateDiagonalTailChunk001Sub000Block079Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19765
    = surrogateDiagTailX0RatChunk001Sub000Block079Part010

theorem surrogateDiagonalTailChunk001Sub000Block079Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block079Part010CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block079Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block079Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block079Part010CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block079Part010SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block079Part010] using hcert

def TailChunk001Sub000Block079Part011SupportExplicit : Finset ℕ :=
  ([19766] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block079Part011 : ℚ :=
  (1526151390625 : ℚ) / 5961372581482684722

def SurrogateDiagonalTailChunk001Sub000Block079Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19766
    = surrogateDiagTailX0RatChunk001Sub000Block079Part011

theorem surrogateDiagonalTailChunk001Sub000Block079Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block079Part011CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block079Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block079Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block079Part011CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block079Part011SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block079Part011] using hcert

def TailChunk001Sub000Block079Part012SupportExplicit : Finset ℕ :=
  ([19767] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block079Part012 : ℚ :=
  (34949514957 : ℚ) / 682166383680870400

def SurrogateDiagonalTailChunk001Sub000Block079Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19767
    = surrogateDiagTailX0RatChunk001Sub000Block079Part012

theorem surrogateDiagonalTailChunk001Sub000Block079Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block079Part012CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block079Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block079Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block079Part012CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block079Part012SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block079Part012] using hcert

def TailChunk001Sub000Block079Part013SupportExplicit : Finset ℕ :=
  ([19769] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block079Part013 : ℚ :=
  (64262762975 : ℚ) / 175058014046630068224

def SurrogateDiagonalTailChunk001Sub000Block079Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19769
    = surrogateDiagTailX0RatChunk001Sub000Block079Part013

theorem surrogateDiagonalTailChunk001Sub000Block079Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block079Part013CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block079Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block079Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block079Part013CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block079Part013SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block079Part013] using hcert

def TailChunk001Sub000Block079Part014SupportExplicit : Finset ℕ :=
  ([19770] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block079Part014 : ℚ :=
  (830816088675 : ℚ) / 639984014885748736

def SurrogateDiagonalTailChunk001Sub000Block079Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19770
    = surrogateDiagTailX0RatChunk001Sub000Block079Part014

theorem surrogateDiagonalTailChunk001Sub000Block079Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block079Part014CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block079Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block079Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block079Part014CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block079Part014SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block079Part014] using hcert

def TailChunk001Sub000Block079Part015SupportExplicit : Finset ℕ :=
  ([19771] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block079Part015 : ℚ :=
  (426612273025 : ℚ) / 298766088815887515648

def SurrogateDiagonalTailChunk001Sub000Block079Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19771
    = surrogateDiagTailX0RatChunk001Sub000Block079Part015

theorem surrogateDiagonalTailChunk001Sub000Block079Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block079Part015CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block079Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block079Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block079Part015CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block079Part015SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block079Part015] using hcert

def TailChunk001Sub000Block079Part016SupportExplicit : Finset ℕ :=
  ([19774] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block079Part016 : ℚ :=
  (1527387015625 : ℚ) / 5971030534273402002

def SurrogateDiagonalTailChunk001Sub000Block079Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19774
    = surrogateDiagTailX0RatChunk001Sub000Block079Part016

theorem surrogateDiagonalTailChunk001Sub000Block079Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block079Part016CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block079Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block079Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block079Part016CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block079Part016SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block079Part016] using hcert

def TailChunk001Sub000Block079Part017SupportExplicit : Finset ℕ :=
  ([19777] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block079Part017 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block079Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19777
    = surrogateDiagTailX0RatChunk001Sub000Block079Part017

theorem surrogateDiagonalTailChunk001Sub000Block079Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block079Part017CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block079Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block079Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block079Part017CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block079Part017SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block079Part017] using hcert

def TailChunk001Sub000Block079Part018SupportExplicit : Finset ℕ :=
  ([19778] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block079Part018 : ℚ :=
  (63360226519 : ℚ) / 165990311424000000

def SurrogateDiagonalTailChunk001Sub000Block079Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19778
    = surrogateDiagTailX0RatChunk001Sub000Block079Part018

theorem surrogateDiagonalTailChunk001Sub000Block079Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block079Part018CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block079Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block079Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block079Part018CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block079Part018SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block079Part018] using hcert

def TailChunk001Sub000Block079Part019SupportExplicit : Finset ℕ :=
  ([19779] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block079Part019 : ℚ :=
  (884153379475 : ℚ) / 20064114724330838016

def SurrogateDiagonalTailChunk001Sub000Block079Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19779
    = surrogateDiagTailX0RatChunk001Sub000Block079Part019

theorem surrogateDiagonalTailChunk001Sub000Block079Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block079Part019CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block079Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block079Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block079Part019CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block079Part019SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block079Part019] using hcert

def TailChunk001Sub000Block079Part020SupportExplicit : Finset ℕ :=
  ([19781] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block079Part020 : ℚ :=
  (692493803 : ℚ) / 2892379610250000000

def SurrogateDiagonalTailChunk001Sub000Block079Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19781
    = surrogateDiagTailX0RatChunk001Sub000Block079Part020

theorem surrogateDiagonalTailChunk001Sub000Block079Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block079Part020CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block079Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block079Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block079Part020CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block079Part020SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block079Part020] using hcert

def TailChunk001Sub000Block079Part021SupportExplicit : Finset ℕ :=
  ([19783] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block079Part021 : ℚ :=
  (4163184673 : ℚ) / 14284725280277299200

def SurrogateDiagonalTailChunk001Sub000Block079Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19783
    = surrogateDiagTailX0RatChunk001Sub000Block079Part021

theorem surrogateDiagonalTailChunk001Sub000Block079Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block079Part021CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block079Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block079Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block079Part021CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block079Part021SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block079Part021] using hcert

def TailChunk001Sub000Block079Part022SupportExplicit : Finset ℕ :=
  ([19785] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block079Part022 : ℚ :=
  (190199044125 : ℚ) / 2575533492338581504

def SurrogateDiagonalTailChunk001Sub000Block079Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19785
    = surrogateDiagTailX0RatChunk001Sub000Block079Part022

theorem surrogateDiagonalTailChunk001Sub000Block079Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block079Part022CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block079Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block079Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block079Part022CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block079Part022SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block079Part022] using hcert

def TailChunk001Sub000Block079Part023SupportExplicit : Finset ℕ :=
  ([19786] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block079Part023 : ℚ :=
  (215334661489 : ℚ) / 691936441152307200

def SurrogateDiagonalTailChunk001Sub000Block079Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19786
    = surrogateDiagTailX0RatChunk001Sub000Block079Part023

theorem surrogateDiagonalTailChunk001Sub000Block079Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block079Part023CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block079Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block079Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block079Part023CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block079Part023SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block079Part023] using hcert

def TailChunk001Sub000Block079Part024SupportExplicit : Finset ℕ :=
  ([19787] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block079Part024 : ℚ :=
  (1170690989 : ℚ) / 2787053684352215040

def SurrogateDiagonalTailChunk001Sub000Block079Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19787
    = surrogateDiagTailX0RatChunk001Sub000Block079Part024

theorem surrogateDiagonalTailChunk001Sub000Block079Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block079Part024CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block079Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block079Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block079Part024CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block079Part024SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block079Part024] using hcert

def surrogateDiagonalTailChunk001Sub000Block079HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block079Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block079Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block079Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block079Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block079Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block079Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block079Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block079Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block079Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block079Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block079Head : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block079Part000
    + surrogateDiagTailX0RatChunk001Sub000Block079Part001
    + surrogateDiagTailX0RatChunk001Sub000Block079Part002
    + surrogateDiagTailX0RatChunk001Sub000Block079Part003
    + surrogateDiagTailX0RatChunk001Sub000Block079Part004
    + surrogateDiagTailX0RatChunk001Sub000Block079Part005
    + surrogateDiagTailX0RatChunk001Sub000Block079Part006
    + surrogateDiagTailX0RatChunk001Sub000Block079Part007
    + surrogateDiagTailX0RatChunk001Sub000Block079Part008
    + surrogateDiagTailX0RatChunk001Sub000Block079Part009

def surrogateDiagonalTailChunk001Sub000Block079MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block079Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block079Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block079Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block079Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block079Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block079Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block079Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block079Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block079Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block079Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block079Mid : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block079Part010
    + surrogateDiagTailX0RatChunk001Sub000Block079Part011
    + surrogateDiagTailX0RatChunk001Sub000Block079Part012
    + surrogateDiagTailX0RatChunk001Sub000Block079Part013
    + surrogateDiagTailX0RatChunk001Sub000Block079Part014
    + surrogateDiagTailX0RatChunk001Sub000Block079Part015
    + surrogateDiagTailX0RatChunk001Sub000Block079Part016
    + surrogateDiagTailX0RatChunk001Sub000Block079Part017
    + surrogateDiagTailX0RatChunk001Sub000Block079Part018
    + surrogateDiagTailX0RatChunk001Sub000Block079Part019

def surrogateDiagonalTailChunk001Sub000Block079TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block079Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block079Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block079Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block079Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block079Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block079Tail : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block079Part020
    + surrogateDiagTailX0RatChunk001Sub000Block079Part021
    + surrogateDiagTailX0RatChunk001Sub000Block079Part022
    + surrogateDiagTailX0RatChunk001Sub000Block079Part023
    + surrogateDiagTailX0RatChunk001Sub000Block079Part024

def surrogateDiagonalTailChunk001Sub000Block079Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk001Sub000Block079HeadSum X0
    + surrogateDiagonalTailChunk001Sub000Block079MidSum X0
    + surrogateDiagonalTailChunk001Sub000Block079TailSum X0

def surrogateDiagTailX0RatChunk001Sub000Block079 : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block079Part000
    + surrogateDiagTailX0RatChunk001Sub000Block079Part001
    + surrogateDiagTailX0RatChunk001Sub000Block079Part002
    + surrogateDiagTailX0RatChunk001Sub000Block079Part003
    + surrogateDiagTailX0RatChunk001Sub000Block079Part004
    + surrogateDiagTailX0RatChunk001Sub000Block079Part005
    + surrogateDiagTailX0RatChunk001Sub000Block079Part006
    + surrogateDiagTailX0RatChunk001Sub000Block079Part007
    + surrogateDiagTailX0RatChunk001Sub000Block079Part008
    + surrogateDiagTailX0RatChunk001Sub000Block079Part009
    + surrogateDiagTailX0RatChunk001Sub000Block079Part010
    + surrogateDiagTailX0RatChunk001Sub000Block079Part011
    + surrogateDiagTailX0RatChunk001Sub000Block079Part012
    + surrogateDiagTailX0RatChunk001Sub000Block079Part013
    + surrogateDiagTailX0RatChunk001Sub000Block079Part014
    + surrogateDiagTailX0RatChunk001Sub000Block079Part015
    + surrogateDiagTailX0RatChunk001Sub000Block079Part016
    + surrogateDiagTailX0RatChunk001Sub000Block079Part017
    + surrogateDiagTailX0RatChunk001Sub000Block079Part018
    + surrogateDiagTailX0RatChunk001Sub000Block079Part019
    + surrogateDiagTailX0RatChunk001Sub000Block079Part020
    + surrogateDiagTailX0RatChunk001Sub000Block079Part021
    + surrogateDiagTailX0RatChunk001Sub000Block079Part022
    + surrogateDiagTailX0RatChunk001Sub000Block079Part023
    + surrogateDiagTailX0RatChunk001Sub000Block079Part024

theorem surrogateDiagTailX0RatChunk001Sub000Block079_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk001Sub000Block079Head + surrogateDiagTailX0RatChunk001Sub000Block079Mid + surrogateDiagTailX0RatChunk001Sub000Block079Tail =
      surrogateDiagTailX0RatChunk001Sub000Block079 := by
  unfold surrogateDiagTailX0RatChunk001Sub000Block079Head surrogateDiagTailX0RatChunk001Sub000Block079Mid surrogateDiagTailX0RatChunk001Sub000Block079Tail surrogateDiagTailX0RatChunk001Sub000Block079
  ring

def SurrogateDiagonalTailChunk001Sub000Block079HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block079HeadSum X0 = surrogateDiagTailX0RatChunk001Sub000Block079Head

def SurrogateDiagonalTailChunk001Sub000Block079MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block079MidSum X0 = surrogateDiagTailX0RatChunk001Sub000Block079Mid

def SurrogateDiagonalTailChunk001Sub000Block079TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block079TailSum X0 = surrogateDiagTailX0RatChunk001Sub000Block079Tail

theorem surrogateDiagonalTailChunk001Sub000Block079_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk001Sub000Block079HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk001Sub000Block079MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk001Sub000Block079TailCertificateAt X0) :
    surrogateDiagonalTailChunk001Sub000Block079Sum X0 = surrogateDiagTailX0RatChunk001Sub000Block079 := by
  unfold SurrogateDiagonalTailChunk001Sub000Block079HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk001Sub000Block079MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk001Sub000Block079TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk001Sub000Block079Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk001Sub000Block079_eq_head_add_mid_add_tail

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

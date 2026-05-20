import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0TailPilot25

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

open scoped BigOperators

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

/- Generated direct-term certificate blocks for tail chunk 000, subchunk 000, blocks [130,131). -/

/- Block 130 covers tail-support indices [3250,3275) and q from 5399 to 5438. -/

def TailChunk000Sub000Block130Part000SupportExplicit : Finset ℕ :=
  ([5399] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block130Part000 : ℚ :=
  (455456265625 : ℚ) / 530760248115468402

def SurrogateDiagonalTailChunk000Sub000Block130Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5399
    = surrogateDiagTailX0RatChunk000Sub000Block130Part000

theorem surrogateDiagonalTailChunk000Sub000Block130Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block130Part000CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block130Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block130Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block130Part000CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block130Part000SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block130Part000] using hcert

def TailChunk000Sub000Block130Part001SupportExplicit : Finset ℕ :=
  ([5401] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block130Part001 : ℚ :=
  (32782542167 : ℚ) / 28829769801000000

def SurrogateDiagonalTailChunk000Sub000Block130Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5401
    = surrogateDiagTailX0RatChunk000Sub000Block130Part001

theorem surrogateDiagonalTailChunk000Sub000Block130Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block130Part001CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block130Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block130Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block130Part001CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block130Part001SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block130Part001] using hcert

def TailChunk000Sub000Block130Part002SupportExplicit : Finset ℕ :=
  ([5402] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block130Part002 : ℚ :=
  (452792815075 : ℚ) / 112866965177499648

def SurrogateDiagonalTailChunk000Sub000Block130Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5402
    = surrogateDiagTailX0RatChunk000Sub000Block130Part002

theorem surrogateDiagonalTailChunk000Sub000Block130Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block130Part002CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block130Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block130Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block130Part002CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block130Part002SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block130Part002] using hcert

def TailChunk000Sub000Block130Part003SupportExplicit : Finset ℕ :=
  ([5403] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block130Part003 : ℚ :=
  (1620833 : ℚ) / 559872000000

def SurrogateDiagonalTailChunk000Sub000Block130Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5403
    = surrogateDiagTailX0RatChunk000Sub000Block130Part003

theorem surrogateDiagonalTailChunk000Sub000Block130Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block130Part003CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block130Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block130Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block130Part003CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block130Part003SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block130Part003] using hcert

def TailChunk000Sub000Block130Part004SupportExplicit : Finset ℕ :=
  ([5405] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block130Part004 : ℚ :=
  (453526560825 : ℚ) / 223803884143476736

def SurrogateDiagonalTailChunk000Sub000Block130Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5405
    = surrogateDiagTailX0RatChunk000Sub000Block130Part004

theorem surrogateDiagonalTailChunk000Sub000Block130Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block130Part004CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block130Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block130Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block130Part004CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block130Part004SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block130Part004] using hcert

def TailChunk000Sub000Block130Part005SupportExplicit : Finset ℕ :=
  ([5406] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block130Part005 : ℚ :=
  (559323994825 : ℚ) / 19170796039569408

def SurrogateDiagonalTailChunk000Sub000Block130Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5406
    = surrogateDiagTailX0RatChunk000Sub000Block130Part005

theorem surrogateDiagonalTailChunk000Sub000Block130Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block130Part005CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block130Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block130Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block130Part005CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block130Part005SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block130Part005] using hcert

def TailChunk000Sub000Block130Part006SupportExplicit : Finset ℕ :=
  ([5407] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block130Part006 : ℚ :=
  (456807015625 : ℚ) / 533913660896713362

def SurrogateDiagonalTailChunk000Sub000Block130Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5407
    = surrogateDiagTailX0RatChunk000Sub000Block130Part006

theorem surrogateDiagonalTailChunk000Sub000Block130Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block130Part006CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block130Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block130Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block130Part006CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block130Part006SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block130Part006] using hcert

def TailChunk000Sub000Block130Part007SupportExplicit : Finset ℕ :=
  ([5410] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block130Part007 : ℚ :=
  (131881919 : ℚ) / 10079711539200

def SurrogateDiagonalTailChunk000Sub000Block130Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5410
    = surrogateDiagTailX0RatChunk000Sub000Block130Part007

theorem surrogateDiagonalTailChunk000Sub000Block130Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block130Part007CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block130Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block130Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block130Part007CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block130Part007SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block130Part007] using hcert

def TailChunk000Sub000Block130Part008SupportExplicit : Finset ℕ :=
  ([5411] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block130Part008 : ℚ :=
  (87035726575 : ℚ) / 63948234175497216

def SurrogateDiagonalTailChunk000Sub000Block130Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5411
    = surrogateDiagTailX0RatChunk000Sub000Block130Part008

theorem surrogateDiagonalTailChunk000Sub000Block130Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block130Part008CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block130Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block130Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block130Part008CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block130Part008SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block130Part008] using hcert

def TailChunk000Sub000Block130Part009SupportExplicit : Finset ℕ :=
  ([5413] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block130Part009 : ℚ :=
  (457821390625 : ℚ) / 536287925878908192

def SurrogateDiagonalTailChunk000Sub000Block130Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5413
    = surrogateDiagTailX0RatChunk000Sub000Block130Part009

theorem surrogateDiagonalTailChunk000Sub000Block130Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block130Part009CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block130Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block130Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block130Part009CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block130Part009SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block130Part009] using hcert

def TailChunk000Sub000Block130Part010SupportExplicit : Finset ℕ :=
  ([5414] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block130Part010 : ℚ :=
  (915797928775 : ℚ) / 134071981469727048

def SurrogateDiagonalTailChunk000Sub000Block130Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5414
    = surrogateDiagTailX0RatChunk000Sub000Block130Part010

theorem surrogateDiagonalTailChunk000Sub000Block130Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block130Part010CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block130Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block130Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block130Part010CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block130Part010SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block130Part010] using hcert

def TailChunk000Sub000Block130Part011SupportExplicit : Finset ℕ :=
  ([5417] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block130Part011 : ℚ :=
  (458498265625 : ℚ) / 537875162458747392

def SurrogateDiagonalTailChunk000Sub000Block130Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5417
    = surrogateDiagTailX0RatChunk000Sub000Block130Part011

theorem surrogateDiagonalTailChunk000Sub000Block130Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block130Part011CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block130Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block130Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block130Part011CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block130Part011SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block130Part011] using hcert

def TailChunk000Sub000Block130Part012SupportExplicit : Finset ℕ :=
  ([5419] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block130Part012 : ℚ :=
  (458836890625 : ℚ) / 538670100675249522

def SurrogateDiagonalTailChunk000Sub000Block130Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5419
    = surrogateDiagTailX0RatChunk000Sub000Block130Part012

theorem surrogateDiagonalTailChunk000Sub000Block130Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block130Part012CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block130Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block130Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block130Part012CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block130Part012SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block130Part012] using hcert

def TailChunk000Sub000Block130Part013SupportExplicit : Finset ℕ :=
  ([5421] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block130Part013 : ℚ :=
  (1114595309875 : ℚ) / 300876432729735168

def SurrogateDiagonalTailChunk000Sub000Block130Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5421
    = surrogateDiagTailX0RatChunk000Sub000Block130Part013

theorem surrogateDiagonalTailChunk000Sub000Block130Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block130Part013CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block130Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block130Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block130Part013CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block130Part013SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block130Part013] using hcert

def TailChunk000Sub000Block130Part014SupportExplicit : Finset ℕ :=
  ([5422] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block130Part014 : ℚ :=
  (36740255479 : ℚ) / 5394659197096200

def SurrogateDiagonalTailChunk000Sub000Block130Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5422
    = surrogateDiagTailX0RatChunk000Sub000Block130Part014

theorem surrogateDiagonalTailChunk000Sub000Block130Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block130Part014CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block130Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block130Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block130Part014CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block130Part014SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block130Part014] using hcert

def TailChunk000Sub000Block130Part015SupportExplicit : Finset ℕ :=
  ([5423] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block130Part015 : ℚ :=
  (9979096347 : ℚ) / 6715025339187200

def SurrogateDiagonalTailChunk000Sub000Block130Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5423
    = surrogateDiagTailX0RatChunk000Sub000Block130Part015

theorem surrogateDiagonalTailChunk000Sub000Block130Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block130Part015CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block130Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block130Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block130Part015CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block130Part015SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block130Part015] using hcert

def TailChunk000Sub000Block130Part016SupportExplicit : Finset ℕ :=
  ([5426] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block130Part016 : ℚ :=
  (919862115775 : ℚ) / 135265050708461568

def SurrogateDiagonalTailChunk000Sub000Block130Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5426
    = surrogateDiagTailX0RatChunk000Sub000Block130Part016

theorem surrogateDiagonalTailChunk000Sub000Block130Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block130Part016CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block130Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block130Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block130Part016CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block130Part016SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block130Part016] using hcert

def TailChunk000Sub000Block130Part017SupportExplicit : Finset ℕ :=
  ([5429] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block130Part017 : ℚ :=
  (71535558751 : ℚ) / 77736062759731200

def SurrogateDiagonalTailChunk000Sub000Block130Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5429
    = surrogateDiagTailX0RatChunk000Sub000Block130Part017

theorem surrogateDiagonalTailChunk000Sub000Block130Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block130Part017CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block130Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block130Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block130Part017CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block130Part017SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block130Part017] using hcert

def TailChunk000Sub000Block130Part018SupportExplicit : Finset ℕ :=
  ([5430] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block130Part018 : ℚ :=
  (1938122353 : ℚ) / 43006769233920

def SurrogateDiagonalTailChunk000Sub000Block130Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5430
    = surrogateDiagTailX0RatChunk000Sub000Block130Part018

theorem surrogateDiagonalTailChunk000Sub000Block130Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block130Part018CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block130Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block130Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block130Part018CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block130Part018SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block130Part018] using hcert

def TailChunk000Sub000Block130Part019SupportExplicit : Finset ℕ :=
  ([5431] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block130Part019 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub000Block130Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5431
    = surrogateDiagTailX0RatChunk000Sub000Block130Part019

theorem surrogateDiagonalTailChunk000Sub000Block130Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block130Part019CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block130Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block130Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block130Part019CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block130Part019SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block130Part019] using hcert

def TailChunk000Sub000Block130Part020SupportExplicit : Finset ℕ :=
  ([5433] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block130Part020 : ℚ :=
  (8201110829 : ℚ) / 8587982220993600

def SurrogateDiagonalTailChunk000Sub000Block130Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5433
    = surrogateDiagTailX0RatChunk000Sub000Block130Part020

theorem surrogateDiagonalTailChunk000Sub000Block130Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block130Part020CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block130Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block130Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block130Part020CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block130Part020SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block130Part020] using hcert

def TailChunk000Sub000Block130Part021SupportExplicit : Finset ℕ :=
  ([5434] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block130Part021 : ℚ :=
  (289578007 : ℚ) / 36286961541120

def SurrogateDiagonalTailChunk000Sub000Block130Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5434
    = surrogateDiagTailX0RatChunk000Sub000Block130Part021

theorem surrogateDiagonalTailChunk000Sub000Block130Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block130Part021CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block130Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block130Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block130Part021CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block130Part021SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block130Part021] using hcert

def TailChunk000Sub000Block130Part022SupportExplicit : Finset ℕ :=
  ([5435] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block130Part022 : ℚ :=
  (737894924375 : ℚ) / 445200998336308224

def SurrogateDiagonalTailChunk000Sub000Block130Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5435
    = surrogateDiagTailX0RatChunk000Sub000Block130Part022

theorem surrogateDiagonalTailChunk000Sub000Block130Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block130Part022CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block130Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block130Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block130Part022CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block130Part022SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block130Part022] using hcert

def TailChunk000Sub000Block130Part023SupportExplicit : Finset ℕ :=
  ([5437] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block130Part023 : ℚ :=
  (461890140625 : ℚ) / 545864259527461152

def SurrogateDiagonalTailChunk000Sub000Block130Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5437
    = surrogateDiagTailX0RatChunk000Sub000Block130Part023

theorem surrogateDiagonalTailChunk000Sub000Block130Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block130Part023CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block130Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block130Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block130Part023CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block130Part023SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block130Part023] using hcert

def TailChunk000Sub000Block130Part024SupportExplicit : Finset ℕ :=
  ([5438] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block130Part024 : ℚ :=
  (923935300975 : ℚ) / 136466064881865288

def SurrogateDiagonalTailChunk000Sub000Block130Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5438
    = surrogateDiagTailX0RatChunk000Sub000Block130Part024

theorem surrogateDiagonalTailChunk000Sub000Block130Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block130Part024CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block130Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block130Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block130Part024CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block130Part024SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block130Part024] using hcert

def surrogateDiagonalTailChunk000Sub000Block130HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block130Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block130Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block130Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block130Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block130Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block130Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block130Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block130Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block130Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block130Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block130Head : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block130Part000
    + surrogateDiagTailX0RatChunk000Sub000Block130Part001
    + surrogateDiagTailX0RatChunk000Sub000Block130Part002
    + surrogateDiagTailX0RatChunk000Sub000Block130Part003
    + surrogateDiagTailX0RatChunk000Sub000Block130Part004
    + surrogateDiagTailX0RatChunk000Sub000Block130Part005
    + surrogateDiagTailX0RatChunk000Sub000Block130Part006
    + surrogateDiagTailX0RatChunk000Sub000Block130Part007
    + surrogateDiagTailX0RatChunk000Sub000Block130Part008
    + surrogateDiagTailX0RatChunk000Sub000Block130Part009

def surrogateDiagonalTailChunk000Sub000Block130MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block130Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block130Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block130Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block130Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block130Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block130Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block130Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block130Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block130Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block130Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block130Mid : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block130Part010
    + surrogateDiagTailX0RatChunk000Sub000Block130Part011
    + surrogateDiagTailX0RatChunk000Sub000Block130Part012
    + surrogateDiagTailX0RatChunk000Sub000Block130Part013
    + surrogateDiagTailX0RatChunk000Sub000Block130Part014
    + surrogateDiagTailX0RatChunk000Sub000Block130Part015
    + surrogateDiagTailX0RatChunk000Sub000Block130Part016
    + surrogateDiagTailX0RatChunk000Sub000Block130Part017
    + surrogateDiagTailX0RatChunk000Sub000Block130Part018
    + surrogateDiagTailX0RatChunk000Sub000Block130Part019

def surrogateDiagonalTailChunk000Sub000Block130TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block130Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block130Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block130Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block130Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block130Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block130Tail : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block130Part020
    + surrogateDiagTailX0RatChunk000Sub000Block130Part021
    + surrogateDiagTailX0RatChunk000Sub000Block130Part022
    + surrogateDiagTailX0RatChunk000Sub000Block130Part023
    + surrogateDiagTailX0RatChunk000Sub000Block130Part024

def surrogateDiagonalTailChunk000Sub000Block130Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub000Block130HeadSum X0
    + surrogateDiagonalTailChunk000Sub000Block130MidSum X0
    + surrogateDiagonalTailChunk000Sub000Block130TailSum X0

def surrogateDiagTailX0RatChunk000Sub000Block130 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block130Part000
    + surrogateDiagTailX0RatChunk000Sub000Block130Part001
    + surrogateDiagTailX0RatChunk000Sub000Block130Part002
    + surrogateDiagTailX0RatChunk000Sub000Block130Part003
    + surrogateDiagTailX0RatChunk000Sub000Block130Part004
    + surrogateDiagTailX0RatChunk000Sub000Block130Part005
    + surrogateDiagTailX0RatChunk000Sub000Block130Part006
    + surrogateDiagTailX0RatChunk000Sub000Block130Part007
    + surrogateDiagTailX0RatChunk000Sub000Block130Part008
    + surrogateDiagTailX0RatChunk000Sub000Block130Part009
    + surrogateDiagTailX0RatChunk000Sub000Block130Part010
    + surrogateDiagTailX0RatChunk000Sub000Block130Part011
    + surrogateDiagTailX0RatChunk000Sub000Block130Part012
    + surrogateDiagTailX0RatChunk000Sub000Block130Part013
    + surrogateDiagTailX0RatChunk000Sub000Block130Part014
    + surrogateDiagTailX0RatChunk000Sub000Block130Part015
    + surrogateDiagTailX0RatChunk000Sub000Block130Part016
    + surrogateDiagTailX0RatChunk000Sub000Block130Part017
    + surrogateDiagTailX0RatChunk000Sub000Block130Part018
    + surrogateDiagTailX0RatChunk000Sub000Block130Part019
    + surrogateDiagTailX0RatChunk000Sub000Block130Part020
    + surrogateDiagTailX0RatChunk000Sub000Block130Part021
    + surrogateDiagTailX0RatChunk000Sub000Block130Part022
    + surrogateDiagTailX0RatChunk000Sub000Block130Part023
    + surrogateDiagTailX0RatChunk000Sub000Block130Part024

theorem surrogateDiagTailX0RatChunk000Sub000Block130_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk000Sub000Block130Head + surrogateDiagTailX0RatChunk000Sub000Block130Mid + surrogateDiagTailX0RatChunk000Sub000Block130Tail =
      surrogateDiagTailX0RatChunk000Sub000Block130 := by
  unfold surrogateDiagTailX0RatChunk000Sub000Block130Head surrogateDiagTailX0RatChunk000Sub000Block130Mid surrogateDiagTailX0RatChunk000Sub000Block130Tail surrogateDiagTailX0RatChunk000Sub000Block130
  ring

def SurrogateDiagonalTailChunk000Sub000Block130HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block130HeadSum X0 = surrogateDiagTailX0RatChunk000Sub000Block130Head

def SurrogateDiagonalTailChunk000Sub000Block130MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block130MidSum X0 = surrogateDiagTailX0RatChunk000Sub000Block130Mid

def SurrogateDiagonalTailChunk000Sub000Block130TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block130TailSum X0 = surrogateDiagTailX0RatChunk000Sub000Block130Tail

theorem surrogateDiagonalTailChunk000Sub000Block130_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk000Sub000Block130HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk000Sub000Block130MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk000Sub000Block130TailCertificateAt X0) :
    surrogateDiagonalTailChunk000Sub000Block130Sum X0 = surrogateDiagTailX0RatChunk000Sub000Block130 := by
  unfold SurrogateDiagonalTailChunk000Sub000Block130HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk000Sub000Block130MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk000Sub000Block130TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk000Sub000Block130Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk000Sub000Block130_eq_head_add_mid_add_tail

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

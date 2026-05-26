import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0TailPilot25

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

open scoped BigOperators

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

/- Generated direct-term certificate blocks for tail chunk 001, subchunk 000, blocks [20,30). -/

/-- Block 020 covers tail-support indices [10500,10525) and q from 17318 to 17357. -/

def TailChunk001Sub000Block020Part000SupportExplicit : Finset ℕ :=
  ([17318] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block020Part000 : ℚ :=
  (207011316875 : ℚ) / 420177931097342976

def SurrogateDiagonalTailChunk001Sub000Block020Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17318
    = surrogateDiagTailX0RatChunk001Sub000Block020Part000

theorem surrogateDiagonalTailChunk001Sub000Block020Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block020Part000CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block020Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block020Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block020Part000CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block020Part000SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block020Part000] using hcert

def TailChunk001Sub000Block020Part001SupportExplicit : Finset ℕ :=
  ([17319] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block020Part001 : ℚ :=
  (25682580303 : ℚ) / 122032735000000000

def SurrogateDiagonalTailChunk001Sub000Block020Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17319
    = surrogateDiagTailX0RatChunk001Sub000Block020Part001

theorem surrogateDiagonalTailChunk001Sub000Block020Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block020Part001CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block020Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block020Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block020Part001CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block020Part001SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block020Part001] using hcert

def TailChunk001Sub000Block020Part002SupportExplicit : Finset ℕ :=
  ([17321] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block020Part002 : ℚ :=
  (7500426025 : ℚ) / 90007438197821952

def SurrogateDiagonalTailChunk001Sub000Block020Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17321
    = surrogateDiagTailX0RatChunk001Sub000Block020Part002

theorem surrogateDiagonalTailChunk001Sub000Block020Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block020Part002CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block020Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block020Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block020Part002CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block020Part002SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block020Part002] using hcert

def TailChunk001Sub000Block020Part003SupportExplicit : Finset ℕ :=
  ([17322] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block020Part003 : ℚ :=
  (2082873711325 : ℚ) / 2775441952115584128

def SurrogateDiagonalTailChunk001Sub000Block020Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17322
    = surrogateDiagTailX0RatChunk001Sub000Block020Part003

theorem surrogateDiagonalTailChunk001Sub000Block020Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block020Part003CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block020Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block020Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block020Part003CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block020Part003SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block020Part003] using hcert

def TailChunk001Sub000Block020Part004SupportExplicit : Finset ℕ :=
  ([17323] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block020Part004 : ℚ :=
  (5615582006625 : ℚ) / 58664671994543865856

def SurrogateDiagonalTailChunk001Sub000Block020Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17323
    = surrogateDiagTailX0RatChunk001Sub000Block020Part004

theorem surrogateDiagonalTailChunk001Sub000Block020Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block020Part004CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block020Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block020Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block020Part004CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block020Part004SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block020Part004] using hcert

def TailChunk001Sub000Block020Part005SupportExplicit : Finset ℕ :=
  ([17326] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block020Part005 : ℚ :=
  (1172618265625 : ℚ) / 3519164638876547442

def SurrogateDiagonalTailChunk001Sub000Block020Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17326
    = surrogateDiagTailX0RatChunk001Sub000Block020Part005

theorem surrogateDiagonalTailChunk001Sub000Block020Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block020Part005CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block020Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block020Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block020Part005CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block020Part005SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block020Part005] using hcert

def TailChunk001Sub000Block020Part006SupportExplicit : Finset ℕ :=
  ([17327] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block020Part006 : ℚ :=
  (4691014515625 : ℚ) / 56332640403323229522

def SurrogateDiagonalTailChunk001Sub000Block020Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17327
    = surrogateDiagTailX0RatChunk001Sub000Block020Part006

theorem surrogateDiagonalTailChunk001Sub000Block020Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block020Part006CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block020Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block020Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block020Part006CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block020Part006SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block020Part006] using hcert

def TailChunk001Sub000Block020Part007SupportExplicit : Finset ℕ :=
  ([17329] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block020Part007 : ℚ :=
  (65490275483 : ℚ) / 580833297734860800

def SurrogateDiagonalTailChunk001Sub000Block020Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17329
    = surrogateDiagTailX0RatChunk001Sub000Block020Part007

theorem surrogateDiagonalTailChunk001Sub000Block020Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block020Part007CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block020Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block020Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block020Part007CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block020Part007SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block020Part007] using hcert

def TailChunk001Sub000Block020Part008SupportExplicit : Finset ℕ :=
  ([17330] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block020Part008 : ℚ :=
  (1125525755775 : ℚ) / 1920158681553534976

def SurrogateDiagonalTailChunk001Sub000Block020Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17330
    = surrogateDiagTailX0RatChunk001Sub000Block020Part008

theorem surrogateDiagonalTailChunk001Sub000Block020Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block020Part008CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block020Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block020Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block020Part008CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block020Part008SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block020Part008] using hcert

def TailChunk001Sub000Block020Part009SupportExplicit : Finset ℕ :=
  ([17331] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block020Part009 : ℚ :=
  (665034079025 : ℚ) / 3316454107442970624

def SurrogateDiagonalTailChunk001Sub000Block020Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17331
    = surrogateDiagTailX0RatChunk001Sub000Block020Part009

theorem surrogateDiagonalTailChunk001Sub000Block020Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block020Part009CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block020Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block020Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block020Part009CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block020Part009SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block020Part009] using hcert

def TailChunk001Sub000Block020Part010SupportExplicit : Finset ℕ :=
  ([17333] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block020Part010 : ℚ :=
  (4694263890625 : ℚ) / 56410713000594154272

def SurrogateDiagonalTailChunk001Sub000Block020Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17333
    = surrogateDiagTailX0RatChunk001Sub000Block020Part010

theorem surrogateDiagonalTailChunk001Sub000Block020Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block020Part010CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block020Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block020Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block020Part010CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block020Part010SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block020Part010] using hcert

def TailChunk001Sub000Block020Part011SupportExplicit : Finset ℕ :=
  ([17335] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block020Part011 : ℚ :=
  (750900390625 : ℚ) / 5773791210550082688

def SurrogateDiagonalTailChunk001Sub000Block020Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17335
    = surrogateDiagTailX0RatChunk001Sub000Block020Part011

theorem surrogateDiagonalTailChunk001Sub000Block020Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block020Part011CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block020Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block020Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block020Part011CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block020Part011SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block020Part011] using hcert

def TailChunk001Sub000Block020Part012SupportExplicit : Finset ℕ :=
  ([17337] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block020Part012 : ℚ :=
  (8346945422125 : ℚ) / 44592004127928325248

def SurrogateDiagonalTailChunk001Sub000Block020Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17337
    = surrogateDiagTailX0RatChunk001Sub000Block020Part012

theorem surrogateDiagonalTailChunk001Sub000Block020Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block020Part012CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block020Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block020Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block020Part012CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block020Part012SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block020Part012] using hcert

def TailChunk001Sub000Block020Part013SupportExplicit : Finset ℕ :=
  ([17338] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block020Part013 : ℚ :=
  (1174243140625 : ℚ) / 3528925404003370272

def SurrogateDiagonalTailChunk001Sub000Block020Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17338
    = surrogateDiagTailX0RatChunk001Sub000Block020Part013

theorem surrogateDiagonalTailChunk001Sub000Block020Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block020Part013CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block020Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block020Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block020Part013CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block020Part013SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block020Part013] using hcert

def TailChunk001Sub000Block020Part014SupportExplicit : Finset ℕ :=
  ([17339] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block020Part014 : ℚ :=
  (14179746609025 : ℚ) / 121796391584789710848

def SurrogateDiagonalTailChunk001Sub000Block020Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17339
    = surrogateDiagTailX0RatChunk001Sub000Block020Part014

theorem surrogateDiagonalTailChunk001Sub000Block020Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block020Part014CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block020Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block020Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block020Part014CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block020Part014SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block020Part014] using hcert

def TailChunk001Sub000Block020Part015SupportExplicit : Finset ℕ :=
  ([17341] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block020Part015 : ℚ :=
  (7517757025 : ℚ) / 90423897598647072

def SurrogateDiagonalTailChunk001Sub000Block020Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17341
    = surrogateDiagTailX0RatChunk001Sub000Block020Part015

theorem surrogateDiagonalTailChunk001Sub000Block020Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block020Part015CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block020Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block020Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block020Part015CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block020Part015SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block020Part015] using hcert

def TailChunk001Sub000Block020Part016SupportExplicit : Finset ℕ :=
  ([17342] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block020Part016 : ℚ :=
  (1249502846225 : ℚ) / 2488590489148194816

def SurrogateDiagonalTailChunk001Sub000Block020Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17342
    = surrogateDiagTailX0RatChunk001Sub000Block020Part016

theorem surrogateDiagonalTailChunk001Sub000Block020Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block020Part016CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block020Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block020Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block020Part016CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block020Part016SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block020Part016] using hcert

def TailChunk001Sub000Block020Part017SupportExplicit : Finset ℕ :=
  ([17345] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block020Part017 : ℚ :=
  (250589046875 : ℚ) / 1929043148771137536

def SurrogateDiagonalTailChunk001Sub000Block020Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17345
    = surrogateDiagTailX0RatChunk001Sub000Block020Part017

theorem surrogateDiagonalTailChunk001Sub000Block020Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block020Part017CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block020Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block020Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block020Part017CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block020Part017SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block020Part017] using hcert

def TailChunk001Sub000Block020Part018SupportExplicit : Finset ℕ :=
  ([17347] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block020Part018 : ℚ :=
  (567028263817 : ℚ) / 4747142626453555200

def SurrogateDiagonalTailChunk001Sub000Block020Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17347
    = surrogateDiagTailX0RatChunk001Sub000Block020Part018

theorem surrogateDiagonalTailChunk001Sub000Block020Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block020Part018CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block020Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block020Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block020Part018CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block020Part018SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block020Part018] using hcert

def TailChunk001Sub000Block020Part019SupportExplicit : Finset ℕ :=
  ([17349] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block020Part019 : ℚ :=
  (8358505421725 : ℚ) / 44715613212878740608

def SurrogateDiagonalTailChunk001Sub000Block020Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17349
    = surrogateDiagTailX0RatChunk001Sub000Block020Part019

theorem surrogateDiagonalTailChunk001Sub000Block020Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block020Part019CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block020Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block020Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block020Part019CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block020Part019SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block020Part019] using hcert

def TailChunk001Sub000Block020Part020SupportExplicit : Finset ℕ :=
  ([17351] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block020Part020 : ℚ :=
  (301057201 : ℚ) / 3625306736614050

def SurrogateDiagonalTailChunk001Sub000Block020Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17351
    = surrogateDiagTailX0RatChunk001Sub000Block020Part020

theorem surrogateDiagonalTailChunk001Sub000Block020Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block020Part020CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block020Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block020Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block020Part020CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block020Part020SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block020Part020] using hcert

def TailChunk001Sub000Block020Part021SupportExplicit : Finset ℕ :=
  ([17353] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block020Part021 : ℚ :=
  (1469418300125 : ℚ) / 11475591924748419072

def SurrogateDiagonalTailChunk001Sub000Block020Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17353
    = surrogateDiagTailX0RatChunk001Sub000Block020Part021

theorem surrogateDiagonalTailChunk001Sub000Block020Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block020Part021CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block020Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block020Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block020Part021CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block020Part021SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block020Part021] using hcert

def TailChunk001Sub000Block020Part022SupportExplicit : Finset ℕ :=
  ([17354] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block020Part022 : ℚ :=
  (1176411390625 : ℚ) / 3541971325049847072

def SurrogateDiagonalTailChunk001Sub000Block020Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17354
    = surrogateDiagTailX0RatChunk001Sub000Block020Part022

theorem surrogateDiagonalTailChunk001Sub000Block020Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block020Part022CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block020Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block020Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block020Part022CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block020Part022SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block020Part022] using hcert

def TailChunk001Sub000Block020Part023SupportExplicit : Finset ℕ :=
  ([17355] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block020Part023 : ℚ :=
  (305471385475 : ℚ) / 796017282659647488

def SurrogateDiagonalTailChunk001Sub000Block020Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17355
    = surrogateDiagTailX0RatChunk001Sub000Block020Part023

theorem surrogateDiagonalTailChunk001Sub000Block020Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block020Part023CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block020Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block020Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block020Part023CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block020Part023SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block020Part023] using hcert

def TailChunk001Sub000Block020Part024SupportExplicit : Finset ℕ :=
  ([17357] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block020Part024 : ℚ :=
  (225506492281 : ℚ) / 2365082056418918400

def SurrogateDiagonalTailChunk001Sub000Block020Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17357
    = surrogateDiagTailX0RatChunk001Sub000Block020Part024

theorem surrogateDiagonalTailChunk001Sub000Block020Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block020Part024CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block020Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block020Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block020Part024CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block020Part024SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block020Part024] using hcert

def surrogateDiagonalTailChunk001Sub000Block020HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block020Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block020Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block020Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block020Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block020Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block020Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block020Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block020Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block020Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block020Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block020Head : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block020Part000
    + surrogateDiagTailX0RatChunk001Sub000Block020Part001
    + surrogateDiagTailX0RatChunk001Sub000Block020Part002
    + surrogateDiagTailX0RatChunk001Sub000Block020Part003
    + surrogateDiagTailX0RatChunk001Sub000Block020Part004
    + surrogateDiagTailX0RatChunk001Sub000Block020Part005
    + surrogateDiagTailX0RatChunk001Sub000Block020Part006
    + surrogateDiagTailX0RatChunk001Sub000Block020Part007
    + surrogateDiagTailX0RatChunk001Sub000Block020Part008
    + surrogateDiagTailX0RatChunk001Sub000Block020Part009

def surrogateDiagonalTailChunk001Sub000Block020MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block020Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block020Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block020Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block020Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block020Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block020Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block020Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block020Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block020Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block020Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block020Mid : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block020Part010
    + surrogateDiagTailX0RatChunk001Sub000Block020Part011
    + surrogateDiagTailX0RatChunk001Sub000Block020Part012
    + surrogateDiagTailX0RatChunk001Sub000Block020Part013
    + surrogateDiagTailX0RatChunk001Sub000Block020Part014
    + surrogateDiagTailX0RatChunk001Sub000Block020Part015
    + surrogateDiagTailX0RatChunk001Sub000Block020Part016
    + surrogateDiagTailX0RatChunk001Sub000Block020Part017
    + surrogateDiagTailX0RatChunk001Sub000Block020Part018
    + surrogateDiagTailX0RatChunk001Sub000Block020Part019

def surrogateDiagonalTailChunk001Sub000Block020TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block020Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block020Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block020Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block020Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block020Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block020Tail : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block020Part020
    + surrogateDiagTailX0RatChunk001Sub000Block020Part021
    + surrogateDiagTailX0RatChunk001Sub000Block020Part022
    + surrogateDiagTailX0RatChunk001Sub000Block020Part023
    + surrogateDiagTailX0RatChunk001Sub000Block020Part024

def surrogateDiagonalTailChunk001Sub000Block020Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk001Sub000Block020HeadSum X0
    + surrogateDiagonalTailChunk001Sub000Block020MidSum X0
    + surrogateDiagonalTailChunk001Sub000Block020TailSum X0

def surrogateDiagTailX0RatChunk001Sub000Block020 : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block020Part000
    + surrogateDiagTailX0RatChunk001Sub000Block020Part001
    + surrogateDiagTailX0RatChunk001Sub000Block020Part002
    + surrogateDiagTailX0RatChunk001Sub000Block020Part003
    + surrogateDiagTailX0RatChunk001Sub000Block020Part004
    + surrogateDiagTailX0RatChunk001Sub000Block020Part005
    + surrogateDiagTailX0RatChunk001Sub000Block020Part006
    + surrogateDiagTailX0RatChunk001Sub000Block020Part007
    + surrogateDiagTailX0RatChunk001Sub000Block020Part008
    + surrogateDiagTailX0RatChunk001Sub000Block020Part009
    + surrogateDiagTailX0RatChunk001Sub000Block020Part010
    + surrogateDiagTailX0RatChunk001Sub000Block020Part011
    + surrogateDiagTailX0RatChunk001Sub000Block020Part012
    + surrogateDiagTailX0RatChunk001Sub000Block020Part013
    + surrogateDiagTailX0RatChunk001Sub000Block020Part014
    + surrogateDiagTailX0RatChunk001Sub000Block020Part015
    + surrogateDiagTailX0RatChunk001Sub000Block020Part016
    + surrogateDiagTailX0RatChunk001Sub000Block020Part017
    + surrogateDiagTailX0RatChunk001Sub000Block020Part018
    + surrogateDiagTailX0RatChunk001Sub000Block020Part019
    + surrogateDiagTailX0RatChunk001Sub000Block020Part020
    + surrogateDiagTailX0RatChunk001Sub000Block020Part021
    + surrogateDiagTailX0RatChunk001Sub000Block020Part022
    + surrogateDiagTailX0RatChunk001Sub000Block020Part023
    + surrogateDiagTailX0RatChunk001Sub000Block020Part024

theorem surrogateDiagTailX0RatChunk001Sub000Block020_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk001Sub000Block020Head + surrogateDiagTailX0RatChunk001Sub000Block020Mid + surrogateDiagTailX0RatChunk001Sub000Block020Tail =
      surrogateDiagTailX0RatChunk001Sub000Block020 := by
  unfold surrogateDiagTailX0RatChunk001Sub000Block020Head surrogateDiagTailX0RatChunk001Sub000Block020Mid surrogateDiagTailX0RatChunk001Sub000Block020Tail surrogateDiagTailX0RatChunk001Sub000Block020
  ring

def SurrogateDiagonalTailChunk001Sub000Block020HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block020HeadSum X0 = surrogateDiagTailX0RatChunk001Sub000Block020Head

def SurrogateDiagonalTailChunk001Sub000Block020MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block020MidSum X0 = surrogateDiagTailX0RatChunk001Sub000Block020Mid

def SurrogateDiagonalTailChunk001Sub000Block020TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block020TailSum X0 = surrogateDiagTailX0RatChunk001Sub000Block020Tail

theorem surrogateDiagonalTailChunk001Sub000Block020_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk001Sub000Block020HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk001Sub000Block020MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk001Sub000Block020TailCertificateAt X0) :
    surrogateDiagonalTailChunk001Sub000Block020Sum X0 = surrogateDiagTailX0RatChunk001Sub000Block020 := by
  unfold SurrogateDiagonalTailChunk001Sub000Block020HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk001Sub000Block020MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk001Sub000Block020TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk001Sub000Block020Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk001Sub000Block020_eq_head_add_mid_add_tail

/-- Block 021 covers tail-support indices [10525,10550) and q from 17358 to 17398. -/

def TailChunk001Sub000Block021Part000SupportExplicit : Finset ℕ :=
  ([17358] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block021Part000 : ℚ :=
  (9207612673 : ℚ) / 7540705817195520

def SurrogateDiagonalTailChunk001Sub000Block021Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17358
    = surrogateDiagTailX0RatChunk001Sub000Block021Part000

theorem surrogateDiagonalTailChunk001Sub000Block021Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block021Part000CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block021Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block021Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block021Part000CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block021Part000SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block021Part000] using hcert

def TailChunk001Sub000Block021Part001SupportExplicit : Finset ℕ :=
  ([17359] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block021Part001 : ℚ :=
  (4708357515625 : ℚ) / 56749965740120113362

def SurrogateDiagonalTailChunk001Sub000Block021Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17359
    = surrogateDiagTailX0RatChunk001Sub000Block021Part001

theorem surrogateDiagonalTailChunk001Sub000Block021Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block021Part001CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block021Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block021Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block021Part001CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block021Part001SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block021Part001] using hcert

def TailChunk001Sub000Block021Part002SupportExplicit : Finset ℕ :=
  ([17362] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block021Part002 : ℚ :=
  (1883994025 : ℚ) / 5677612533207552

def SurrogateDiagonalTailChunk001Sub000Block021Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17362
    = surrogateDiagTailX0RatChunk001Sub000Block021Part002

theorem surrogateDiagonalTailChunk001Sub000Block021Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block021Part002CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block021Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block021Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block021Part002CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block021Part002SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block021Part002] using hcert

def TailChunk001Sub000Block021Part003SupportExplicit : Finset ℕ :=
  ([17363] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block021Part003 : ℚ :=
  (18334907416075 : ℚ) / 213202258165411872768

def SurrogateDiagonalTailChunk001Sub000Block021Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17363
    = surrogateDiagTailX0RatChunk001Sub000Block021Part003

theorem surrogateDiagonalTailChunk001Sub000Block021Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block021Part003CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block021Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block021Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block021Part003CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block021Part003SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block021Part003] using hcert

def TailChunk001Sub000Block021Part004SupportExplicit : Finset ℕ :=
  ([17365] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block021Part004 : ℚ :=
  (117477815503 : ℚ) / 759141237888000000

def SurrogateDiagonalTailChunk001Sub000Block021Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17365
    = surrogateDiagTailX0RatChunk001Sub000Block021Part004

theorem surrogateDiagonalTailChunk001Sub000Block021Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block021Part004CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block021Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block021Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block021Part004CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block021Part004SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block021Part004] using hcert

def TailChunk001Sub000Block021Part005SupportExplicit : Finset ℕ :=
  ([17366] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block021Part005 : ℚ :=
  (7546817375 : ℚ) / 19703971312501248

def SurrogateDiagonalTailChunk001Sub000Block021Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17366
    = surrogateDiagTailX0RatChunk001Sub000Block021Part005

theorem surrogateDiagonalTailChunk001Sub000Block021Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block021Part005CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block021Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block021Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block021Part005CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block021Part005SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block021Part005] using hcert

def TailChunk001Sub000Block021Part006SupportExplicit : Finset ℕ :=
  ([17367] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block021Part006 : ℚ :=
  (6484982821225 : ℚ) / 24136374312324384768

def SurrogateDiagonalTailChunk001Sub000Block021Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17367
    = surrogateDiagTailX0RatChunk001Sub000Block021Part006

theorem surrogateDiagonalTailChunk001Sub000Block021Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block021Part006CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block021Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block021Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block021Part006CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block021Part006SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block021Part006] using hcert

def TailChunk001Sub000Block021Part007SupportExplicit : Finset ℕ :=
  ([17369] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block021Part007 : ℚ :=
  (39696472879 : ℚ) / 387609901920088200

def SurrogateDiagonalTailChunk001Sub000Block021Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17369
    = surrogateDiagTailX0RatChunk001Sub000Block021Part007

theorem surrogateDiagonalTailChunk001Sub000Block021Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block021Part007CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block021Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block021Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block021Part007CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block021Part007SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block021Part007] using hcert

def TailChunk001Sub000Block021Part008SupportExplicit : Finset ℕ :=
  ([17371] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block021Part008 : ℚ :=
  (8855911213775 : ℚ) / 98272889233066189824

def SurrogateDiagonalTailChunk001Sub000Block021Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17371
    = surrogateDiagTailX0RatChunk001Sub000Block021Part008

theorem surrogateDiagonalTailChunk001Sub000Block021Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block021Part008CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block021Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block021Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block021Part008CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block021Part008SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block021Part008] using hcert

def TailChunk001Sub000Block021Part009SupportExplicit : Finset ℕ :=
  ([17373] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block021Part009 : ℚ :=
  (335265976837 : ℚ) / 1798544086185859200

def SurrogateDiagonalTailChunk001Sub000Block021Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17373
    = surrogateDiagTailX0RatChunk001Sub000Block021Part009

theorem surrogateDiagonalTailChunk001Sub000Block021Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block021Part009CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block021Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block021Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block021Part009CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block021Part009SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block021Part009] using hcert

def TailChunk001Sub000Block021Part010SupportExplicit : Finset ℕ :=
  ([17374] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block021Part010 : ℚ :=
  (1693735111025 : ℚ) / 2853722773870608384

def SurrogateDiagonalTailChunk001Sub000Block021Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17374
    = surrogateDiagTailX0RatChunk001Sub000Block021Part010

theorem surrogateDiagonalTailChunk001Sub000Block021Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block021Part010CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block021Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block021Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block021Part010CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block021Part010SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block021Part010] using hcert

def TailChunk001Sub000Block021Part011SupportExplicit : Finset ℕ :=
  ([17377] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block021Part011 : ℚ :=
  (4718127015625 : ℚ) / 56985727787047452672

def SurrogateDiagonalTailChunk001Sub000Block021Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17377
    = surrogateDiagTailX0RatChunk001Sub000Block021Part011

theorem surrogateDiagonalTailChunk001Sub000Block021Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block021Part011CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block021Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block021Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block021Part011CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block021Part011SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block021Part011] using hcert

def TailChunk001Sub000Block021Part012SupportExplicit : Finset ℕ :=
  ([17378] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block021Part012 : ℚ :=
  (1179667515625 : ℚ) / 3561607986690465792

def SurrogateDiagonalTailChunk001Sub000Block021Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17378
    = surrogateDiagTailX0RatChunk001Sub000Block021Part012

theorem surrogateDiagonalTailChunk001Sub000Block021Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block021Part012CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block021Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block021Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block021Part012CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block021Part012SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block021Part012] using hcert

def TailChunk001Sub000Block021Part013SupportExplicit : Finset ℕ :=
  ([17381] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block021Part013 : ℚ :=
  (2284295027 : ℚ) / 16217260339507200

def SurrogateDiagonalTailChunk001Sub000Block021Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17381
    = surrogateDiagTailX0RatChunk001Sub000Block021Part013

theorem surrogateDiagonalTailChunk001Sub000Block021Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block021Part013CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block021Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block021Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block021Part013CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block021Part013SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block021Part013] using hcert

def TailChunk001Sub000Block021Part014SupportExplicit : Finset ℕ :=
  ([17382] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block021Part014 : ℚ :=
  (1310962102925 : ℚ) / 1407055007087591424

def SurrogateDiagonalTailChunk001Sub000Block021Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17382
    = surrogateDiagTailX0RatChunk001Sub000Block021Part014

theorem surrogateDiagonalTailChunk001Sub000Block021Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block021Part014CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block021Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block021Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block021Part014CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block021Part014SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block021Part014] using hcert

def TailChunk001Sub000Block021Part015SupportExplicit : Finset ℕ :=
  ([17383] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block021Part015 : ℚ :=
  (4721385765625 : ℚ) / 57064478133277564722

def SurrogateDiagonalTailChunk001Sub000Block021Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17383
    = surrogateDiagTailX0RatChunk001Sub000Block021Part015

theorem surrogateDiagonalTailChunk001Sub000Block021Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block021Part015CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block021Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block021Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block021Part015CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block021Part015SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block021Part015] using hcert

def TailChunk001Sub000Block021Part016SupportExplicit : Finset ℕ :=
  ([17385] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block021Part016 : ℚ :=
  (21085294921 : ℚ) / 55736772927160320

def SurrogateDiagonalTailChunk001Sub000Block021Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17385
    = surrogateDiagTailX0RatChunk001Sub000Block021Part016

theorem surrogateDiagonalTailChunk001Sub000Block021Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block021Part016CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block021Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block021Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block021Part016CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block021Part016SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block021Part016] using hcert

def TailChunk001Sub000Block021Part017SupportExplicit : Finset ℕ :=
  ([17386] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block021Part017 : ℚ :=
  (1180753890625 : ℚ) / 3568171648597953312

def SurrogateDiagonalTailChunk001Sub000Block021Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17386
    = surrogateDiagTailX0RatChunk001Sub000Block021Part017

theorem surrogateDiagonalTailChunk001Sub000Block021Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block021Part017CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block021Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block021Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block021Part017CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block021Part017SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block021Part017] using hcert

def TailChunk001Sub000Block021Part018SupportExplicit : Finset ℕ :=
  ([17387] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block021Part018 : ℚ :=
  (4723558890625 : ℚ) / 57117023689773862002

def SurrogateDiagonalTailChunk001Sub000Block021Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17387
    = surrogateDiagTailX0RatChunk001Sub000Block021Part018

theorem surrogateDiagonalTailChunk001Sub000Block021Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block021Part018CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block021Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block021Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block021Part018CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block021Part018SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block021Part018] using hcert

def TailChunk001Sub000Block021Part019SupportExplicit : Finset ℕ :=
  ([17389] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block021Part019 : ℚ :=
  (4724645640625 : ℚ) / 57143310071984008992

def SurrogateDiagonalTailChunk001Sub000Block021Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17389
    = surrogateDiagTailX0RatChunk001Sub000Block021Part019

theorem surrogateDiagonalTailChunk001Sub000Block021Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block021Part019CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block021Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block021Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block021Part019CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block021Part019SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block021Part019] using hcert

def TailChunk001Sub000Block021Part020SupportExplicit : Finset ℕ :=
  ([17390] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block021Part020 : ℚ :=
  (1591189759625 : ℚ) / 2407011461837881344

def SurrogateDiagonalTailChunk001Sub000Block021Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17390
    = surrogateDiagTailX0RatChunk001Sub000Block021Part020

theorem surrogateDiagonalTailChunk001Sub000Block021Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block021Part020CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block021Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block021Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block021Part020CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block021Part020SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block021Part020] using hcert

def TailChunk001Sub000Block021Part021SupportExplicit : Finset ℕ :=
  ([17391] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block021Part021 : ℚ :=
  (249033535879 : ℚ) / 849516429312000000

def SurrogateDiagonalTailChunk001Sub000Block021Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17391
    = surrogateDiagTailX0RatChunk001Sub000Block021Part021

theorem surrogateDiagonalTailChunk001Sub000Block021Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block021Part021CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block021Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block021Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block021Part021CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block021Part021SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block021Part021] using hcert

def TailChunk001Sub000Block021Part022SupportExplicit : Finset ℕ :=
  ([17393] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block021Part022 : ℚ :=
  (4726819515625 : ℚ) / 57195910054762586112

def SurrogateDiagonalTailChunk001Sub000Block021Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17393
    = surrogateDiagTailX0RatChunk001Sub000Block021Part022

theorem surrogateDiagonalTailChunk001Sub000Block021Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block021Part022CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block021Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block021Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block021Part022CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block021Part022SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block021Part022] using hcert

def TailChunk001Sub000Block021Part023SupportExplicit : Finset ℕ :=
  ([17394] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block021Part023 : ℚ :=
  (86763918175 : ℚ) / 74631120031678464

def SurrogateDiagonalTailChunk001Sub000Block021Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17394
    = surrogateDiagTailX0RatChunk001Sub000Block021Part023

theorem surrogateDiagonalTailChunk001Sub000Block021Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block021Part023CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block021Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block021Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block021Part023CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block021Part023SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block021Part023] using hcert

def TailChunk001Sub000Block021Part024SupportExplicit : Finset ℕ :=
  ([17398] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block021Part024 : ℚ :=
  (1182384390625 : ℚ) / 3578034146412545202

def SurrogateDiagonalTailChunk001Sub000Block021Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17398
    = surrogateDiagTailX0RatChunk001Sub000Block021Part024

theorem surrogateDiagonalTailChunk001Sub000Block021Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block021Part024CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block021Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block021Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block021Part024CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block021Part024SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block021Part024] using hcert

def surrogateDiagonalTailChunk001Sub000Block021HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block021Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block021Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block021Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block021Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block021Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block021Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block021Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block021Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block021Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block021Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block021Head : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block021Part000
    + surrogateDiagTailX0RatChunk001Sub000Block021Part001
    + surrogateDiagTailX0RatChunk001Sub000Block021Part002
    + surrogateDiagTailX0RatChunk001Sub000Block021Part003
    + surrogateDiagTailX0RatChunk001Sub000Block021Part004
    + surrogateDiagTailX0RatChunk001Sub000Block021Part005
    + surrogateDiagTailX0RatChunk001Sub000Block021Part006
    + surrogateDiagTailX0RatChunk001Sub000Block021Part007
    + surrogateDiagTailX0RatChunk001Sub000Block021Part008
    + surrogateDiagTailX0RatChunk001Sub000Block021Part009

def surrogateDiagonalTailChunk001Sub000Block021MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block021Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block021Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block021Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block021Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block021Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block021Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block021Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block021Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block021Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block021Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block021Mid : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block021Part010
    + surrogateDiagTailX0RatChunk001Sub000Block021Part011
    + surrogateDiagTailX0RatChunk001Sub000Block021Part012
    + surrogateDiagTailX0RatChunk001Sub000Block021Part013
    + surrogateDiagTailX0RatChunk001Sub000Block021Part014
    + surrogateDiagTailX0RatChunk001Sub000Block021Part015
    + surrogateDiagTailX0RatChunk001Sub000Block021Part016
    + surrogateDiagTailX0RatChunk001Sub000Block021Part017
    + surrogateDiagTailX0RatChunk001Sub000Block021Part018
    + surrogateDiagTailX0RatChunk001Sub000Block021Part019

def surrogateDiagonalTailChunk001Sub000Block021TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block021Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block021Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block021Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block021Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block021Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block021Tail : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block021Part020
    + surrogateDiagTailX0RatChunk001Sub000Block021Part021
    + surrogateDiagTailX0RatChunk001Sub000Block021Part022
    + surrogateDiagTailX0RatChunk001Sub000Block021Part023
    + surrogateDiagTailX0RatChunk001Sub000Block021Part024

def surrogateDiagonalTailChunk001Sub000Block021Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk001Sub000Block021HeadSum X0
    + surrogateDiagonalTailChunk001Sub000Block021MidSum X0
    + surrogateDiagonalTailChunk001Sub000Block021TailSum X0

def surrogateDiagTailX0RatChunk001Sub000Block021 : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block021Part000
    + surrogateDiagTailX0RatChunk001Sub000Block021Part001
    + surrogateDiagTailX0RatChunk001Sub000Block021Part002
    + surrogateDiagTailX0RatChunk001Sub000Block021Part003
    + surrogateDiagTailX0RatChunk001Sub000Block021Part004
    + surrogateDiagTailX0RatChunk001Sub000Block021Part005
    + surrogateDiagTailX0RatChunk001Sub000Block021Part006
    + surrogateDiagTailX0RatChunk001Sub000Block021Part007
    + surrogateDiagTailX0RatChunk001Sub000Block021Part008
    + surrogateDiagTailX0RatChunk001Sub000Block021Part009
    + surrogateDiagTailX0RatChunk001Sub000Block021Part010
    + surrogateDiagTailX0RatChunk001Sub000Block021Part011
    + surrogateDiagTailX0RatChunk001Sub000Block021Part012
    + surrogateDiagTailX0RatChunk001Sub000Block021Part013
    + surrogateDiagTailX0RatChunk001Sub000Block021Part014
    + surrogateDiagTailX0RatChunk001Sub000Block021Part015
    + surrogateDiagTailX0RatChunk001Sub000Block021Part016
    + surrogateDiagTailX0RatChunk001Sub000Block021Part017
    + surrogateDiagTailX0RatChunk001Sub000Block021Part018
    + surrogateDiagTailX0RatChunk001Sub000Block021Part019
    + surrogateDiagTailX0RatChunk001Sub000Block021Part020
    + surrogateDiagTailX0RatChunk001Sub000Block021Part021
    + surrogateDiagTailX0RatChunk001Sub000Block021Part022
    + surrogateDiagTailX0RatChunk001Sub000Block021Part023
    + surrogateDiagTailX0RatChunk001Sub000Block021Part024

theorem surrogateDiagTailX0RatChunk001Sub000Block021_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk001Sub000Block021Head + surrogateDiagTailX0RatChunk001Sub000Block021Mid + surrogateDiagTailX0RatChunk001Sub000Block021Tail =
      surrogateDiagTailX0RatChunk001Sub000Block021 := by
  unfold surrogateDiagTailX0RatChunk001Sub000Block021Head surrogateDiagTailX0RatChunk001Sub000Block021Mid surrogateDiagTailX0RatChunk001Sub000Block021Tail surrogateDiagTailX0RatChunk001Sub000Block021
  ring

def SurrogateDiagonalTailChunk001Sub000Block021HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block021HeadSum X0 = surrogateDiagTailX0RatChunk001Sub000Block021Head

def SurrogateDiagonalTailChunk001Sub000Block021MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block021MidSum X0 = surrogateDiagTailX0RatChunk001Sub000Block021Mid

def SurrogateDiagonalTailChunk001Sub000Block021TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block021TailSum X0 = surrogateDiagTailX0RatChunk001Sub000Block021Tail

theorem surrogateDiagonalTailChunk001Sub000Block021_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk001Sub000Block021HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk001Sub000Block021MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk001Sub000Block021TailCertificateAt X0) :
    surrogateDiagonalTailChunk001Sub000Block021Sum X0 = surrogateDiagTailX0RatChunk001Sub000Block021 := by
  unfold SurrogateDiagonalTailChunk001Sub000Block021HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk001Sub000Block021MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk001Sub000Block021TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk001Sub000Block021Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk001Sub000Block021_eq_head_add_mid_add_tail

/-- Block 022 covers tail-support indices [10550,10575) and q from 17399 to 17439. -/

def TailChunk001Sub000Block022Part000SupportExplicit : Finset ℕ :=
  ([17399] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block022Part000 : ℚ :=
  (2048228516225 : ℚ) / 23956433511167066112

def SurrogateDiagonalTailChunk001Sub000Block022Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17399
    = surrogateDiagTailX0RatChunk001Sub000Block022Part000

theorem surrogateDiagonalTailChunk001Sub000Block022Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block022Part000CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block022Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block022Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block022Part000CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block022Part000SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block022Part000] using hcert

def TailChunk001Sub000Block022Part001SupportExplicit : Finset ℕ :=
  ([17401] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block022Part001 : ℚ :=
  (302794801 : ℚ) / 3667278012940800

def SurrogateDiagonalTailChunk001Sub000Block022Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17401
    = surrogateDiagTailX0RatChunk001Sub000Block022Part001

theorem surrogateDiagonalTailChunk001Sub000Block022Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block022Part001CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block022Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block022Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block022Part001CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block022Part001SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block022Part001] using hcert

def TailChunk001Sub000Block022Part002SupportExplicit : Finset ℕ :=
  ([17402] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block022Part002 : ℚ :=
  (3606550667 : ℚ) / 5665802629939200

def SurrogateDiagonalTailChunk001Sub000Block022Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17402
    = surrogateDiagTailX0RatChunk001Sub000Block022Part002

theorem surrogateDiagonalTailChunk001Sub000Block022Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block022Part002CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block022Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block022Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block022Part002CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block022Part002SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block022Part002] using hcert

def TailChunk001Sub000Block022Part003SupportExplicit : Finset ℕ :=
  ([17403] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block022Part003 : ℚ :=
  (336424976797 : ℚ) / 1811001487872000000

def SurrogateDiagonalTailChunk001Sub000Block022Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17403
    = surrogateDiagTailX0RatChunk001Sub000Block022Part003

theorem surrogateDiagonalTailChunk001Sub000Block022Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block022Part003CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block022Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block022Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block022Part003CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block022Part003SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block022Part003] using hcert

def TailChunk001Sub000Block022Part004SupportExplicit : Finset ℕ :=
  ([17409] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block022Part004 : ℚ :=
  (6516406992025 : ℚ) / 24370991051108548608

def SurrogateDiagonalTailChunk001Sub000Block022Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17409
    = surrogateDiagTailX0RatChunk001Sub000Block022Part004

theorem surrogateDiagonalTailChunk001Sub000Block022Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block022Part004CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block022Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block022Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block022Part004CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block022Part004SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block022Part004] using hcert

def TailChunk001Sub000Block022Part005SupportExplicit : Finset ℕ :=
  ([17410] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block022Part005 : ℚ :=
  (136313205157 : ℚ) / 234705792828211200

def SurrogateDiagonalTailChunk001Sub000Block022Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17410
    = surrogateDiagTailX0RatChunk001Sub000Block022Part005

theorem surrogateDiagonalTailChunk001Sub000Block022Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block022Part005CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block022Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block022Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block022Part005CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block022Part005SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block022Part005] using hcert

def TailChunk001Sub000Block022Part006SupportExplicit : Finset ℕ :=
  ([17411] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block022Part006 : ℚ :=
  (17511787863475 : ℚ) / 191339557023062181888

def SurrogateDiagonalTailChunk001Sub000Block022Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17411
    = surrogateDiagTailX0RatChunk001Sub000Block022Part006

theorem surrogateDiagonalTailChunk001Sub000Block022Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block022Part006CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block022Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block022Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block022Part006CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block022Part006SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block022Part006] using hcert

def TailChunk001Sub000Block022Part007SupportExplicit : Finset ℕ :=
  ([17413] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block022Part007 : ℚ :=
  (644643852793 : ℚ) / 6264880145660035200

def SurrogateDiagonalTailChunk001Sub000Block022Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17413
    = surrogateDiagTailX0RatChunk001Sub000Block022Part007

theorem surrogateDiagonalTailChunk001Sub000Block022Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block022Part007CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block022Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block022Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block022Part007CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block022Part007SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block022Part007] using hcert

def TailChunk001Sub000Block022Part008SupportExplicit : Finset ℕ :=
  ([17414] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block022Part008 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block022Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17414
    = surrogateDiagTailX0RatChunk001Sub000Block022Part008

theorem surrogateDiagonalTailChunk001Sub000Block022Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block022Part008CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block022Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block022Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block022Part008CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block022Part008SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block022Part008] using hcert

def TailChunk001Sub000Block022Part009SupportExplicit : Finset ℕ :=
  ([17417] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block022Part009 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block022Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17417
    = surrogateDiagTailX0RatChunk001Sub000Block022Part009

theorem surrogateDiagonalTailChunk001Sub000Block022Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block022Part009CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block022Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block022Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block022Part009CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block022Part009SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block022Part009] using hcert

def TailChunk001Sub000Block022Part010SupportExplicit : Finset ℕ :=
  ([17418] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block022Part010 : ℚ :=
  (263487682475 : ℚ) / 1418751972312051264

def SurrogateDiagonalTailChunk001Sub000Block022Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17418
    = surrogateDiagTailX0RatChunk001Sub000Block022Part010

theorem surrogateDiagonalTailChunk001Sub000Block022Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block022Part010CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block022Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block022Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block022Part010CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block022Part010SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block022Part010] using hcert

def TailChunk001Sub000Block022Part011SupportExplicit : Finset ℕ :=
  ([17419] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block022Part011 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block022Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17419
    = surrogateDiagTailX0RatChunk001Sub000Block022Part011

theorem surrogateDiagonalTailChunk001Sub000Block022Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block022Part011CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block022Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block022Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block022Part011CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block022Part011SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block022Part011] using hcert

def TailChunk001Sub000Block022Part012SupportExplicit : Finset ℕ :=
  ([17421] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block022Part012 : ℚ :=
  (125025 : ℚ) / 9090716474019968

def SurrogateDiagonalTailChunk001Sub000Block022Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17421
    = surrogateDiagTailX0RatChunk001Sub000Block022Part012

theorem surrogateDiagonalTailChunk001Sub000Block022Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block022Part012CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block022Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block022Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block022Part012CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block022Part012SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block022Part012] using hcert

def TailChunk001Sub000Block022Part013SupportExplicit : Finset ℕ :=
  ([17422] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block022Part013 : ℚ :=
  (3890344309 : ℚ) / 497970934272000000

def SurrogateDiagonalTailChunk001Sub000Block022Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17422
    = surrogateDiagTailX0RatChunk001Sub000Block022Part013

theorem surrogateDiagonalTailChunk001Sub000Block022Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block022Part013CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block022Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block022Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block022Part013CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block022Part013SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block022Part013] using hcert

def TailChunk001Sub000Block022Part014SupportExplicit : Finset ℕ :=
  ([17423] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block022Part014 : ℚ :=
  (964641299 : ℚ) / 99653068132300800

def SurrogateDiagonalTailChunk001Sub000Block022Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17423
    = surrogateDiagTailX0RatChunk001Sub000Block022Part014

theorem surrogateDiagonalTailChunk001Sub000Block022Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block022Part014CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block022Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block022Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block022Part014CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block022Part014SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block022Part014] using hcert

def TailChunk001Sub000Block022Part015SupportExplicit : Finset ℕ :=
  ([17426] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block022Part015 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block022Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17426
    = surrogateDiagTailX0RatChunk001Sub000Block022Part015

theorem surrogateDiagonalTailChunk001Sub000Block022Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block022Part015CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block022Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block022Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block022Part015CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block022Part015SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block022Part015] using hcert

def TailChunk001Sub000Block022Part016SupportExplicit : Finset ℕ :=
  ([17427] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block022Part016 : ℚ :=
  (121363147225 : ℚ) / 39797449289315647488

def SurrogateDiagonalTailChunk001Sub000Block022Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17427
    = surrogateDiagTailX0RatChunk001Sub000Block022Part016

theorem surrogateDiagonalTailChunk001Sub000Block022Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block022Part016CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block022Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block022Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block022Part016CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block022Part016SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block022Part016] using hcert

def TailChunk001Sub000Block022Part017SupportExplicit : Finset ℕ :=
  ([17429] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block022Part017 : ℚ :=
  (602592959 : ℚ) / 569109639168000000

def SurrogateDiagonalTailChunk001Sub000Block022Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17429
    = surrogateDiagTailX0RatChunk001Sub000Block022Part017

theorem surrogateDiagonalTailChunk001Sub000Block022Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block022Part017CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block022Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block022Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block022Part017CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block022Part017SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block022Part017] using hcert

def TailChunk001Sub000Block022Part018SupportExplicit : Finset ℕ :=
  ([17430] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block022Part018 : ℚ :=
  (702079253275 : ℚ) / 600132598702276608

def SurrogateDiagonalTailChunk001Sub000Block022Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17430
    = surrogateDiagTailX0RatChunk001Sub000Block022Part018

theorem surrogateDiagonalTailChunk001Sub000Block022Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block022Part018CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block022Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block022Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block022Part018CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block022Part018SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block022Part018] using hcert

def TailChunk001Sub000Block022Part019SupportExplicit : Finset ℕ :=
  ([17431] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block022Part019 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block022Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17431
    = surrogateDiagTailX0RatChunk001Sub000Block022Part019

theorem surrogateDiagonalTailChunk001Sub000Block022Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block022Part019CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block022Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block022Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block022Part019CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block022Part019SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block022Part019] using hcert

def TailChunk001Sub000Block022Part020SupportExplicit : Finset ℕ :=
  ([17434] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block022Part020 : ℚ :=
  (40892689175 : ℚ) / 3986240771313795456

def SurrogateDiagonalTailChunk001Sub000Block022Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17434
    = surrogateDiagTailX0RatChunk001Sub000Block022Part020

theorem surrogateDiagonalTailChunk001Sub000Block022Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block022Part020CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block022Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block022Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block022Part020CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block022Part020SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block022Part020] using hcert

def TailChunk001Sub000Block022Part021SupportExplicit : Finset ℕ :=
  ([17435] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block022Part021 : ℚ :=
  (31598099 : ℚ) / 1994642996029440

def SurrogateDiagonalTailChunk001Sub000Block022Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17435
    = surrogateDiagTailX0RatChunk001Sub000Block022Part021

theorem surrogateDiagonalTailChunk001Sub000Block022Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block022Part021CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block022Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block022Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block022Part021CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block022Part021SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block022Part021] using hcert

def TailChunk001Sub000Block022Part022SupportExplicit : Finset ℕ :=
  ([17437] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block022Part022 : ℚ :=
  (49920767425 : ℚ) / 5893917555002720256

def SurrogateDiagonalTailChunk001Sub000Block022Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17437
    = surrogateDiagTailX0RatChunk001Sub000Block022Part022

theorem surrogateDiagonalTailChunk001Sub000Block022Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block022Part022CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block022Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block022Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block022Part022CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block022Part022SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block022Part022] using hcert

def TailChunk001Sub000Block022Part023SupportExplicit : Finset ℕ :=
  ([17438] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block022Part023 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block022Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17438
    = surrogateDiagTailX0RatChunk001Sub000Block022Part023

theorem surrogateDiagonalTailChunk001Sub000Block022Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block022Part023CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block022Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block022Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block022Part023CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block022Part023SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block022Part023] using hcert

def TailChunk001Sub000Block022Part024SupportExplicit : Finset ℕ :=
  ([17439] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block022Part024 : ℚ :=
  (125025 : ℚ) / 9128352648562688

def SurrogateDiagonalTailChunk001Sub000Block022Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17439
    = surrogateDiagTailX0RatChunk001Sub000Block022Part024

theorem surrogateDiagonalTailChunk001Sub000Block022Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block022Part024CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block022Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block022Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block022Part024CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block022Part024SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block022Part024] using hcert

def surrogateDiagonalTailChunk001Sub000Block022HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block022Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block022Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block022Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block022Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block022Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block022Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block022Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block022Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block022Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block022Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block022Head : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block022Part000
    + surrogateDiagTailX0RatChunk001Sub000Block022Part001
    + surrogateDiagTailX0RatChunk001Sub000Block022Part002
    + surrogateDiagTailX0RatChunk001Sub000Block022Part003
    + surrogateDiagTailX0RatChunk001Sub000Block022Part004
    + surrogateDiagTailX0RatChunk001Sub000Block022Part005
    + surrogateDiagTailX0RatChunk001Sub000Block022Part006
    + surrogateDiagTailX0RatChunk001Sub000Block022Part007
    + surrogateDiagTailX0RatChunk001Sub000Block022Part008
    + surrogateDiagTailX0RatChunk001Sub000Block022Part009

def surrogateDiagonalTailChunk001Sub000Block022MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block022Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block022Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block022Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block022Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block022Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block022Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block022Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block022Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block022Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block022Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block022Mid : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block022Part010
    + surrogateDiagTailX0RatChunk001Sub000Block022Part011
    + surrogateDiagTailX0RatChunk001Sub000Block022Part012
    + surrogateDiagTailX0RatChunk001Sub000Block022Part013
    + surrogateDiagTailX0RatChunk001Sub000Block022Part014
    + surrogateDiagTailX0RatChunk001Sub000Block022Part015
    + surrogateDiagTailX0RatChunk001Sub000Block022Part016
    + surrogateDiagTailX0RatChunk001Sub000Block022Part017
    + surrogateDiagTailX0RatChunk001Sub000Block022Part018
    + surrogateDiagTailX0RatChunk001Sub000Block022Part019

def surrogateDiagonalTailChunk001Sub000Block022TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block022Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block022Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block022Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block022Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block022Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block022Tail : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block022Part020
    + surrogateDiagTailX0RatChunk001Sub000Block022Part021
    + surrogateDiagTailX0RatChunk001Sub000Block022Part022
    + surrogateDiagTailX0RatChunk001Sub000Block022Part023
    + surrogateDiagTailX0RatChunk001Sub000Block022Part024

def surrogateDiagonalTailChunk001Sub000Block022Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk001Sub000Block022HeadSum X0
    + surrogateDiagonalTailChunk001Sub000Block022MidSum X0
    + surrogateDiagonalTailChunk001Sub000Block022TailSum X0

def surrogateDiagTailX0RatChunk001Sub000Block022 : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block022Part000
    + surrogateDiagTailX0RatChunk001Sub000Block022Part001
    + surrogateDiagTailX0RatChunk001Sub000Block022Part002
    + surrogateDiagTailX0RatChunk001Sub000Block022Part003
    + surrogateDiagTailX0RatChunk001Sub000Block022Part004
    + surrogateDiagTailX0RatChunk001Sub000Block022Part005
    + surrogateDiagTailX0RatChunk001Sub000Block022Part006
    + surrogateDiagTailX0RatChunk001Sub000Block022Part007
    + surrogateDiagTailX0RatChunk001Sub000Block022Part008
    + surrogateDiagTailX0RatChunk001Sub000Block022Part009
    + surrogateDiagTailX0RatChunk001Sub000Block022Part010
    + surrogateDiagTailX0RatChunk001Sub000Block022Part011
    + surrogateDiagTailX0RatChunk001Sub000Block022Part012
    + surrogateDiagTailX0RatChunk001Sub000Block022Part013
    + surrogateDiagTailX0RatChunk001Sub000Block022Part014
    + surrogateDiagTailX0RatChunk001Sub000Block022Part015
    + surrogateDiagTailX0RatChunk001Sub000Block022Part016
    + surrogateDiagTailX0RatChunk001Sub000Block022Part017
    + surrogateDiagTailX0RatChunk001Sub000Block022Part018
    + surrogateDiagTailX0RatChunk001Sub000Block022Part019
    + surrogateDiagTailX0RatChunk001Sub000Block022Part020
    + surrogateDiagTailX0RatChunk001Sub000Block022Part021
    + surrogateDiagTailX0RatChunk001Sub000Block022Part022
    + surrogateDiagTailX0RatChunk001Sub000Block022Part023
    + surrogateDiagTailX0RatChunk001Sub000Block022Part024

theorem surrogateDiagTailX0RatChunk001Sub000Block022_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk001Sub000Block022Head + surrogateDiagTailX0RatChunk001Sub000Block022Mid + surrogateDiagTailX0RatChunk001Sub000Block022Tail =
      surrogateDiagTailX0RatChunk001Sub000Block022 := by
  unfold surrogateDiagTailX0RatChunk001Sub000Block022Head surrogateDiagTailX0RatChunk001Sub000Block022Mid surrogateDiagTailX0RatChunk001Sub000Block022Tail surrogateDiagTailX0RatChunk001Sub000Block022
  ring

def SurrogateDiagonalTailChunk001Sub000Block022HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block022HeadSum X0 = surrogateDiagTailX0RatChunk001Sub000Block022Head

def SurrogateDiagonalTailChunk001Sub000Block022MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block022MidSum X0 = surrogateDiagTailX0RatChunk001Sub000Block022Mid

def SurrogateDiagonalTailChunk001Sub000Block022TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block022TailSum X0 = surrogateDiagTailX0RatChunk001Sub000Block022Tail

theorem surrogateDiagonalTailChunk001Sub000Block022_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk001Sub000Block022HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk001Sub000Block022MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk001Sub000Block022TailCertificateAt X0) :
    surrogateDiagonalTailChunk001Sub000Block022Sum X0 = surrogateDiagTailX0RatChunk001Sub000Block022 := by
  unfold SurrogateDiagonalTailChunk001Sub000Block022HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk001Sub000Block022MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk001Sub000Block022TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk001Sub000Block022Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk001Sub000Block022_eq_head_add_mid_add_tail

/-- Block 023 covers tail-support indices [10575,10600) and q from 17441 to 17482. -/

def TailChunk001Sub000Block023Part000SupportExplicit : Finset ℕ :=
  ([17441] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block023Part000 : ℚ :=
  (83855312725 : ℚ) / 217425450258965478528

def SurrogateDiagonalTailChunk001Sub000Block023Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17441
    = surrogateDiagTailX0RatChunk001Sub000Block023Part000

theorem surrogateDiagonalTailChunk001Sub000Block023Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block023Part000CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block023Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block023Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block023Part000CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block023Part000SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block023Part000] using hcert

def TailChunk001Sub000Block023Part001SupportExplicit : Finset ℕ :=
  ([17443] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block023Part001 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block023Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17443
    = surrogateDiagTailX0RatChunk001Sub000Block023Part001

theorem surrogateDiagonalTailChunk001Sub000Block023Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block023Part001CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block023Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block023Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block023Part001CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block023Part001SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block023Part001] using hcert

def TailChunk001Sub000Block023Part002SupportExplicit : Finset ℕ :=
  ([17445] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block023Part002 : ℚ :=
  (1943711839375 : ℚ) / 18672880550992969728

def SurrogateDiagonalTailChunk001Sub000Block023Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17445
    = surrogateDiagTailX0RatChunk001Sub000Block023Part002

theorem surrogateDiagonalTailChunk001Sub000Block023Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block023Part002CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block023Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block023Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block023Part002CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block023Part002SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block023Part002] using hcert

def TailChunk001Sub000Block023Part003SupportExplicit : Finset ℕ :=
  ([17446] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block023Part003 : ℚ :=
  (5395916527 : ℚ) / 89597435904000000

def SurrogateDiagonalTailChunk001Sub000Block023Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17446
    = surrogateDiagTailX0RatChunk001Sub000Block023Part003

theorem surrogateDiagonalTailChunk001Sub000Block023Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block023Part003CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block023Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block023Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block023Part003CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block023Part003SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block023Part003] using hcert

def TailChunk001Sub000Block023Part004SupportExplicit : Finset ℕ :=
  ([17447] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block023Part004 : ℚ :=
  (455301425 : ℚ) / 1056901478433841152

def SurrogateDiagonalTailChunk001Sub000Block023Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17447
    = surrogateDiagTailX0RatChunk001Sub000Block023Part004

theorem surrogateDiagonalTailChunk001Sub000Block023Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block023Part004CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block023Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block023Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block023Part004CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block023Part004SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block023Part004] using hcert

def TailChunk001Sub000Block023Part005SupportExplicit : Finset ℕ :=
  ([17449] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block023Part005 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block023Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17449
    = surrogateDiagTailX0RatChunk001Sub000Block023Part005

theorem surrogateDiagonalTailChunk001Sub000Block023Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block023Part005CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block023Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block023Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block023Part005CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block023Part005SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block023Part005] using hcert

def TailChunk001Sub000Block023Part006SupportExplicit : Finset ℕ :=
  ([17453] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block023Part006 : ℚ :=
  (139217713 : ℚ) / 168374335200413400

def SurrogateDiagonalTailChunk001Sub000Block023Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17453
    = surrogateDiagTailX0RatChunk001Sub000Block023Part006

theorem surrogateDiagonalTailChunk001Sub000Block023Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block023Part006CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block023Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block023Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block023Part006CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block023Part006SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block023Part006] using hcert

def TailChunk001Sub000Block023Part007SupportExplicit : Finset ℕ :=
  ([17454] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block023Part007 : ℚ :=
  (528735711275 : ℚ) / 1430521714799453184

def SurrogateDiagonalTailChunk001Sub000Block023Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17454
    = surrogateDiagTailX0RatChunk001Sub000Block023Part007

theorem surrogateDiagonalTailChunk001Sub000Block023Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block023Part007CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block023Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block023Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block023Part007CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block023Part007SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block023Part007] using hcert

def TailChunk001Sub000Block023Part008SupportExplicit : Finset ℕ :=
  ([17455] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block023Part008 : ℚ :=
  (2033352003 : ℚ) / 253242891907758080

def SurrogateDiagonalTailChunk001Sub000Block023Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17455
    = surrogateDiagTailX0RatChunk001Sub000Block023Part008

theorem surrogateDiagonalTailChunk001Sub000Block023Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block023Part008CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block023Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block023Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block023Part008CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block023Part008SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block023Part008] using hcert

def TailChunk001Sub000Block023Part009SupportExplicit : Finset ℕ :=
  ([17458] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block023Part009 : ℚ :=
  (470926150675 : ℚ) / 6198136657161781248

def SurrogateDiagonalTailChunk001Sub000Block023Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17458
    = surrogateDiagTailX0RatChunk001Sub000Block023Part009

theorem surrogateDiagonalTailChunk001Sub000Block023Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block023Part009CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block023Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block023Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block023Part009CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block023Part009SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block023Part009] using hcert

def TailChunk001Sub000Block023Part010SupportExplicit : Finset ℕ :=
  ([17459] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block023Part010 : ℚ :=
  (744190032925 : ℚ) / 125779592815614885888

def SurrogateDiagonalTailChunk001Sub000Block023Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17459
    = surrogateDiagTailX0RatChunk001Sub000Block023Part010

theorem surrogateDiagonalTailChunk001Sub000Block023Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block023Part010CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block023Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block023Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block023Part010CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block023Part010SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block023Part010] using hcert

def TailChunk001Sub000Block023Part011SupportExplicit : Finset ℕ :=
  ([17461] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block023Part011 : ℚ :=
  (134381570525 : ℚ) / 93208948447971898944

def SurrogateDiagonalTailChunk001Sub000Block023Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17461
    = surrogateDiagTailX0RatChunk001Sub000Block023Part011

theorem surrogateDiagonalTailChunk001Sub000Block023Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block023Part011CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block023Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block023Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block023Part011CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block023Part011SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block023Part011] using hcert

def TailChunk001Sub000Block023Part012SupportExplicit : Finset ℕ :=
  ([17462] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block023Part012 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block023Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17462
    = surrogateDiagTailX0RatChunk001Sub000Block023Part012

theorem surrogateDiagonalTailChunk001Sub000Block023Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block023Part012CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block023Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block023Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block023Part012CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block023Part012SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block023Part012] using hcert

def TailChunk001Sub000Block023Part013SupportExplicit : Finset ℕ :=
  ([17463] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block023Part013 : ℚ :=
  (1058825021 : ℚ) / 22951378993127040

def SurrogateDiagonalTailChunk001Sub000Block023Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17463
    = surrogateDiagTailX0RatChunk001Sub000Block023Part013

theorem surrogateDiagonalTailChunk001Sub000Block023Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block023Part013CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block023Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block023Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block023Part013CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block023Part013SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block023Part013] using hcert

def TailChunk001Sub000Block023Part014SupportExplicit : Finset ℕ :=
  ([17465] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block023Part014 : ℚ :=
  (1170100353625 : ℚ) / 51025726486907486208

def SurrogateDiagonalTailChunk001Sub000Block023Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17465
    = surrogateDiagTailX0RatChunk001Sub000Block023Part014

theorem surrogateDiagonalTailChunk001Sub000Block023Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block023Part014CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block023Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block023Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block023Part014CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block023Part014SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block023Part014] using hcert

def TailChunk001Sub000Block023Part015SupportExplicit : Finset ℕ :=
  ([17466] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block023Part015 : ℚ :=
  (41854611181 : ℚ) / 98364628992000000

def SurrogateDiagonalTailChunk001Sub000Block023Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17466
    = surrogateDiagTailX0RatChunk001Sub000Block023Part015

theorem surrogateDiagonalTailChunk001Sub000Block023Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block023Part015CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block023Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block023Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block023Part015CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block023Part015SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block023Part015] using hcert

def TailChunk001Sub000Block023Part016SupportExplicit : Finset ℕ :=
  ([17467] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block023Part016 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block023Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17467
    = surrogateDiagTailX0RatChunk001Sub000Block023Part016

theorem surrogateDiagonalTailChunk001Sub000Block023Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block023Part016CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block023Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block023Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block023Part016CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block023Part016SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block023Part016] using hcert

def TailChunk001Sub000Block023Part017SupportExplicit : Finset ℕ :=
  ([17470] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block023Part017 : ℚ :=
  (143154564175 : ℚ) / 1487249358754632192

def SurrogateDiagonalTailChunk001Sub000Block023Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17470
    = surrogateDiagTailX0RatChunk001Sub000Block023Part017

theorem surrogateDiagonalTailChunk001Sub000Block023Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block023Part017CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block023Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block023Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block023Part017CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block023Part017SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block023Part017] using hcert

def TailChunk001Sub000Block023Part018SupportExplicit : Finset ℕ :=
  ([17471] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block023Part018 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block023Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17471
    = surrogateDiagTailX0RatChunk001Sub000Block023Part018

theorem surrogateDiagonalTailChunk001Sub000Block023Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block023Part018CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block023Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block023Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block023Part018CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block023Part018SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block023Part018] using hcert

def TailChunk001Sub000Block023Part019SupportExplicit : Finset ℕ :=
  ([17473] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block023Part019 : ℚ :=
  (3394994251 : ℚ) / 8753880986112000000

def SurrogateDiagonalTailChunk001Sub000Block023Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17473
    = surrogateDiagTailX0RatChunk001Sub000Block023Part019

theorem surrogateDiagonalTailChunk001Sub000Block023Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block023Part019CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block023Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block023Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block023Part019CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block023Part019SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block023Part019] using hcert

def TailChunk001Sub000Block023Part020SupportExplicit : Finset ℕ :=
  ([17474] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block023Part020 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block023Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17474
    = surrogateDiagTailX0RatChunk001Sub000Block023Part020

theorem surrogateDiagonalTailChunk001Sub000Block023Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block023Part020CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block023Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block023Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block023Part020CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block023Part020SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block023Part020] using hcert

def TailChunk001Sub000Block023Part021SupportExplicit : Finset ℕ :=
  ([17477] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block023Part021 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block023Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17477
    = surrogateDiagTailX0RatChunk001Sub000Block023Part021

theorem surrogateDiagonalTailChunk001Sub000Block023Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block023Part021CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block023Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block023Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block023Part021CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block023Part021SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block023Part021] using hcert

def TailChunk001Sub000Block023Part022SupportExplicit : Finset ℕ :=
  ([17479] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block023Part022 : ℚ :=
  (586752269 : ℚ) / 46967031495993600

def SurrogateDiagonalTailChunk001Sub000Block023Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17479
    = surrogateDiagTailX0RatChunk001Sub000Block023Part022

theorem surrogateDiagonalTailChunk001Sub000Block023Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block023Part022CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block023Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block023Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block023Part022CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block023Part022SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block023Part022] using hcert

def TailChunk001Sub000Block023Part023SupportExplicit : Finset ℕ :=
  ([17481] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block023Part023 : ℚ :=
  (1061008645925 : ℚ) / 23046170313603760704

def SurrogateDiagonalTailChunk001Sub000Block023Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17481
    = surrogateDiagTailX0RatChunk001Sub000Block023Part023

theorem surrogateDiagonalTailChunk001Sub000Block023Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block023Part023CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block023Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block023Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block023Part023CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block023Part023SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block023Part023] using hcert

def TailChunk001Sub000Block023Part024SupportExplicit : Finset ℕ :=
  ([17482] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block023Part024 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block023Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17482
    = surrogateDiagTailX0RatChunk001Sub000Block023Part024

theorem surrogateDiagonalTailChunk001Sub000Block023Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block023Part024CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block023Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block023Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block023Part024CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block023Part024SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block023Part024] using hcert

def surrogateDiagonalTailChunk001Sub000Block023HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block023Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block023Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block023Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block023Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block023Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block023Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block023Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block023Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block023Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block023Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block023Head : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block023Part000
    + surrogateDiagTailX0RatChunk001Sub000Block023Part001
    + surrogateDiagTailX0RatChunk001Sub000Block023Part002
    + surrogateDiagTailX0RatChunk001Sub000Block023Part003
    + surrogateDiagTailX0RatChunk001Sub000Block023Part004
    + surrogateDiagTailX0RatChunk001Sub000Block023Part005
    + surrogateDiagTailX0RatChunk001Sub000Block023Part006
    + surrogateDiagTailX0RatChunk001Sub000Block023Part007
    + surrogateDiagTailX0RatChunk001Sub000Block023Part008
    + surrogateDiagTailX0RatChunk001Sub000Block023Part009

def surrogateDiagonalTailChunk001Sub000Block023MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block023Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block023Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block023Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block023Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block023Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block023Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block023Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block023Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block023Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block023Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block023Mid : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block023Part010
    + surrogateDiagTailX0RatChunk001Sub000Block023Part011
    + surrogateDiagTailX0RatChunk001Sub000Block023Part012
    + surrogateDiagTailX0RatChunk001Sub000Block023Part013
    + surrogateDiagTailX0RatChunk001Sub000Block023Part014
    + surrogateDiagTailX0RatChunk001Sub000Block023Part015
    + surrogateDiagTailX0RatChunk001Sub000Block023Part016
    + surrogateDiagTailX0RatChunk001Sub000Block023Part017
    + surrogateDiagTailX0RatChunk001Sub000Block023Part018
    + surrogateDiagTailX0RatChunk001Sub000Block023Part019

def surrogateDiagonalTailChunk001Sub000Block023TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block023Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block023Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block023Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block023Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block023Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block023Tail : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block023Part020
    + surrogateDiagTailX0RatChunk001Sub000Block023Part021
    + surrogateDiagTailX0RatChunk001Sub000Block023Part022
    + surrogateDiagTailX0RatChunk001Sub000Block023Part023
    + surrogateDiagTailX0RatChunk001Sub000Block023Part024

def surrogateDiagonalTailChunk001Sub000Block023Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk001Sub000Block023HeadSum X0
    + surrogateDiagonalTailChunk001Sub000Block023MidSum X0
    + surrogateDiagonalTailChunk001Sub000Block023TailSum X0

def surrogateDiagTailX0RatChunk001Sub000Block023 : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block023Part000
    + surrogateDiagTailX0RatChunk001Sub000Block023Part001
    + surrogateDiagTailX0RatChunk001Sub000Block023Part002
    + surrogateDiagTailX0RatChunk001Sub000Block023Part003
    + surrogateDiagTailX0RatChunk001Sub000Block023Part004
    + surrogateDiagTailX0RatChunk001Sub000Block023Part005
    + surrogateDiagTailX0RatChunk001Sub000Block023Part006
    + surrogateDiagTailX0RatChunk001Sub000Block023Part007
    + surrogateDiagTailX0RatChunk001Sub000Block023Part008
    + surrogateDiagTailX0RatChunk001Sub000Block023Part009
    + surrogateDiagTailX0RatChunk001Sub000Block023Part010
    + surrogateDiagTailX0RatChunk001Sub000Block023Part011
    + surrogateDiagTailX0RatChunk001Sub000Block023Part012
    + surrogateDiagTailX0RatChunk001Sub000Block023Part013
    + surrogateDiagTailX0RatChunk001Sub000Block023Part014
    + surrogateDiagTailX0RatChunk001Sub000Block023Part015
    + surrogateDiagTailX0RatChunk001Sub000Block023Part016
    + surrogateDiagTailX0RatChunk001Sub000Block023Part017
    + surrogateDiagTailX0RatChunk001Sub000Block023Part018
    + surrogateDiagTailX0RatChunk001Sub000Block023Part019
    + surrogateDiagTailX0RatChunk001Sub000Block023Part020
    + surrogateDiagTailX0RatChunk001Sub000Block023Part021
    + surrogateDiagTailX0RatChunk001Sub000Block023Part022
    + surrogateDiagTailX0RatChunk001Sub000Block023Part023
    + surrogateDiagTailX0RatChunk001Sub000Block023Part024

theorem surrogateDiagTailX0RatChunk001Sub000Block023_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk001Sub000Block023Head + surrogateDiagTailX0RatChunk001Sub000Block023Mid + surrogateDiagTailX0RatChunk001Sub000Block023Tail =
      surrogateDiagTailX0RatChunk001Sub000Block023 := by
  unfold surrogateDiagTailX0RatChunk001Sub000Block023Head surrogateDiagTailX0RatChunk001Sub000Block023Mid surrogateDiagTailX0RatChunk001Sub000Block023Tail surrogateDiagTailX0RatChunk001Sub000Block023
  ring

def SurrogateDiagonalTailChunk001Sub000Block023HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block023HeadSum X0 = surrogateDiagTailX0RatChunk001Sub000Block023Head

def SurrogateDiagonalTailChunk001Sub000Block023MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block023MidSum X0 = surrogateDiagTailX0RatChunk001Sub000Block023Mid

def SurrogateDiagonalTailChunk001Sub000Block023TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block023TailSum X0 = surrogateDiagTailX0RatChunk001Sub000Block023Tail

theorem surrogateDiagonalTailChunk001Sub000Block023_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk001Sub000Block023HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk001Sub000Block023MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk001Sub000Block023TailCertificateAt X0) :
    surrogateDiagonalTailChunk001Sub000Block023Sum X0 = surrogateDiagTailX0RatChunk001Sub000Block023 := by
  unfold SurrogateDiagonalTailChunk001Sub000Block023HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk001Sub000Block023MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk001Sub000Block023TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk001Sub000Block023Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk001Sub000Block023_eq_head_add_mid_add_tail

/-- Block 024 covers tail-support indices [10600,10625) and q from 17483 to 17521. -/

def TailChunk001Sub000Block024Part000SupportExplicit : Finset ℕ :=
  ([17483] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block024Part000 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block024Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17483
    = surrogateDiagTailX0RatChunk001Sub000Block024Part000

theorem surrogateDiagonalTailChunk001Sub000Block024Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block024Part000CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block024Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block024Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block024Part000CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block024Part000SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block024Part000] using hcert

def TailChunk001Sub000Block024Part001SupportExplicit : Finset ℕ :=
  ([17485] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block024Part001 : ℚ :=
  (1653148969375 : ℚ) / 68474833434216235008

def SurrogateDiagonalTailChunk001Sub000Block024Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17485
    = surrogateDiagTailX0RatChunk001Sub000Block024Part001

theorem surrogateDiagonalTailChunk001Sub000Block024Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block024Part001CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block024Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block024Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block024Part001CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block024Part001SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block024Part001] using hcert

def TailChunk001Sub000Block024Part002SupportExplicit : Finset ℕ :=
  ([17486] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block024Part002 : ℚ :=
  (391016811925 : ℚ) / 7861224550975930368

def SurrogateDiagonalTailChunk001Sub000Block024Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17486
    = surrogateDiagTailX0RatChunk001Sub000Block024Part002

theorem surrogateDiagonalTailChunk001Sub000Block024Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block024Part002CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block024Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block024Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block024Part002CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block024Part002SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block024Part002] using hcert

def TailChunk001Sub000Block024Part003SupportExplicit : Finset ℕ :=
  ([17489] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block024Part003 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block024Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17489
    = surrogateDiagTailX0RatChunk001Sub000Block024Part003

theorem surrogateDiagonalTailChunk001Sub000Block024Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block024Part003CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block024Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block024Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block024Part003CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block024Part003SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block024Part003] using hcert

def TailChunk001Sub000Block024Part004SupportExplicit : Finset ℕ :=
  ([17490] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block024Part004 : ℚ :=
  (9610603963 : ℚ) / 7488592202956800

def SurrogateDiagonalTailChunk001Sub000Block024Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17490
    = surrogateDiagTailX0RatChunk001Sub000Block024Part004

theorem surrogateDiagonalTailChunk001Sub000Block024Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block024Part004CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block024Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block024Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block024Part004CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block024Part004SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block024Part004] using hcert

def TailChunk001Sub000Block024Part005SupportExplicit : Finset ℕ :=
  ([17491] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block024Part005 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block024Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17491
    = surrogateDiagTailX0RatChunk001Sub000Block024Part005

theorem surrogateDiagonalTailChunk001Sub000Block024Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block024Part005CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block024Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block024Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block024Part005CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block024Part005SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block024Part005] using hcert

def TailChunk001Sub000Block024Part006SupportExplicit : Finset ℕ :=
  ([17494] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block024Part006 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block024Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17494
    = surrogateDiagTailX0RatChunk001Sub000Block024Part006

theorem surrogateDiagonalTailChunk001Sub000Block024Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block024Part006CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block024Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block024Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block024Part006CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block024Part006SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block024Part006] using hcert

def TailChunk001Sub000Block024Part007SupportExplicit : Finset ℕ :=
  ([17495] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block024Part007 : ℚ :=
  (510148225075 : ℚ) / 31946610740649302016

def SurrogateDiagonalTailChunk001Sub000Block024Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17495
    = surrogateDiagTailX0RatChunk001Sub000Block024Part007

theorem surrogateDiagonalTailChunk001Sub000Block024Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block024Part007CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block024Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block024Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block024Part007CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block024Part007SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block024Part007] using hcert

def TailChunk001Sub000Block024Part008SupportExplicit : Finset ℕ :=
  ([17497] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block024Part008 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block024Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17497
    = surrogateDiagTailX0RatChunk001Sub000Block024Part008

theorem surrogateDiagonalTailChunk001Sub000Block024Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block024Part008CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block024Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block024Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block024Part008CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block024Part008SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block024Part008] using hcert

def TailChunk001Sub000Block024Part009SupportExplicit : Finset ℕ :=
  ([17498] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block024Part009 : ℚ :=
  (397965325 : ℚ) / 18357200521003008

def SurrogateDiagonalTailChunk001Sub000Block024Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17498
    = surrogateDiagTailX0RatChunk001Sub000Block024Part009

theorem surrogateDiagonalTailChunk001Sub000Block024Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block024Part009CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block024Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block024Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block024Part009CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block024Part009SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block024Part009] using hcert

def TailChunk001Sub000Block024Part010SupportExplicit : Finset ℕ :=
  ([17499] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block024Part010 : ℚ :=
  (2100392359525 : ℚ) / 36823288275741984768

def SurrogateDiagonalTailChunk001Sub000Block024Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17499
    = surrogateDiagTailX0RatChunk001Sub000Block024Part010

theorem surrogateDiagonalTailChunk001Sub000Block024Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block024Part010CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block024Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block024Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block024Part010CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block024Part010SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block024Part010] using hcert

def TailChunk001Sub000Block024Part011SupportExplicit : Finset ℕ :=
  ([17501] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block024Part011 : ℚ :=
  (26406357889 : ℚ) / 5227499679613747200

def SurrogateDiagonalTailChunk001Sub000Block024Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17501
    = surrogateDiagTailX0RatChunk001Sub000Block024Part011

theorem surrogateDiagonalTailChunk001Sub000Block024Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block024Part011CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block024Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block024Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block024Part011CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block024Part011SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block024Part011] using hcert

def TailChunk001Sub000Block024Part012SupportExplicit : Finset ℕ :=
  ([17502] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block024Part012 : ℚ :=
  (531647128475 : ℚ) / 1446328434628076544

def SurrogateDiagonalTailChunk001Sub000Block024Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17502
    = surrogateDiagTailX0RatChunk001Sub000Block024Part012

theorem surrogateDiagonalTailChunk001Sub000Block024Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block024Part012CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block024Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block024Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block024Part012CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block024Part012SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block024Part012] using hcert

def TailChunk001Sub000Block024Part013SupportExplicit : Finset ℕ :=
  ([17503] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block024Part013 : ℚ :=
  (162362257 : ℚ) / 142124599255203840

def SurrogateDiagonalTailChunk001Sub000Block024Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17503
    = surrogateDiagTailX0RatChunk001Sub000Block024Part013

theorem surrogateDiagonalTailChunk001Sub000Block024Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block024Part013CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block024Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block024Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block024Part013CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block024Part013SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block024Part013] using hcert

def TailChunk001Sub000Block024Part014SupportExplicit : Finset ℕ :=
  ([17506] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block024Part014 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block024Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17506
    = surrogateDiagTailX0RatChunk001Sub000Block024Part014

theorem surrogateDiagonalTailChunk001Sub000Block024Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block024Part014CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block024Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block024Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block024Part014CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block024Part014SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block024Part014] using hcert

def TailChunk001Sub000Block024Part015SupportExplicit : Finset ℕ :=
  ([17507] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block024Part015 : ℚ :=
  (12075553793 : ℚ) / 1433558974464000000

def SurrogateDiagonalTailChunk001Sub000Block024Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17507
    = surrogateDiagTailX0RatChunk001Sub000Block024Part015

theorem surrogateDiagonalTailChunk001Sub000Block024Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block024Part015CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block024Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block024Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block024Part015CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block024Part015SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block024Part015] using hcert

def TailChunk001Sub000Block024Part016SupportExplicit : Finset ℕ :=
  ([17509] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block024Part016 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block024Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17509
    = surrogateDiagTailX0RatChunk001Sub000Block024Part016

theorem surrogateDiagonalTailChunk001Sub000Block024Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block024Part016CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block024Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block024Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block024Part016CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block024Part016SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block024Part016] using hcert

def TailChunk001Sub000Block024Part017SupportExplicit : Finset ℕ :=
  ([17510] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block024Part017 : ℚ :=
  (23923215725 : ℚ) / 168183612900900864

def SurrogateDiagonalTailChunk001Sub000Block024Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17510
    = surrogateDiagTailX0RatChunk001Sub000Block024Part017

theorem surrogateDiagonalTailChunk001Sub000Block024Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block024Part017CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block024Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block024Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block024Part017CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block024Part017SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block024Part017] using hcert

def TailChunk001Sub000Block024Part018SupportExplicit : Finset ℕ :=
  ([17511] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block024Part018 : ℚ :=
  (684088996175 : ℚ) / 11139421234670862336

def SurrogateDiagonalTailChunk001Sub000Block024Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17511
    = surrogateDiagTailX0RatChunk001Sub000Block024Part018

theorem surrogateDiagonalTailChunk001Sub000Block024Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block024Part018CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block024Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block024Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block024Part018CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block024Part018SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block024Part018] using hcert

def TailChunk001Sub000Block024Part019SupportExplicit : Finset ℕ :=
  ([17513] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block024Part019 : ℚ :=
  (203050553 : ℚ) / 488592654583118400

def SurrogateDiagonalTailChunk001Sub000Block024Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17513
    = surrogateDiagTailX0RatChunk001Sub000Block024Part019

theorem surrogateDiagonalTailChunk001Sub000Block024Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block024Part019CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block024Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block024Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block024Part019CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block024Part019SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block024Part019] using hcert

def TailChunk001Sub000Block024Part020SupportExplicit : Finset ℕ :=
  ([17515] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block024Part020 : ℚ :=
  (9076693567 : ℚ) / 466214616406425600

def SurrogateDiagonalTailChunk001Sub000Block024Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17515
    = surrogateDiagTailX0RatChunk001Sub000Block024Part020

theorem surrogateDiagonalTailChunk001Sub000Block024Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block024Part020CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block024Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block024Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block024Part020CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block024Part020SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block024Part020] using hcert

def TailChunk001Sub000Block024Part021SupportExplicit : Finset ℕ :=
  ([17517] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block024Part021 : ℚ :=
  (21742502975 : ℚ) / 474217010590510656

def SurrogateDiagonalTailChunk001Sub000Block024Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17517
    = surrogateDiagTailX0RatChunk001Sub000Block024Part021

theorem surrogateDiagonalTailChunk001Sub000Block024Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block024Part021CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block024Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block024Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block024Part021CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block024Part021SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block024Part021] using hcert

def TailChunk001Sub000Block024Part022SupportExplicit : Finset ℕ :=
  ([17518] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block024Part022 : ℚ :=
  (80429587 : ℚ) / 6268259015202816

def SurrogateDiagonalTailChunk001Sub000Block024Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17518
    = surrogateDiagTailX0RatChunk001Sub000Block024Part022

theorem surrogateDiagonalTailChunk001Sub000Block024Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block024Part022CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block024Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block024Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block024Part022CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block024Part022SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block024Part022] using hcert

def TailChunk001Sub000Block024Part023SupportExplicit : Finset ℕ :=
  ([17519] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block024Part023 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block024Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17519
    = surrogateDiagTailX0RatChunk001Sub000Block024Part023

theorem surrogateDiagonalTailChunk001Sub000Block024Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block024Part023CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block024Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block024Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block024Part023CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block024Part023SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block024Part023] using hcert

def TailChunk001Sub000Block024Part024SupportExplicit : Finset ℕ :=
  ([17521] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block024Part024 : ℚ :=
  (392109406175 : ℚ) / 63496689928251845184

def SurrogateDiagonalTailChunk001Sub000Block024Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17521
    = surrogateDiagTailX0RatChunk001Sub000Block024Part024

theorem surrogateDiagonalTailChunk001Sub000Block024Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block024Part024CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block024Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block024Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block024Part024CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block024Part024SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block024Part024] using hcert

def surrogateDiagonalTailChunk001Sub000Block024HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block024Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block024Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block024Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block024Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block024Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block024Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block024Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block024Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block024Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block024Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block024Head : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block024Part000
    + surrogateDiagTailX0RatChunk001Sub000Block024Part001
    + surrogateDiagTailX0RatChunk001Sub000Block024Part002
    + surrogateDiagTailX0RatChunk001Sub000Block024Part003
    + surrogateDiagTailX0RatChunk001Sub000Block024Part004
    + surrogateDiagTailX0RatChunk001Sub000Block024Part005
    + surrogateDiagTailX0RatChunk001Sub000Block024Part006
    + surrogateDiagTailX0RatChunk001Sub000Block024Part007
    + surrogateDiagTailX0RatChunk001Sub000Block024Part008
    + surrogateDiagTailX0RatChunk001Sub000Block024Part009

def surrogateDiagonalTailChunk001Sub000Block024MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block024Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block024Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block024Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block024Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block024Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block024Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block024Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block024Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block024Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block024Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block024Mid : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block024Part010
    + surrogateDiagTailX0RatChunk001Sub000Block024Part011
    + surrogateDiagTailX0RatChunk001Sub000Block024Part012
    + surrogateDiagTailX0RatChunk001Sub000Block024Part013
    + surrogateDiagTailX0RatChunk001Sub000Block024Part014
    + surrogateDiagTailX0RatChunk001Sub000Block024Part015
    + surrogateDiagTailX0RatChunk001Sub000Block024Part016
    + surrogateDiagTailX0RatChunk001Sub000Block024Part017
    + surrogateDiagTailX0RatChunk001Sub000Block024Part018
    + surrogateDiagTailX0RatChunk001Sub000Block024Part019

def surrogateDiagonalTailChunk001Sub000Block024TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block024Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block024Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block024Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block024Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block024Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block024Tail : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block024Part020
    + surrogateDiagTailX0RatChunk001Sub000Block024Part021
    + surrogateDiagTailX0RatChunk001Sub000Block024Part022
    + surrogateDiagTailX0RatChunk001Sub000Block024Part023
    + surrogateDiagTailX0RatChunk001Sub000Block024Part024

def surrogateDiagonalTailChunk001Sub000Block024Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk001Sub000Block024HeadSum X0
    + surrogateDiagonalTailChunk001Sub000Block024MidSum X0
    + surrogateDiagonalTailChunk001Sub000Block024TailSum X0

def surrogateDiagTailX0RatChunk001Sub000Block024 : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block024Part000
    + surrogateDiagTailX0RatChunk001Sub000Block024Part001
    + surrogateDiagTailX0RatChunk001Sub000Block024Part002
    + surrogateDiagTailX0RatChunk001Sub000Block024Part003
    + surrogateDiagTailX0RatChunk001Sub000Block024Part004
    + surrogateDiagTailX0RatChunk001Sub000Block024Part005
    + surrogateDiagTailX0RatChunk001Sub000Block024Part006
    + surrogateDiagTailX0RatChunk001Sub000Block024Part007
    + surrogateDiagTailX0RatChunk001Sub000Block024Part008
    + surrogateDiagTailX0RatChunk001Sub000Block024Part009
    + surrogateDiagTailX0RatChunk001Sub000Block024Part010
    + surrogateDiagTailX0RatChunk001Sub000Block024Part011
    + surrogateDiagTailX0RatChunk001Sub000Block024Part012
    + surrogateDiagTailX0RatChunk001Sub000Block024Part013
    + surrogateDiagTailX0RatChunk001Sub000Block024Part014
    + surrogateDiagTailX0RatChunk001Sub000Block024Part015
    + surrogateDiagTailX0RatChunk001Sub000Block024Part016
    + surrogateDiagTailX0RatChunk001Sub000Block024Part017
    + surrogateDiagTailX0RatChunk001Sub000Block024Part018
    + surrogateDiagTailX0RatChunk001Sub000Block024Part019
    + surrogateDiagTailX0RatChunk001Sub000Block024Part020
    + surrogateDiagTailX0RatChunk001Sub000Block024Part021
    + surrogateDiagTailX0RatChunk001Sub000Block024Part022
    + surrogateDiagTailX0RatChunk001Sub000Block024Part023
    + surrogateDiagTailX0RatChunk001Sub000Block024Part024

theorem surrogateDiagTailX0RatChunk001Sub000Block024_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk001Sub000Block024Head + surrogateDiagTailX0RatChunk001Sub000Block024Mid + surrogateDiagTailX0RatChunk001Sub000Block024Tail =
      surrogateDiagTailX0RatChunk001Sub000Block024 := by
  unfold surrogateDiagTailX0RatChunk001Sub000Block024Head surrogateDiagTailX0RatChunk001Sub000Block024Mid surrogateDiagTailX0RatChunk001Sub000Block024Tail surrogateDiagTailX0RatChunk001Sub000Block024
  ring

def SurrogateDiagonalTailChunk001Sub000Block024HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block024HeadSum X0 = surrogateDiagTailX0RatChunk001Sub000Block024Head

def SurrogateDiagonalTailChunk001Sub000Block024MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block024MidSum X0 = surrogateDiagTailX0RatChunk001Sub000Block024Mid

def SurrogateDiagonalTailChunk001Sub000Block024TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block024TailSum X0 = surrogateDiagTailX0RatChunk001Sub000Block024Tail

theorem surrogateDiagonalTailChunk001Sub000Block024_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk001Sub000Block024HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk001Sub000Block024MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk001Sub000Block024TailCertificateAt X0) :
    surrogateDiagonalTailChunk001Sub000Block024Sum X0 = surrogateDiagTailX0RatChunk001Sub000Block024 := by
  unfold SurrogateDiagonalTailChunk001Sub000Block024HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk001Sub000Block024MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk001Sub000Block024TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk001Sub000Block024Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk001Sub000Block024_eq_head_add_mid_add_tail

/-- Block 025 covers tail-support indices [10625,10650) and q from 17522 to 17563. -/

def TailChunk001Sub000Block025Part000SupportExplicit : Finset ℕ :=
  ([17522] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block025Part000 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block025Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17522
    = surrogateDiagTailX0RatChunk001Sub000Block025Part000

theorem surrogateDiagonalTailChunk001Sub000Block025Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block025Part000CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block025Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block025Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block025Part000CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block025Part000SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block025Part000] using hcert

def TailChunk001Sub000Block025Part001SupportExplicit : Finset ℕ :=
  ([17526] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block025Part001 : ℚ :=
  (31684587925 : ℚ) / 131234264076174336

def SurrogateDiagonalTailChunk001Sub000Block025Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17526
    = surrogateDiagTailX0RatChunk001Sub000Block025Part001

theorem surrogateDiagonalTailChunk001Sub000Block025Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block025Part001CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block025Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block025Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block025Part001CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block025Part001SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block025Part001] using hcert

def TailChunk001Sub000Block025Part002SupportExplicit : Finset ℕ :=
  ([17527] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block025Part002 : ℚ :=
  (13450585681 : ℚ) / 7377609764123443200

def SurrogateDiagonalTailChunk001Sub000Block025Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17527
    = surrogateDiagTailX0RatChunk001Sub000Block025Part002

theorem surrogateDiagonalTailChunk001Sub000Block025Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block025Part002CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block025Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block025Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block025Part002CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block025Part002SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block025Part002] using hcert

def TailChunk001Sub000Block025Part003SupportExplicit : Finset ℕ :=
  ([17529] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block025Part003 : ℚ :=
  (1066842645725 : ℚ) / 23300382819000773184

def SurrogateDiagonalTailChunk001Sub000Block025Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17529
    = surrogateDiagTailX0RatChunk001Sub000Block025Part003

theorem surrogateDiagonalTailChunk001Sub000Block025Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block025Part003CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block025Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block025Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block025Part003CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block025Part003SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block025Part003] using hcert

def TailChunk001Sub000Block025Part004SupportExplicit : Finset ℕ :=
  ([17530] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block025Part004 : ℚ :=
  (288275964725 : ℚ) / 3015596536632705024

def SurrogateDiagonalTailChunk001Sub000Block025Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17530
    = surrogateDiagTailX0RatChunk001Sub000Block025Part004

theorem surrogateDiagonalTailChunk001Sub000Block025Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block025Part004CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block025Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block025Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block025Part004CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block025Part004SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block025Part004] using hcert

def TailChunk001Sub000Block025Part005SupportExplicit : Finset ℕ :=
  ([17531] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block025Part005 : ℚ :=
  (42164788625 : ℚ) / 71467516468878022656

def SurrogateDiagonalTailChunk001Sub000Block025Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17531
    = surrogateDiagTailX0RatChunk001Sub000Block025Part005

theorem surrogateDiagonalTailChunk001Sub000Block025Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block025Part005CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block025Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block025Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block025Part005CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block025Part005SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block025Part005] using hcert

def TailChunk001Sub000Block025Part006SupportExplicit : Finset ℕ :=
  ([17533] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block025Part006 : ℚ :=
  (87625896475 : ℚ) / 221300213497956139008

def SurrogateDiagonalTailChunk001Sub000Block025Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17533
    = surrogateDiagTailX0RatChunk001Sub000Block025Part006

theorem surrogateDiagonalTailChunk001Sub000Block025Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block025Part006CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block025Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block025Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block025Part006CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block025Part006SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block025Part006] using hcert

def TailChunk001Sub000Block025Part007SupportExplicit : Finset ℕ :=
  ([17534] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block025Part007 : ℚ :=
  (961981297 : ℚ) / 40154952930309120

def SurrogateDiagonalTailChunk001Sub000Block025Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17534
    = surrogateDiagTailX0RatChunk001Sub000Block025Part007

theorem surrogateDiagonalTailChunk001Sub000Block025Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block025Part007CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block025Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block025Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block025Part007CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block025Part007SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block025Part007] using hcert

def TailChunk001Sub000Block025Part008SupportExplicit : Finset ℕ :=
  ([17535] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block025Part008 : ℚ :=
  (194176865225 : ℚ) / 1119906205473964032

def SurrogateDiagonalTailChunk001Sub000Block025Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17535
    = surrogateDiagTailX0RatChunk001Sub000Block025Part008

theorem surrogateDiagonalTailChunk001Sub000Block025Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block025Part008CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block025Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block025Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block025Part008CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block025Part008SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block025Part008] using hcert

def TailChunk001Sub000Block025Part009SupportExplicit : Finset ℕ :=
  ([17537] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block025Part009 : ℚ :=
  (14924981039 : ℚ) / 2613749839806873600

def SurrogateDiagonalTailChunk001Sub000Block025Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17537
    = surrogateDiagTailX0RatChunk001Sub000Block025Part009

theorem surrogateDiagonalTailChunk001Sub000Block025Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block025Part009CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block025Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block025Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block025Part009CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block025Part009SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block025Part009] using hcert

def TailChunk001Sub000Block025Part010SupportExplicit : Finset ℕ :=
  ([17538] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block025Part010 : ℚ :=
  (562730433325 : ℚ) / 2487340580582227968

def SurrogateDiagonalTailChunk001Sub000Block025Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17538
    = surrogateDiagTailX0RatChunk001Sub000Block025Part010

theorem surrogateDiagonalTailChunk001Sub000Block025Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block025Part010CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block025Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block025Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block025Part010CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block025Part010SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block025Part010] using hcert

def TailChunk001Sub000Block025Part011SupportExplicit : Finset ℕ :=
  ([17539] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block025Part011 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block025Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17539
    = surrogateDiagTailX0RatChunk001Sub000Block025Part011

theorem surrogateDiagonalTailChunk001Sub000Block025Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block025Part011CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block025Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block025Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block025Part011CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block025Part011SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block025Part011] using hcert

def TailChunk001Sub000Block025Part012SupportExplicit : Finset ℕ :=
  ([17543] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block025Part012 : ℚ :=
  (945326027 : ℚ) / 1734546631625533440

def SurrogateDiagonalTailChunk001Sub000Block025Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17543
    = surrogateDiagTailX0RatChunk001Sub000Block025Part012

theorem surrogateDiagonalTailChunk001Sub000Block025Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block025Part012CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block025Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block025Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block025Part012CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block025Part012SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block025Part012] using hcert

def TailChunk001Sub000Block025Part013SupportExplicit : Finset ℕ :=
  ([17546] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block025Part013 : ℚ :=
  (36542111861 : ℚ) / 102470368506906240

def SurrogateDiagonalTailChunk001Sub000Block025Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17546
    = surrogateDiagTailX0RatChunk001Sub000Block025Part013

theorem surrogateDiagonalTailChunk001Sub000Block025Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block025Part013CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block025Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block025Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block025Part013CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block025Part013SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block025Part013] using hcert

def TailChunk001Sub000Block025Part014SupportExplicit : Finset ℕ :=
  ([17547] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block025Part014 : ℚ :=
  (534517260325 : ℚ) / 11698126301456965632

def SurrogateDiagonalTailChunk001Sub000Block025Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17547
    = surrogateDiagTailX0RatChunk001Sub000Block025Part014

theorem surrogateDiagonalTailChunk001Sub000Block025Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block025Part014CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block025Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block025Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block025Part014CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block025Part014SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block025Part014] using hcert

def TailChunk001Sub000Block025Part015SupportExplicit : Finset ℕ :=
  ([17549] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block025Part015 : ℚ :=
  (310621418675 : ℚ) / 34426775774245257216

def SurrogateDiagonalTailChunk001Sub000Block025Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17549
    = surrogateDiagTailX0RatChunk001Sub000Block025Part015

theorem surrogateDiagonalTailChunk001Sub000Block025Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block025Part015CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block025Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block025Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block025Part015CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block025Part015SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block025Part015] using hcert

def TailChunk001Sub000Block025Part016SupportExplicit : Finset ℕ :=
  ([17551] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block025Part016 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block025Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17551
    = surrogateDiagTailX0RatChunk001Sub000Block025Part016

theorem surrogateDiagonalTailChunk001Sub000Block025Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block025Part016CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block025Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block025Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block025Part016CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block025Part016SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block025Part016] using hcert

def TailChunk001Sub000Block025Part017SupportExplicit : Finset ℕ :=
  ([17553] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block025Part017 : ℚ :=
  (1711625033 : ℚ) / 37485239748840000

def SurrogateDiagonalTailChunk001Sub000Block025Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17553
    = surrogateDiagTailX0RatChunk001Sub000Block025Part017

theorem surrogateDiagonalTailChunk001Sub000Block025Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block025Part017CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block025Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block025Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block025Part017CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block025Part017SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block025Part017] using hcert

def TailChunk001Sub000Block025Part018SupportExplicit : Finset ℕ :=
  ([17554] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block025Part018 : ℚ :=
  (651931789 : ℚ) / 1895265113227200

def SurrogateDiagonalTailChunk001Sub000Block025Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17554
    = surrogateDiagTailX0RatChunk001Sub000Block025Part018

theorem surrogateDiagonalTailChunk001Sub000Block025Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block025Part018CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block025Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block025Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block025Part018CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block025Part018SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block025Part018] using hcert

def TailChunk001Sub000Block025Part019SupportExplicit : Finset ℕ :=
  ([17555] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block025Part019 : ℚ :=
  (6170055989 : ℚ) / 777293931431946240

def SurrogateDiagonalTailChunk001Sub000Block025Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17555
    = surrogateDiagTailX0RatChunk001Sub000Block025Part019

theorem surrogateDiagonalTailChunk001Sub000Block025Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block025Part019CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block025Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block025Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block025Part019CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block025Part019SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block025Part019] using hcert

def TailChunk001Sub000Block025Part020SupportExplicit : Finset ℕ :=
  ([17557] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block025Part020 : ℚ :=
  (433252127 : ℚ) / 1114735458543206400

def SurrogateDiagonalTailChunk001Sub000Block025Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17557
    = surrogateDiagTailX0RatChunk001Sub000Block025Part020

theorem surrogateDiagonalTailChunk001Sub000Block025Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block025Part020CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block025Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block025Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block025Part020CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block025Part020SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block025Part020] using hcert

def TailChunk001Sub000Block025Part021SupportExplicit : Finset ℕ :=
  ([17558] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block025Part021 : ℚ :=
  (1204231890625 : ℚ) / 3711497510562308082

def SurrogateDiagonalTailChunk001Sub000Block025Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17558
    = surrogateDiagTailX0RatChunk001Sub000Block025Part021

theorem surrogateDiagonalTailChunk001Sub000Block025Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block025Part021CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block025Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block025Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block025Part021CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block025Part021SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block025Part021] using hcert

def TailChunk001Sub000Block025Part022SupportExplicit : Finset ℕ :=
  ([17561] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block025Part022 : ℚ :=
  (271095080275 : ℚ) / 185876967555090874368

def SurrogateDiagonalTailChunk001Sub000Block025Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17561
    = surrogateDiagTailX0RatChunk001Sub000Block025Part022

theorem surrogateDiagonalTailChunk001Sub000Block025Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block025Part022CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block025Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block025Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block025Part022CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block025Part022SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block025Part022] using hcert

def TailChunk001Sub000Block025Part023SupportExplicit : Finset ℕ :=
  ([17562] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block025Part023 : ℚ :=
  (669128547025 : ℚ) / 733135310728357152

def SurrogateDiagonalTailChunk001Sub000Block025Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17562
    = surrogateDiagTailX0RatChunk001Sub000Block025Part023

theorem surrogateDiagonalTailChunk001Sub000Block025Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block025Part023CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block025Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block025Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block025Part023CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block025Part023SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block025Part023] using hcert

def TailChunk001Sub000Block025Part024SupportExplicit : Finset ℕ :=
  ([17563] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block025Part024 : ℚ :=
  (6828145925 : ℚ) / 634160616415690752

def SurrogateDiagonalTailChunk001Sub000Block025Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17563
    = surrogateDiagTailX0RatChunk001Sub000Block025Part024

theorem surrogateDiagonalTailChunk001Sub000Block025Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block025Part024CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block025Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block025Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block025Part024CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block025Part024SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block025Part024] using hcert

def surrogateDiagonalTailChunk001Sub000Block025HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block025Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block025Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block025Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block025Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block025Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block025Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block025Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block025Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block025Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block025Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block025Head : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block025Part000
    + surrogateDiagTailX0RatChunk001Sub000Block025Part001
    + surrogateDiagTailX0RatChunk001Sub000Block025Part002
    + surrogateDiagTailX0RatChunk001Sub000Block025Part003
    + surrogateDiagTailX0RatChunk001Sub000Block025Part004
    + surrogateDiagTailX0RatChunk001Sub000Block025Part005
    + surrogateDiagTailX0RatChunk001Sub000Block025Part006
    + surrogateDiagTailX0RatChunk001Sub000Block025Part007
    + surrogateDiagTailX0RatChunk001Sub000Block025Part008
    + surrogateDiagTailX0RatChunk001Sub000Block025Part009

def surrogateDiagonalTailChunk001Sub000Block025MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block025Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block025Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block025Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block025Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block025Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block025Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block025Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block025Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block025Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block025Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block025Mid : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block025Part010
    + surrogateDiagTailX0RatChunk001Sub000Block025Part011
    + surrogateDiagTailX0RatChunk001Sub000Block025Part012
    + surrogateDiagTailX0RatChunk001Sub000Block025Part013
    + surrogateDiagTailX0RatChunk001Sub000Block025Part014
    + surrogateDiagTailX0RatChunk001Sub000Block025Part015
    + surrogateDiagTailX0RatChunk001Sub000Block025Part016
    + surrogateDiagTailX0RatChunk001Sub000Block025Part017
    + surrogateDiagTailX0RatChunk001Sub000Block025Part018
    + surrogateDiagTailX0RatChunk001Sub000Block025Part019

def surrogateDiagonalTailChunk001Sub000Block025TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block025Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block025Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block025Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block025Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block025Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block025Tail : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block025Part020
    + surrogateDiagTailX0RatChunk001Sub000Block025Part021
    + surrogateDiagTailX0RatChunk001Sub000Block025Part022
    + surrogateDiagTailX0RatChunk001Sub000Block025Part023
    + surrogateDiagTailX0RatChunk001Sub000Block025Part024

def surrogateDiagonalTailChunk001Sub000Block025Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk001Sub000Block025HeadSum X0
    + surrogateDiagonalTailChunk001Sub000Block025MidSum X0
    + surrogateDiagonalTailChunk001Sub000Block025TailSum X0

def surrogateDiagTailX0RatChunk001Sub000Block025 : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block025Part000
    + surrogateDiagTailX0RatChunk001Sub000Block025Part001
    + surrogateDiagTailX0RatChunk001Sub000Block025Part002
    + surrogateDiagTailX0RatChunk001Sub000Block025Part003
    + surrogateDiagTailX0RatChunk001Sub000Block025Part004
    + surrogateDiagTailX0RatChunk001Sub000Block025Part005
    + surrogateDiagTailX0RatChunk001Sub000Block025Part006
    + surrogateDiagTailX0RatChunk001Sub000Block025Part007
    + surrogateDiagTailX0RatChunk001Sub000Block025Part008
    + surrogateDiagTailX0RatChunk001Sub000Block025Part009
    + surrogateDiagTailX0RatChunk001Sub000Block025Part010
    + surrogateDiagTailX0RatChunk001Sub000Block025Part011
    + surrogateDiagTailX0RatChunk001Sub000Block025Part012
    + surrogateDiagTailX0RatChunk001Sub000Block025Part013
    + surrogateDiagTailX0RatChunk001Sub000Block025Part014
    + surrogateDiagTailX0RatChunk001Sub000Block025Part015
    + surrogateDiagTailX0RatChunk001Sub000Block025Part016
    + surrogateDiagTailX0RatChunk001Sub000Block025Part017
    + surrogateDiagTailX0RatChunk001Sub000Block025Part018
    + surrogateDiagTailX0RatChunk001Sub000Block025Part019
    + surrogateDiagTailX0RatChunk001Sub000Block025Part020
    + surrogateDiagTailX0RatChunk001Sub000Block025Part021
    + surrogateDiagTailX0RatChunk001Sub000Block025Part022
    + surrogateDiagTailX0RatChunk001Sub000Block025Part023
    + surrogateDiagTailX0RatChunk001Sub000Block025Part024

theorem surrogateDiagTailX0RatChunk001Sub000Block025_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk001Sub000Block025Head + surrogateDiagTailX0RatChunk001Sub000Block025Mid + surrogateDiagTailX0RatChunk001Sub000Block025Tail =
      surrogateDiagTailX0RatChunk001Sub000Block025 := by
  unfold surrogateDiagTailX0RatChunk001Sub000Block025Head surrogateDiagTailX0RatChunk001Sub000Block025Mid surrogateDiagTailX0RatChunk001Sub000Block025Tail surrogateDiagTailX0RatChunk001Sub000Block025
  ring

def SurrogateDiagonalTailChunk001Sub000Block025HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block025HeadSum X0 = surrogateDiagTailX0RatChunk001Sub000Block025Head

def SurrogateDiagonalTailChunk001Sub000Block025MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block025MidSum X0 = surrogateDiagTailX0RatChunk001Sub000Block025Mid

def SurrogateDiagonalTailChunk001Sub000Block025TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block025TailSum X0 = surrogateDiagTailX0RatChunk001Sub000Block025Tail

theorem surrogateDiagonalTailChunk001Sub000Block025_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk001Sub000Block025HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk001Sub000Block025MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk001Sub000Block025TailCertificateAt X0) :
    surrogateDiagonalTailChunk001Sub000Block025Sum X0 = surrogateDiagTailX0RatChunk001Sub000Block025 := by
  unfold SurrogateDiagonalTailChunk001Sub000Block025HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk001Sub000Block025MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk001Sub000Block025TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk001Sub000Block025Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk001Sub000Block025_eq_head_add_mid_add_tail

/-- Block 026 covers tail-support indices [10650,10675) and q from 17565 to 17603. -/

def TailChunk001Sub000Block026Part000SupportExplicit : Finset ℕ :=
  ([17565] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block026Part000 : ℚ :=
  (1212635759 : ℚ) / 11810734000865280

def SurrogateDiagonalTailChunk001Sub000Block026Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17565
    = surrogateDiagTailX0RatChunk001Sub000Block026Part000

theorem surrogateDiagonalTailChunk001Sub000Block026Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block026Part000CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block026Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block026Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block026Part000CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block026Part000SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block026Part000] using hcert

def TailChunk001Sub000Block026Part001SupportExplicit : Finset ℕ :=
  ([17566] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block026Part001 : ℚ :=
  (1205329515625 : ℚ) / 3718267226105882322

def SurrogateDiagonalTailChunk001Sub000Block026Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17566
    = surrogateDiagTailX0RatChunk001Sub000Block026Part001

theorem surrogateDiagonalTailChunk001Sub000Block026Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block026Part001CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block026Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block026Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block026Part001CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block026Part001SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block026Part001] using hcert

def TailChunk001Sub000Block026Part002SupportExplicit : Finset ℕ :=
  ([17567] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block026Part002 : ℚ :=
  (2745939619 : ℚ) / 927086716075161600

def SurrogateDiagonalTailChunk001Sub000Block026Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17567
    = surrogateDiagTailX0RatChunk001Sub000Block026Part002

theorem surrogateDiagonalTailChunk001Sub000Block026Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block026Part002CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block026Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block026Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block026Part002CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block026Part002SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block026Part002] using hcert

def TailChunk001Sub000Block026Part003SupportExplicit : Finset ℕ :=
  ([17569] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block026Part003 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block026Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17569
    = surrogateDiagTailX0RatChunk001Sub000Block026Part003

theorem surrogateDiagonalTailChunk001Sub000Block026Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block026Part003CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block026Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block026Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block026Part003CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block026Part003SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block026Part003] using hcert

def TailChunk001Sub000Block026Part004SupportExplicit : Finset ℕ :=
  ([17570] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block026Part004 : ℚ :=
  (13887072767 : ℚ) / 16203240000000000

def SurrogateDiagonalTailChunk001Sub000Block026Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17570
    = surrogateDiagTailX0RatChunk001Sub000Block026Part004

theorem surrogateDiagonalTailChunk001Sub000Block026Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block026Part004CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block026Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block026Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block026Part004CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block026Part004SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block026Part004] using hcert

def TailChunk001Sub000Block026Part005SupportExplicit : Finset ℕ :=
  ([17571] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block026Part005 : ℚ :=
  (535980260275 : ℚ) / 11762269407141691392

def SurrogateDiagonalTailChunk001Sub000Block026Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17571
    = surrogateDiagTailX0RatChunk001Sub000Block026Part005

theorem surrogateDiagonalTailChunk001Sub000Block026Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block026Part005CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block026Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block026Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block026Part005CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block026Part005SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block026Part005] using hcert

def TailChunk001Sub000Block026Part006SupportExplicit : Finset ℕ :=
  ([17573] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block026Part006 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block026Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17573
    = surrogateDiagTailX0RatChunk001Sub000Block026Part006

theorem surrogateDiagonalTailChunk001Sub000Block026Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block026Part006CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block026Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block026Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block026Part006CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block026Part006SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block026Part006] using hcert

def TailChunk001Sub000Block026Part007SupportExplicit : Finset ℕ :=
  ([17574] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block026Part007 : ℚ :=
  (101026604479 : ℚ) / 98364628992000000

def SurrogateDiagonalTailChunk001Sub000Block026Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17574
    = surrogateDiagTailX0RatChunk001Sub000Block026Part007

theorem surrogateDiagonalTailChunk001Sub000Block026Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block026Part007CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block026Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block026Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block026Part007CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block026Part007SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block026Part007] using hcert

def TailChunk001Sub000Block026Part008SupportExplicit : Finset ℕ :=
  ([17578] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block026Part008 : ℚ :=
  (75116666813 : ℚ) / 146746621663641600

def SurrogateDiagonalTailChunk001Sub000Block026Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17578
    = surrogateDiagTailX0RatChunk001Sub000Block026Part008

theorem surrogateDiagonalTailChunk001Sub000Block026Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block026Part008CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block026Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block026Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block026Part008CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block026Part008SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block026Part008] using hcert

def TailChunk001Sub000Block026Part009SupportExplicit : Finset ℕ :=
  ([17579] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block026Part009 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block026Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17579
    = surrogateDiagTailX0RatChunk001Sub000Block026Part009

theorem surrogateDiagonalTailChunk001Sub000Block026Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block026Part009CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block026Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block026Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block026Part009CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block026Part009SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block026Part009] using hcert

def TailChunk001Sub000Block026Part010SupportExplicit : Finset ℕ :=
  ([17581] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block026Part010 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block026Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17581
    = surrogateDiagTailX0RatChunk001Sub000Block026Part010

theorem surrogateDiagonalTailChunk001Sub000Block026Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block026Part010CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block026Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block026Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block026Part010CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block026Part010SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block026Part010] using hcert

def TailChunk001Sub000Block026Part011SupportExplicit : Finset ℕ :=
  ([17582] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block026Part011 : ℚ :=
  (1556406911775 : ℚ) / 4525477812682233856

def SurrogateDiagonalTailChunk001Sub000Block026Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17582
    = surrogateDiagTailX0RatChunk001Sub000Block026Part011

theorem surrogateDiagonalTailChunk001Sub000Block026Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block026Part011CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block026Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block026Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block026Part011CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block026Part011SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block026Part011] using hcert

def TailChunk001Sub000Block026Part012SupportExplicit : Finset ℕ :=
  ([17583] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block026Part012 : ℚ :=
  (2146850041 : ℚ) / 47177758791425280

def SurrogateDiagonalTailChunk001Sub000Block026Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17583
    = surrogateDiagTailX0RatChunk001Sub000Block026Part012

theorem surrogateDiagonalTailChunk001Sub000Block026Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block026Part012CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block026Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block026Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block026Part012CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block026Part012SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block026Part012] using hcert

def TailChunk001Sub000Block026Part013SupportExplicit : Finset ℕ :=
  ([17585] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block026Part013 : ℚ :=
  (773891747875 : ℚ) / 97827800629899460608

def SurrogateDiagonalTailChunk001Sub000Block026Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17585
    = surrogateDiagTailX0RatChunk001Sub000Block026Part013

theorem surrogateDiagonalTailChunk001Sub000Block026Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block026Part013CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block026Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block026Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block026Part013CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block026Part013SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block026Part013] using hcert

def TailChunk001Sub000Block026Part014SupportExplicit : Finset ℕ :=
  ([17587] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block026Part014 : ℚ :=
  (3827071175 : ℚ) / 5989108377791766528

def SurrogateDiagonalTailChunk001Sub000Block026Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17587
    = surrogateDiagTailX0RatChunk001Sub000Block026Part014

theorem surrogateDiagonalTailChunk001Sub000Block026Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block026Part014CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block026Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block026Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block026Part014CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block026Part014SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block026Part014] using hcert

def TailChunk001Sub000Block026Part015SupportExplicit : Finset ℕ :=
  ([17589] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block026Part015 : ℚ :=
  (79984743187 : ℚ) / 849516429312000000

def SurrogateDiagonalTailChunk001Sub000Block026Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17589
    = surrogateDiagTailX0RatChunk001Sub000Block026Part015

theorem surrogateDiagonalTailChunk001Sub000Block026Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block026Part015CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block026Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block026Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block026Part015CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block026Part015SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block026Part015] using hcert

def TailChunk001Sub000Block026Part016SupportExplicit : Finset ℕ :=
  ([17590] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block026Part016 : ℚ :=
  (3478675649425 : ℚ) / 6114237539368716288

def SurrogateDiagonalTailChunk001Sub000Block026Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17590
    = surrogateDiagTailX0RatChunk001Sub000Block026Part016

theorem surrogateDiagonalTailChunk001Sub000Block026Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block026Part016CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block026Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block026Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block026Part016CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block026Part016SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block026Part016] using hcert

def TailChunk001Sub000Block026Part017SupportExplicit : Finset ℕ :=
  ([17593] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block026Part017 : ℚ :=
  (488215403 : ℚ) / 1114735458543206400

def SurrogateDiagonalTailChunk001Sub000Block026Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17593
    = surrogateDiagTailX0RatChunk001Sub000Block026Part017

theorem surrogateDiagonalTailChunk001Sub000Block026Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block026Part017CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block026Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block026Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block026Part017CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block026Part017SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block026Part017] using hcert

def TailChunk001Sub000Block026Part018SupportExplicit : Finset ℕ :=
  ([17594] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block026Part018 : ℚ :=
  (123943468975 : ℚ) / 332186730942816288

def SurrogateDiagonalTailChunk001Sub000Block026Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17594
    = surrogateDiagTailX0RatChunk001Sub000Block026Part018

theorem surrogateDiagonalTailChunk001Sub000Block026Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block026Part018CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block026Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block026Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block026Part018CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block026Part018SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block026Part018] using hcert

def TailChunk001Sub000Block026Part019SupportExplicit : Finset ℕ :=
  ([17597] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block026Part019 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block026Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17597
    = surrogateDiagTailX0RatChunk001Sub000Block026Part019

theorem surrogateDiagonalTailChunk001Sub000Block026Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block026Part019CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block026Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block026Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block026Part019CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block026Part019SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block026Part019] using hcert

def TailChunk001Sub000Block026Part020SupportExplicit : Finset ℕ :=
  ([17598] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block026Part020 : ℚ :=
  (2177194029625 : ℚ) / 1582912724204832768

def SurrogateDiagonalTailChunk001Sub000Block026Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17598
    = surrogateDiagTailX0RatChunk001Sub000Block026Part020

theorem surrogateDiagonalTailChunk001Sub000Block026Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block026Part020CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block026Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block026Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block026Part020CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block026Part020SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block026Part020] using hcert

def TailChunk001Sub000Block026Part021SupportExplicit : Finset ℕ :=
  ([17599] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block026Part021 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block026Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17599
    = surrogateDiagTailX0RatChunk001Sub000Block026Part021

theorem surrogateDiagonalTailChunk001Sub000Block026Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block026Part021CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block026Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block026Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block026Part021CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block026Part021SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block026Part021] using hcert

def TailChunk001Sub000Block026Part022SupportExplicit : Finset ℕ :=
  ([17601] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block026Part022 : ℚ :=
  (153660520775 : ℚ) / 3383662516960915392

def SurrogateDiagonalTailChunk001Sub000Block026Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17601
    = surrogateDiagTailX0RatChunk001Sub000Block026Part022

theorem surrogateDiagonalTailChunk001Sub000Block026Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block026Part022CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block026Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block026Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block026Part022CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block026Part022SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block026Part022] using hcert

def TailChunk001Sub000Block026Part023SupportExplicit : Finset ℕ :=
  ([17602] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block026Part023 : ℚ :=
  (4288545861775 : ℚ) / 10827760146625363968

def SurrogateDiagonalTailChunk001Sub000Block026Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17602
    = surrogateDiagTailX0RatChunk001Sub000Block026Part023

theorem surrogateDiagonalTailChunk001Sub000Block026Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block026Part023CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block026Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block026Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block026Part023CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block026Part023SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block026Part023] using hcert

def TailChunk001Sub000Block026Part024SupportExplicit : Finset ℕ :=
  ([17603] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block026Part024 : ℚ :=
  (96046299425 : ℚ) / 103638110213377926144

def SurrogateDiagonalTailChunk001Sub000Block026Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17603
    = surrogateDiagTailX0RatChunk001Sub000Block026Part024

theorem surrogateDiagonalTailChunk001Sub000Block026Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block026Part024CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block026Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block026Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block026Part024CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block026Part024SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block026Part024] using hcert

def surrogateDiagonalTailChunk001Sub000Block026HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block026Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block026Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block026Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block026Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block026Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block026Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block026Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block026Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block026Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block026Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block026Head : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block026Part000
    + surrogateDiagTailX0RatChunk001Sub000Block026Part001
    + surrogateDiagTailX0RatChunk001Sub000Block026Part002
    + surrogateDiagTailX0RatChunk001Sub000Block026Part003
    + surrogateDiagTailX0RatChunk001Sub000Block026Part004
    + surrogateDiagTailX0RatChunk001Sub000Block026Part005
    + surrogateDiagTailX0RatChunk001Sub000Block026Part006
    + surrogateDiagTailX0RatChunk001Sub000Block026Part007
    + surrogateDiagTailX0RatChunk001Sub000Block026Part008
    + surrogateDiagTailX0RatChunk001Sub000Block026Part009

def surrogateDiagonalTailChunk001Sub000Block026MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block026Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block026Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block026Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block026Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block026Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block026Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block026Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block026Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block026Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block026Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block026Mid : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block026Part010
    + surrogateDiagTailX0RatChunk001Sub000Block026Part011
    + surrogateDiagTailX0RatChunk001Sub000Block026Part012
    + surrogateDiagTailX0RatChunk001Sub000Block026Part013
    + surrogateDiagTailX0RatChunk001Sub000Block026Part014
    + surrogateDiagTailX0RatChunk001Sub000Block026Part015
    + surrogateDiagTailX0RatChunk001Sub000Block026Part016
    + surrogateDiagTailX0RatChunk001Sub000Block026Part017
    + surrogateDiagTailX0RatChunk001Sub000Block026Part018
    + surrogateDiagTailX0RatChunk001Sub000Block026Part019

def surrogateDiagonalTailChunk001Sub000Block026TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block026Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block026Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block026Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block026Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block026Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block026Tail : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block026Part020
    + surrogateDiagTailX0RatChunk001Sub000Block026Part021
    + surrogateDiagTailX0RatChunk001Sub000Block026Part022
    + surrogateDiagTailX0RatChunk001Sub000Block026Part023
    + surrogateDiagTailX0RatChunk001Sub000Block026Part024

def surrogateDiagonalTailChunk001Sub000Block026Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk001Sub000Block026HeadSum X0
    + surrogateDiagonalTailChunk001Sub000Block026MidSum X0
    + surrogateDiagonalTailChunk001Sub000Block026TailSum X0

def surrogateDiagTailX0RatChunk001Sub000Block026 : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block026Part000
    + surrogateDiagTailX0RatChunk001Sub000Block026Part001
    + surrogateDiagTailX0RatChunk001Sub000Block026Part002
    + surrogateDiagTailX0RatChunk001Sub000Block026Part003
    + surrogateDiagTailX0RatChunk001Sub000Block026Part004
    + surrogateDiagTailX0RatChunk001Sub000Block026Part005
    + surrogateDiagTailX0RatChunk001Sub000Block026Part006
    + surrogateDiagTailX0RatChunk001Sub000Block026Part007
    + surrogateDiagTailX0RatChunk001Sub000Block026Part008
    + surrogateDiagTailX0RatChunk001Sub000Block026Part009
    + surrogateDiagTailX0RatChunk001Sub000Block026Part010
    + surrogateDiagTailX0RatChunk001Sub000Block026Part011
    + surrogateDiagTailX0RatChunk001Sub000Block026Part012
    + surrogateDiagTailX0RatChunk001Sub000Block026Part013
    + surrogateDiagTailX0RatChunk001Sub000Block026Part014
    + surrogateDiagTailX0RatChunk001Sub000Block026Part015
    + surrogateDiagTailX0RatChunk001Sub000Block026Part016
    + surrogateDiagTailX0RatChunk001Sub000Block026Part017
    + surrogateDiagTailX0RatChunk001Sub000Block026Part018
    + surrogateDiagTailX0RatChunk001Sub000Block026Part019
    + surrogateDiagTailX0RatChunk001Sub000Block026Part020
    + surrogateDiagTailX0RatChunk001Sub000Block026Part021
    + surrogateDiagTailX0RatChunk001Sub000Block026Part022
    + surrogateDiagTailX0RatChunk001Sub000Block026Part023
    + surrogateDiagTailX0RatChunk001Sub000Block026Part024

theorem surrogateDiagTailX0RatChunk001Sub000Block026_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk001Sub000Block026Head + surrogateDiagTailX0RatChunk001Sub000Block026Mid + surrogateDiagTailX0RatChunk001Sub000Block026Tail =
      surrogateDiagTailX0RatChunk001Sub000Block026 := by
  unfold surrogateDiagTailX0RatChunk001Sub000Block026Head surrogateDiagTailX0RatChunk001Sub000Block026Mid surrogateDiagTailX0RatChunk001Sub000Block026Tail surrogateDiagTailX0RatChunk001Sub000Block026
  ring

def SurrogateDiagonalTailChunk001Sub000Block026HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block026HeadSum X0 = surrogateDiagTailX0RatChunk001Sub000Block026Head

def SurrogateDiagonalTailChunk001Sub000Block026MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block026MidSum X0 = surrogateDiagTailX0RatChunk001Sub000Block026Mid

def SurrogateDiagonalTailChunk001Sub000Block026TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block026TailSum X0 = surrogateDiagTailX0RatChunk001Sub000Block026Tail

theorem surrogateDiagonalTailChunk001Sub000Block026_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk001Sub000Block026HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk001Sub000Block026MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk001Sub000Block026TailCertificateAt X0) :
    surrogateDiagonalTailChunk001Sub000Block026Sum X0 = surrogateDiagTailX0RatChunk001Sub000Block026 := by
  unfold SurrogateDiagonalTailChunk001Sub000Block026HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk001Sub000Block026MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk001Sub000Block026TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk001Sub000Block026Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk001Sub000Block026_eq_head_add_mid_add_tail

/-- Block 027 covers tail-support indices [10675,10700) and q from 17605 to 17643. -/

def TailChunk001Sub000Block027Part000SupportExplicit : Finset ℕ :=
  ([17605] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block027Part000 : ℚ :=
  (1173050832175 : ℚ) / 52684964810295902208

def SurrogateDiagonalTailChunk001Sub000Block027Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17605
    = surrogateDiagTailX0RatChunk001Sub000Block027Part000

theorem surrogateDiagonalTailChunk001Sub000Block027Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block027Part000CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block027Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block027Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block027Part000CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block027Part000SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block027Part000] using hcert

def TailChunk001Sub000Block027Part001SupportExplicit : Finset ℕ :=
  ([17606] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block027Part001 : ℚ :=
  (1210825140625 : ℚ) / 3752254822680365202

def SurrogateDiagonalTailChunk001Sub000Block027Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17606
    = surrogateDiagTailX0RatChunk001Sub000Block027Part001

theorem surrogateDiagonalTailChunk001Sub000Block027Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block027Part001CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block027Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block027Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block027Part001CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block027Part001SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block027Part001] using hcert

def TailChunk001Sub000Block027Part002SupportExplicit : Finset ℕ :=
  ([17607] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block027Part002 : ℚ :=
  (67272313775 : ℚ) / 1482372275626810944

def SurrogateDiagonalTailChunk001Sub000Block027Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17607
    = surrogateDiagTailX0RatChunk001Sub000Block027Part002

theorem surrogateDiagonalTailChunk001Sub000Block027Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block027Part002CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block027Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block027Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block027Part002CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block027Part002SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block027Part002] using hcert

def TailChunk001Sub000Block027Part003SupportExplicit : Finset ℕ :=
  ([17609] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block027Part003 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block027Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17609
    = surrogateDiagTailX0RatChunk001Sub000Block027Part003

theorem surrogateDiagonalTailChunk001Sub000Block027Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block027Part003CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block027Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block027Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block027Part003CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block027Part003SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block027Part003] using hcert

def TailChunk001Sub000Block027Part004SupportExplicit : Finset ℕ :=
  ([17610] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block027Part004 : ℚ :=
  (31230856975 : ℚ) / 18871103516570112

def SurrogateDiagonalTailChunk001Sub000Block027Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17610
    = surrogateDiagTailX0RatChunk001Sub000Block027Part004

theorem surrogateDiagonalTailChunk001Sub000Block027Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block027Part004CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block027Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block027Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block027Part004CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block027Part004SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block027Part004] using hcert

def TailChunk001Sub000Block027Part005SupportExplicit : Finset ℕ :=
  ([17611] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block027Part005 : ℚ :=
  (19317418897 : ℚ) / 6554910720000000000

def SurrogateDiagonalTailChunk001Sub000Block027Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17611
    = surrogateDiagTailX0RatChunk001Sub000Block027Part005

theorem surrogateDiagonalTailChunk001Sub000Block027Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block027Part005CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block027Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block027Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block027Part005CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block027Part005SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block027Part005] using hcert

def TailChunk001Sub000Block027Part006SupportExplicit : Finset ℕ :=
  ([17614] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block027Part006 : ℚ :=
  (1211925765625 : ℚ) / 3759080204860640562

def SurrogateDiagonalTailChunk001Sub000Block027Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17614
    = surrogateDiagTailX0RatChunk001Sub000Block027Part006

theorem surrogateDiagonalTailChunk001Sub000Block027Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block027Part006CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block027Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block027Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block027Part006CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block027Part006SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block027Part006] using hcert

def TailChunk001Sub000Block027Part007SupportExplicit : Finset ℕ :=
  ([17615] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block027Part007 : ℚ :=
  (64198408273 : ℚ) / 2821674129437491200

def SurrogateDiagonalTailChunk001Sub000Block027Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17615
    = surrogateDiagTailX0RatChunk001Sub000Block027Part007

theorem surrogateDiagonalTailChunk001Sub000Block027Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block027Part007CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block027Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block027Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block027Part007CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block027Part007SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block027Part007] using hcert

def TailChunk001Sub000Block027Part008SupportExplicit : Finset ℕ :=
  ([17617] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block027Part008 : ℚ :=
  (45874490825 : ℚ) / 112405399060681157184

def SurrogateDiagonalTailChunk001Sub000Block027Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17617
    = surrogateDiagTailX0RatChunk001Sub000Block027Part008

theorem surrogateDiagonalTailChunk001Sub000Block027Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block027Part008CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block027Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block027Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block027Part008CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block027Part008SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block027Part008] using hcert

def TailChunk001Sub000Block027Part009SupportExplicit : Finset ℕ :=
  ([17618] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block027Part009 : ℚ :=
  (755199670875 : ℚ) / 2078833866932765888

def SurrogateDiagonalTailChunk001Sub000Block027Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17618
    = surrogateDiagTailX0RatChunk001Sub000Block027Part009

theorem surrogateDiagonalTailChunk001Sub000Block027Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block027Part009CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block027Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block027Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block027Part009CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block027Part009SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block027Part009] using hcert

def TailChunk001Sub000Block027Part010SupportExplicit : Finset ℕ :=
  ([17619] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block027Part010 : ℚ :=
  (35362075 : ℚ) / 1704314772412416

def SurrogateDiagonalTailChunk001Sub000Block027Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17619
    = surrogateDiagTailX0RatChunk001Sub000Block027Part010

theorem surrogateDiagonalTailChunk001Sub000Block027Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block027Part010CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block027Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block027Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block027Part010CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block027Part010SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block027Part010] using hcert

def TailChunk001Sub000Block027Part011SupportExplicit : Finset ℕ :=
  ([17621] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block027Part011 : ℚ :=
  (101945505025 : ℚ) / 223567034585858206848

def SurrogateDiagonalTailChunk001Sub000Block027Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17621
    = surrogateDiagTailX0RatChunk001Sub000Block027Part011

theorem surrogateDiagonalTailChunk001Sub000Block027Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block027Part011CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block027Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block027Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block027Part011CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block027Part011SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block027Part011] using hcert

def TailChunk001Sub000Block027Part012SupportExplicit : Finset ℕ :=
  ([17623] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block027Part012 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block027Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17623
    = surrogateDiagTailX0RatChunk001Sub000Block027Part012

theorem surrogateDiagonalTailChunk001Sub000Block027Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block027Part012CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block027Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block027Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block027Part012CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block027Part012SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block027Part012] using hcert

def TailChunk001Sub000Block027Part013SupportExplicit : Finset ℕ :=
  ([17626] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block027Part013 : ℚ :=
  (214442501075 : ℚ) / 450901748854587456

def SurrogateDiagonalTailChunk001Sub000Block027Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17626
    = surrogateDiagTailX0RatChunk001Sub000Block027Part013

theorem surrogateDiagonalTailChunk001Sub000Block027Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block027Part013CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block027Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block027Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block027Part013CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block027Part013SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block027Part013] using hcert

def TailChunk001Sub000Block027Part014SupportExplicit : Finset ℕ :=
  ([17627] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block027Part014 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block027Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17627
    = surrogateDiagTailX0RatChunk001Sub000Block027Part014

theorem surrogateDiagonalTailChunk001Sub000Block027Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block027Part014CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block027Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block027Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block027Part014CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block027Part014SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block027Part014] using hcert

def TailChunk001Sub000Block027Part015SupportExplicit : Finset ℕ :=
  ([17630] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block027Part015 : ℚ :=
  (130889101351 : ℚ) / 203968894677811200

def SurrogateDiagonalTailChunk001Sub000Block027Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17630
    = surrogateDiagTailX0RatChunk001Sub000Block027Part015

theorem surrogateDiagonalTailChunk001Sub000Block027Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block027Part015CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block027Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block027Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block027Part015CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block027Part015SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block027Part015] using hcert

def TailChunk001Sub000Block027Part016SupportExplicit : Finset ℕ :=
  ([17633] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block027Part016 : ℚ :=
  (23762141729 : ℚ) / 1751464116666777600

def SurrogateDiagonalTailChunk001Sub000Block027Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17633
    = surrogateDiagTailX0RatChunk001Sub000Block027Part016

theorem surrogateDiagonalTailChunk001Sub000Block027Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block027Part016CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block027Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block027Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block027Part016CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block027Part016SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block027Part016] using hcert

def TailChunk001Sub000Block027Part017SupportExplicit : Finset ℕ :=
  ([17634] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block027Part017 : ℚ :=
  (2158585706125 : ℚ) / 2980945303460162688

def SurrogateDiagonalTailChunk001Sub000Block027Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17634
    = surrogateDiagTailX0RatChunk001Sub000Block027Part017

theorem surrogateDiagonalTailChunk001Sub000Block027Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block027Part017CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block027Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block027Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block027Part017CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block027Part017SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block027Part017] using hcert

def TailChunk001Sub000Block027Part018SupportExplicit : Finset ℕ :=
  ([17635] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block027Part018 : ℚ :=
  (1555023750025 : ℚ) / 98945501956787324928

def SurrogateDiagonalTailChunk001Sub000Block027Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17635
    = surrogateDiagTailX0RatChunk001Sub000Block027Part018

theorem surrogateDiagonalTailChunk001Sub000Block027Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block027Part018CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block027Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block027Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block027Part018CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block027Part018SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block027Part018] using hcert

def TailChunk001Sub000Block027Part019SupportExplicit : Finset ℕ :=
  ([17637] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block027Part019 : ℚ :=
  (125025 : ℚ) / 9550108681451648

def SurrogateDiagonalTailChunk001Sub000Block027Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17637
    = surrogateDiagTailX0RatChunk001Sub000Block027Part019

theorem surrogateDiagonalTailChunk001Sub000Block027Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block027Part019CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block027Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block027Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block027Part019CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block027Part019SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block027Part019] using hcert

def TailChunk001Sub000Block027Part020SupportExplicit : Finset ℕ :=
  ([17638] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block027Part020 : ℚ :=
  (1215230640625 : ℚ) / 3779612229261203922

def SurrogateDiagonalTailChunk001Sub000Block027Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17638
    = surrogateDiagTailX0RatChunk001Sub000Block027Part020

theorem surrogateDiagonalTailChunk001Sub000Block027Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block027Part020CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block027Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block027Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block027Part020CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block027Part020SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block027Part020] using hcert

def TailChunk001Sub000Block027Part021SupportExplicit : Finset ℕ :=
  ([17639] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block027Part021 : ℚ :=
  (7621833013 : ℚ) / 8432672072631091200

def SurrogateDiagonalTailChunk001Sub000Block027Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17639
    = surrogateDiagTailX0RatChunk001Sub000Block027Part021

theorem surrogateDiagonalTailChunk001Sub000Block027Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block027Part021CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block027Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block027Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block027Part021CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block027Part021SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block027Part021] using hcert

def TailChunk001Sub000Block027Part022SupportExplicit : Finset ℕ :=
  ([17641] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block027Part022 : ℚ :=
  (29728077325 : ℚ) / 5727212521329733632

def SurrogateDiagonalTailChunk001Sub000Block027Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17641
    = surrogateDiagTailX0RatChunk001Sub000Block027Part022

theorem surrogateDiagonalTailChunk001Sub000Block027Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block027Part022CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block027Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block027Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block027Part022CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block027Part022SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block027Part022] using hcert

def TailChunk001Sub000Block027Part023SupportExplicit : Finset ℕ :=
  ([17642] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block027Part023 : ℚ :=
  (1945251025 : ℚ) / 6052867829259552

def SurrogateDiagonalTailChunk001Sub000Block027Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17642
    = surrogateDiagTailX0RatChunk001Sub000Block027Part023

theorem surrogateDiagonalTailChunk001Sub000Block027Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block027Part023CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block027Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block027Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block027Part023CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block027Part023SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block027Part023] using hcert

def TailChunk001Sub000Block027Part024SupportExplicit : Finset ℕ :=
  ([17643] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block027Part024 : ℚ :=
  (1667 : ℚ) / 127508174438400

def SurrogateDiagonalTailChunk001Sub000Block027Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17643
    = surrogateDiagTailX0RatChunk001Sub000Block027Part024

theorem surrogateDiagonalTailChunk001Sub000Block027Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block027Part024CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block027Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block027Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block027Part024CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block027Part024SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block027Part024] using hcert

def surrogateDiagonalTailChunk001Sub000Block027HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block027Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block027Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block027Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block027Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block027Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block027Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block027Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block027Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block027Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block027Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block027Head : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block027Part000
    + surrogateDiagTailX0RatChunk001Sub000Block027Part001
    + surrogateDiagTailX0RatChunk001Sub000Block027Part002
    + surrogateDiagTailX0RatChunk001Sub000Block027Part003
    + surrogateDiagTailX0RatChunk001Sub000Block027Part004
    + surrogateDiagTailX0RatChunk001Sub000Block027Part005
    + surrogateDiagTailX0RatChunk001Sub000Block027Part006
    + surrogateDiagTailX0RatChunk001Sub000Block027Part007
    + surrogateDiagTailX0RatChunk001Sub000Block027Part008
    + surrogateDiagTailX0RatChunk001Sub000Block027Part009

def surrogateDiagonalTailChunk001Sub000Block027MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block027Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block027Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block027Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block027Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block027Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block027Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block027Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block027Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block027Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block027Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block027Mid : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block027Part010
    + surrogateDiagTailX0RatChunk001Sub000Block027Part011
    + surrogateDiagTailX0RatChunk001Sub000Block027Part012
    + surrogateDiagTailX0RatChunk001Sub000Block027Part013
    + surrogateDiagTailX0RatChunk001Sub000Block027Part014
    + surrogateDiagTailX0RatChunk001Sub000Block027Part015
    + surrogateDiagTailX0RatChunk001Sub000Block027Part016
    + surrogateDiagTailX0RatChunk001Sub000Block027Part017
    + surrogateDiagTailX0RatChunk001Sub000Block027Part018
    + surrogateDiagTailX0RatChunk001Sub000Block027Part019

def surrogateDiagonalTailChunk001Sub000Block027TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block027Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block027Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block027Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block027Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block027Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block027Tail : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block027Part020
    + surrogateDiagTailX0RatChunk001Sub000Block027Part021
    + surrogateDiagTailX0RatChunk001Sub000Block027Part022
    + surrogateDiagTailX0RatChunk001Sub000Block027Part023
    + surrogateDiagTailX0RatChunk001Sub000Block027Part024

def surrogateDiagonalTailChunk001Sub000Block027Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk001Sub000Block027HeadSum X0
    + surrogateDiagonalTailChunk001Sub000Block027MidSum X0
    + surrogateDiagonalTailChunk001Sub000Block027TailSum X0

def surrogateDiagTailX0RatChunk001Sub000Block027 : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block027Part000
    + surrogateDiagTailX0RatChunk001Sub000Block027Part001
    + surrogateDiagTailX0RatChunk001Sub000Block027Part002
    + surrogateDiagTailX0RatChunk001Sub000Block027Part003
    + surrogateDiagTailX0RatChunk001Sub000Block027Part004
    + surrogateDiagTailX0RatChunk001Sub000Block027Part005
    + surrogateDiagTailX0RatChunk001Sub000Block027Part006
    + surrogateDiagTailX0RatChunk001Sub000Block027Part007
    + surrogateDiagTailX0RatChunk001Sub000Block027Part008
    + surrogateDiagTailX0RatChunk001Sub000Block027Part009
    + surrogateDiagTailX0RatChunk001Sub000Block027Part010
    + surrogateDiagTailX0RatChunk001Sub000Block027Part011
    + surrogateDiagTailX0RatChunk001Sub000Block027Part012
    + surrogateDiagTailX0RatChunk001Sub000Block027Part013
    + surrogateDiagTailX0RatChunk001Sub000Block027Part014
    + surrogateDiagTailX0RatChunk001Sub000Block027Part015
    + surrogateDiagTailX0RatChunk001Sub000Block027Part016
    + surrogateDiagTailX0RatChunk001Sub000Block027Part017
    + surrogateDiagTailX0RatChunk001Sub000Block027Part018
    + surrogateDiagTailX0RatChunk001Sub000Block027Part019
    + surrogateDiagTailX0RatChunk001Sub000Block027Part020
    + surrogateDiagTailX0RatChunk001Sub000Block027Part021
    + surrogateDiagTailX0RatChunk001Sub000Block027Part022
    + surrogateDiagTailX0RatChunk001Sub000Block027Part023
    + surrogateDiagTailX0RatChunk001Sub000Block027Part024

theorem surrogateDiagTailX0RatChunk001Sub000Block027_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk001Sub000Block027Head + surrogateDiagTailX0RatChunk001Sub000Block027Mid + surrogateDiagTailX0RatChunk001Sub000Block027Tail =
      surrogateDiagTailX0RatChunk001Sub000Block027 := by
  unfold surrogateDiagTailX0RatChunk001Sub000Block027Head surrogateDiagTailX0RatChunk001Sub000Block027Mid surrogateDiagTailX0RatChunk001Sub000Block027Tail surrogateDiagTailX0RatChunk001Sub000Block027
  ring

def SurrogateDiagonalTailChunk001Sub000Block027HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block027HeadSum X0 = surrogateDiagTailX0RatChunk001Sub000Block027Head

def SurrogateDiagonalTailChunk001Sub000Block027MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block027MidSum X0 = surrogateDiagTailX0RatChunk001Sub000Block027Mid

def SurrogateDiagonalTailChunk001Sub000Block027TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block027TailSum X0 = surrogateDiagTailX0RatChunk001Sub000Block027Tail

theorem surrogateDiagonalTailChunk001Sub000Block027_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk001Sub000Block027HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk001Sub000Block027MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk001Sub000Block027TailCertificateAt X0) :
    surrogateDiagonalTailChunk001Sub000Block027Sum X0 = surrogateDiagTailX0RatChunk001Sub000Block027 := by
  unfold SurrogateDiagonalTailChunk001Sub000Block027HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk001Sub000Block027MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk001Sub000Block027TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk001Sub000Block027Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk001Sub000Block027_eq_head_add_mid_add_tail

/-- Block 028 covers tail-support indices [10700,10725) and q from 17645 to 17687. -/

def TailChunk001Sub000Block028Part000SupportExplicit : Finset ℕ :=
  ([17645] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block028Part000 : ℚ :=
  (518928965575 : ℚ) / 33056728838196166656

def SurrogateDiagonalTailChunk001Sub000Block028Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17645
    = surrogateDiagTailX0RatChunk001Sub000Block028Part000

theorem surrogateDiagonalTailChunk001Sub000Block028Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block028Part000CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block028Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block028Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block028Part000CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block028Part000SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block028Part000] using hcert

def TailChunk001Sub000Block028Part001SupportExplicit : Finset ℕ :=
  ([17646] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block028Part001 : ℚ :=
  (668331176325 : ℚ) / 764925792407781376

def SurrogateDiagonalTailChunk001Sub000Block028Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17646
    = surrogateDiagTailX0RatChunk001Sub000Block028Part001

theorem surrogateDiagonalTailChunk001Sub000Block028Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block028Part001CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block028Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block028Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block028Part001CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block028Part001SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block028Part001] using hcert

def TailChunk001Sub000Block028Part002SupportExplicit : Finset ℕ :=
  ([17647] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block028Part002 : ℚ :=
  (15910321067 : ℚ) / 2613749839806873600

def SurrogateDiagonalTailChunk001Sub000Block028Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17647
    = surrogateDiagTailX0RatChunk001Sub000Block028Part002

theorem surrogateDiagonalTailChunk001Sub000Block028Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block028Part002CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block028Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block028Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block028Part002CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block028Part002SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block028Part002] using hcert

def TailChunk001Sub000Block028Part003SupportExplicit : Finset ℕ :=
  ([17651] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block028Part003 : ℚ :=
  (5719318225 : ℚ) / 4055716100071489536

def SurrogateDiagonalTailChunk001Sub000Block028Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17651
    = surrogateDiagTailX0RatChunk001Sub000Block028Part003

theorem surrogateDiagonalTailChunk001Sub000Block028Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block028Part003CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block028Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block028Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block028Part003CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block028Part003SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block028Part003] using hcert

def TailChunk001Sub000Block028Part004SupportExplicit : Finset ℕ :=
  ([17653] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block028Part004 : ℚ :=
  (9062663525 : ℚ) / 25397026698659559552

def SurrogateDiagonalTailChunk001Sub000Block028Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17653
    = surrogateDiagTailX0RatChunk001Sub000Block028Part004

theorem surrogateDiagonalTailChunk001Sub000Block028Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block028Part004CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block028Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block028Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block028Part004CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block028Part004SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block028Part004] using hcert

def TailChunk001Sub000Block028Part005SupportExplicit : Finset ℕ :=
  ([17654] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block028Part005 : ℚ :=
  (378450098875 : ℚ) / 634160616415690752

def SurrogateDiagonalTailChunk001Sub000Block028Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17654
    = surrogateDiagTailX0RatChunk001Sub000Block028Part005

theorem surrogateDiagonalTailChunk001Sub000Block028Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block028Part005CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block028Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block028Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block028Part005CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block028Part005SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block028Part005] using hcert

def TailChunk001Sub000Block028Part006SupportExplicit : Finset ℕ :=
  ([17655] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block028Part006 : ℚ :=
  (39405431 : ℚ) / 243968860815360

def SurrogateDiagonalTailChunk001Sub000Block028Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17655
    = surrogateDiagTailX0RatChunk001Sub000Block028Part006

theorem surrogateDiagonalTailChunk001Sub000Block028Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block028Part006CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block028Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block028Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block028Part006CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block028Part006SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block028Part006] using hcert

def TailChunk001Sub000Block028Part007SupportExplicit : Finset ℕ :=
  ([17657] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block028Part007 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block028Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17657
    = surrogateDiagTailX0RatChunk001Sub000Block028Part007

theorem surrogateDiagonalTailChunk001Sub000Block028Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block028Part007CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block028Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block028Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block028Part007CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block028Part007SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block028Part007] using hcert

def TailChunk001Sub000Block028Part008SupportExplicit : Finset ℕ :=
  ([17659] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block028Part008 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block028Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17659
    = surrogateDiagTailX0RatChunk001Sub000Block028Part008

theorem surrogateDiagonalTailChunk001Sub000Block028Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block028Part008CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block028Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block028Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block028Part008CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block028Part008SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block028Part008] using hcert

def TailChunk001Sub000Block028Part009SupportExplicit : Finset ℕ :=
  ([17662] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block028Part009 : ℚ :=
  (1949664025 : ℚ) / 6080365197083442

def SurrogateDiagonalTailChunk001Sub000Block028Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17662
    = surrogateDiagTailX0RatChunk001Sub000Block028Part009

theorem surrogateDiagonalTailChunk001Sub000Block028Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block028Part009CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block028Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block028Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block028Part009CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block028Part009SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block028Part009] using hcert

def TailChunk001Sub000Block028Part010SupportExplicit : Finset ℕ :=
  ([17663] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block028Part010 : ℚ :=
  (341430504025 : ℚ) / 190237532201062760448

def SurrogateDiagonalTailChunk001Sub000Block028Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17663
    = surrogateDiagTailX0RatChunk001Sub000Block028Part010

theorem surrogateDiagonalTailChunk001Sub000Block028Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block028Part010CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block028Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block028Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block028Part010CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block028Part010SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block028Part010] using hcert

def TailChunk001Sub000Block028Part011SupportExplicit : Finset ℕ :=
  ([17665] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block028Part011 : ℚ :=
  (260313248625 : ℚ) / 33206901129671704576

def SurrogateDiagonalTailChunk001Sub000Block028Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17665
    = surrogateDiagTailX0RatChunk001Sub000Block028Part011

theorem surrogateDiagonalTailChunk001Sub000Block028Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block028Part011CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block028Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block028Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block028Part011CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block028Part011SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block028Part011] using hcert

def TailChunk001Sub000Block028Part012SupportExplicit : Finset ℕ :=
  ([17669] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block028Part012 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block028Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17669
    = surrogateDiagTailX0RatChunk001Sub000Block028Part012

theorem surrogateDiagonalTailChunk001Sub000Block028Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block028Part012CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block028Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block028Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block028Part012CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block028Part012SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block028Part012] using hcert

def TailChunk001Sub000Block028Part013SupportExplicit : Finset ℕ :=
  ([17670] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block028Part013 : ℚ :=
  (72246469153 : ℚ) / 34835483079475200

def SurrogateDiagonalTailChunk001Sub000Block028Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17670
    = surrogateDiagTailX0RatChunk001Sub000Block028Part013

theorem surrogateDiagonalTailChunk001Sub000Block028Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block028Part013CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block028Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block028Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block028Part013CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block028Part013SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block028Part013] using hcert

def TailChunk001Sub000Block028Part014SupportExplicit : Finset ℕ :=
  ([17671] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block028Part014 : ℚ :=
  (2787396851 : ℚ) / 4376940493056000000

def SurrogateDiagonalTailChunk001Sub000Block028Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17671
    = surrogateDiagTailX0RatChunk001Sub000Block028Part014

theorem surrogateDiagonalTailChunk001Sub000Block028Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block028Part014CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block028Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block028Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block028Part014CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block028Part014SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block028Part014] using hcert

def TailChunk001Sub000Block028Part015SupportExplicit : Finset ℕ :=
  ([17673] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block028Part015 : ℚ :=
  (14921709275 : ℚ) / 295758438409469952

def SurrogateDiagonalTailChunk001Sub000Block028Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17673
    = surrogateDiagTailX0RatChunk001Sub000Block028Part015

theorem surrogateDiagonalTailChunk001Sub000Block028Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block028Part015CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block028Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block028Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block028Part015CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block028Part015SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block028Part015] using hcert

def TailChunk001Sub000Block028Part016SupportExplicit : Finset ℕ :=
  ([17674] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block028Part016 : ℚ :=
  (1220196390625 : ℚ) / 3810567827054936352

def SurrogateDiagonalTailChunk001Sub000Block028Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17674
    = surrogateDiagTailX0RatChunk001Sub000Block028Part016

theorem surrogateDiagonalTailChunk001Sub000Block028Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block028Part016CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block028Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block028Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block028Part016CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block028Part016SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block028Part016] using hcert

def TailChunk001Sub000Block028Part017SupportExplicit : Finset ℕ :=
  ([17677] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block028Part017 : ℚ :=
  (19461631063 : ℚ) / 6653788835364739200

def SurrogateDiagonalTailChunk001Sub000Block028Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17677
    = surrogateDiagTailX0RatChunk001Sub000Block028Part017

theorem surrogateDiagonalTailChunk001Sub000Block028Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block028Part017CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block028Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block028Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block028Part017CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block028Part017SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block028Part017] using hcert

def TailChunk001Sub000Block028Part018SupportExplicit : Finset ℕ :=
  ([17678] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block028Part018 : ℚ :=
  (1220748765625 : ℚ) / 3814019037364427442

def SurrogateDiagonalTailChunk001Sub000Block028Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17678
    = surrogateDiagTailX0RatChunk001Sub000Block028Part018

theorem surrogateDiagonalTailChunk001Sub000Block028Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block028Part018CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block028Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block028Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block028Part018CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block028Part018SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block028Part018] using hcert

def TailChunk001Sub000Block028Part019SupportExplicit : Finset ℕ :=
  ([17679] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block028Part019 : ℚ :=
  (2690141219 : ℚ) / 54288072731457600

def SurrogateDiagonalTailChunk001Sub000Block028Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17679
    = surrogateDiagTailX0RatChunk001Sub000Block028Part019

theorem surrogateDiagonalTailChunk001Sub000Block028Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block028Part019CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block028Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block028Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block028Part019CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block028Part019SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block028Part019] using hcert

def TailChunk001Sub000Block028Part020SupportExplicit : Finset ℕ :=
  ([17681] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block028Part020 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block028Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17681
    = surrogateDiagTailX0RatChunk001Sub000Block028Part020

theorem surrogateDiagonalTailChunk001Sub000Block028Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block028Part020CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block028Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block028Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block028Part020CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block028Part020SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block028Part020] using hcert

def TailChunk001Sub000Block028Part021SupportExplicit : Finset ℕ :=
  ([17682] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block028Part021 : ℚ :=
  (87921696787 : ℚ) / 64537033081651200

def SurrogateDiagonalTailChunk001Sub000Block028Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17682
    = surrogateDiagTailX0RatChunk001Sub000Block028Part021

theorem surrogateDiagonalTailChunk001Sub000Block028Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block028Part021CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block028Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block028Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block028Part021CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block028Part021SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block028Part021] using hcert

def TailChunk001Sub000Block028Part022SupportExplicit : Finset ℕ :=
  ([17683] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block028Part022 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block028Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17683
    = surrogateDiagTailX0RatChunk001Sub000Block028Part022

theorem surrogateDiagonalTailChunk001Sub000Block028Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block028Part022CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block028Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block028Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block028Part022CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block028Part022SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block028Part022] using hcert

def TailChunk001Sub000Block028Part023SupportExplicit : Finset ℕ :=
  ([17686] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block028Part023 : ℚ :=
  (4667312045125 : ℚ) / 13475493850031474688

def SurrogateDiagonalTailChunk001Sub000Block028Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17686
    = surrogateDiagTailX0RatChunk001Sub000Block028Part023

theorem surrogateDiagonalTailChunk001Sub000Block028Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block028Part023CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block028Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block028Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block028Part023CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block028Part023SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block028Part023] using hcert

def TailChunk001Sub000Block028Part024SupportExplicit : Finset ℕ :=
  ([17687] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block028Part024 : ℚ :=
  (227827524175 : ℚ) / 203780424360869756928

def SurrogateDiagonalTailChunk001Sub000Block028Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17687
    = surrogateDiagTailX0RatChunk001Sub000Block028Part024

theorem surrogateDiagonalTailChunk001Sub000Block028Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block028Part024CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block028Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block028Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block028Part024CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block028Part024SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block028Part024] using hcert

def surrogateDiagonalTailChunk001Sub000Block028HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block028Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block028Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block028Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block028Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block028Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block028Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block028Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block028Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block028Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block028Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block028Head : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block028Part000
    + surrogateDiagTailX0RatChunk001Sub000Block028Part001
    + surrogateDiagTailX0RatChunk001Sub000Block028Part002
    + surrogateDiagTailX0RatChunk001Sub000Block028Part003
    + surrogateDiagTailX0RatChunk001Sub000Block028Part004
    + surrogateDiagTailX0RatChunk001Sub000Block028Part005
    + surrogateDiagTailX0RatChunk001Sub000Block028Part006
    + surrogateDiagTailX0RatChunk001Sub000Block028Part007
    + surrogateDiagTailX0RatChunk001Sub000Block028Part008
    + surrogateDiagTailX0RatChunk001Sub000Block028Part009

def surrogateDiagonalTailChunk001Sub000Block028MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block028Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block028Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block028Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block028Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block028Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block028Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block028Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block028Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block028Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block028Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block028Mid : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block028Part010
    + surrogateDiagTailX0RatChunk001Sub000Block028Part011
    + surrogateDiagTailX0RatChunk001Sub000Block028Part012
    + surrogateDiagTailX0RatChunk001Sub000Block028Part013
    + surrogateDiagTailX0RatChunk001Sub000Block028Part014
    + surrogateDiagTailX0RatChunk001Sub000Block028Part015
    + surrogateDiagTailX0RatChunk001Sub000Block028Part016
    + surrogateDiagTailX0RatChunk001Sub000Block028Part017
    + surrogateDiagTailX0RatChunk001Sub000Block028Part018
    + surrogateDiagTailX0RatChunk001Sub000Block028Part019

def surrogateDiagonalTailChunk001Sub000Block028TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block028Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block028Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block028Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block028Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block028Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block028Tail : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block028Part020
    + surrogateDiagTailX0RatChunk001Sub000Block028Part021
    + surrogateDiagTailX0RatChunk001Sub000Block028Part022
    + surrogateDiagTailX0RatChunk001Sub000Block028Part023
    + surrogateDiagTailX0RatChunk001Sub000Block028Part024

def surrogateDiagonalTailChunk001Sub000Block028Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk001Sub000Block028HeadSum X0
    + surrogateDiagonalTailChunk001Sub000Block028MidSum X0
    + surrogateDiagonalTailChunk001Sub000Block028TailSum X0

def surrogateDiagTailX0RatChunk001Sub000Block028 : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block028Part000
    + surrogateDiagTailX0RatChunk001Sub000Block028Part001
    + surrogateDiagTailX0RatChunk001Sub000Block028Part002
    + surrogateDiagTailX0RatChunk001Sub000Block028Part003
    + surrogateDiagTailX0RatChunk001Sub000Block028Part004
    + surrogateDiagTailX0RatChunk001Sub000Block028Part005
    + surrogateDiagTailX0RatChunk001Sub000Block028Part006
    + surrogateDiagTailX0RatChunk001Sub000Block028Part007
    + surrogateDiagTailX0RatChunk001Sub000Block028Part008
    + surrogateDiagTailX0RatChunk001Sub000Block028Part009
    + surrogateDiagTailX0RatChunk001Sub000Block028Part010
    + surrogateDiagTailX0RatChunk001Sub000Block028Part011
    + surrogateDiagTailX0RatChunk001Sub000Block028Part012
    + surrogateDiagTailX0RatChunk001Sub000Block028Part013
    + surrogateDiagTailX0RatChunk001Sub000Block028Part014
    + surrogateDiagTailX0RatChunk001Sub000Block028Part015
    + surrogateDiagTailX0RatChunk001Sub000Block028Part016
    + surrogateDiagTailX0RatChunk001Sub000Block028Part017
    + surrogateDiagTailX0RatChunk001Sub000Block028Part018
    + surrogateDiagTailX0RatChunk001Sub000Block028Part019
    + surrogateDiagTailX0RatChunk001Sub000Block028Part020
    + surrogateDiagTailX0RatChunk001Sub000Block028Part021
    + surrogateDiagTailX0RatChunk001Sub000Block028Part022
    + surrogateDiagTailX0RatChunk001Sub000Block028Part023
    + surrogateDiagTailX0RatChunk001Sub000Block028Part024

theorem surrogateDiagTailX0RatChunk001Sub000Block028_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk001Sub000Block028Head + surrogateDiagTailX0RatChunk001Sub000Block028Mid + surrogateDiagTailX0RatChunk001Sub000Block028Tail =
      surrogateDiagTailX0RatChunk001Sub000Block028 := by
  unfold surrogateDiagTailX0RatChunk001Sub000Block028Head surrogateDiagTailX0RatChunk001Sub000Block028Mid surrogateDiagTailX0RatChunk001Sub000Block028Tail surrogateDiagTailX0RatChunk001Sub000Block028
  ring

def SurrogateDiagonalTailChunk001Sub000Block028HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block028HeadSum X0 = surrogateDiagTailX0RatChunk001Sub000Block028Head

def SurrogateDiagonalTailChunk001Sub000Block028MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block028MidSum X0 = surrogateDiagTailX0RatChunk001Sub000Block028Mid

def SurrogateDiagonalTailChunk001Sub000Block028TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block028TailSum X0 = surrogateDiagTailX0RatChunk001Sub000Block028Tail

theorem surrogateDiagonalTailChunk001Sub000Block028_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk001Sub000Block028HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk001Sub000Block028MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk001Sub000Block028TailCertificateAt X0) :
    surrogateDiagonalTailChunk001Sub000Block028Sum X0 = surrogateDiagTailX0RatChunk001Sub000Block028 := by
  unfold SurrogateDiagonalTailChunk001Sub000Block028HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk001Sub000Block028MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk001Sub000Block028TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk001Sub000Block028Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk001Sub000Block028_eq_head_add_mid_add_tail

/-- Block 029 covers tail-support indices [10725,10750) and q from 17690 to 17727. -/

def TailChunk001Sub000Block029Part000SupportExplicit : Finset ℕ :=
  ([17690] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block029Part000 : ℚ :=
  (131112306961 : ℚ) / 203968894677811200

def SurrogateDiagonalTailChunk001Sub000Block029Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17690
    = surrogateDiagTailX0RatChunk001Sub000Block029Part000

theorem surrogateDiagonalTailChunk001Sub000Block029Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block029Part000CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block029Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block029Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block029Part000CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block029Part000SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block029Part000] using hcert

def TailChunk001Sub000Block029Part001SupportExplicit : Finset ℕ :=
  ([17691] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block029Part001 : ℚ :=
  (543325260025 : ℚ) / 12086950669251059712

def SurrogateDiagonalTailChunk001Sub000Block029Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17691
    = surrogateDiagTailX0RatChunk001Sub000Block029Part001

theorem surrogateDiagonalTailChunk001Sub000Block029Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block029Part001CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block029Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block029Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block029Part001CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block029Part001SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block029Part001] using hcert

def TailChunk001Sub000Block029Part002SupportExplicit : Finset ℕ :=
  ([17693] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block029Part002 : ℚ :=
  (3105836479 : ℚ) / 1182541028209459200

def SurrogateDiagonalTailChunk001Sub000Block029Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17693
    = surrogateDiagTailX0RatChunk001Sub000Block029Part002

theorem surrogateDiagonalTailChunk001Sub000Block029Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block029Part002CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block029Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block029Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block029Part002CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block029Part002SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block029Part002] using hcert

def TailChunk001Sub000Block029Part003SupportExplicit : Finset ℕ :=
  ([17695] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block029Part003 : ℚ :=
  (261196998375 : ℚ) / 33433118202452187136

def SurrogateDiagonalTailChunk001Sub000Block029Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17695
    = surrogateDiagTailX0RatChunk001Sub000Block029Part003

theorem surrogateDiagonalTailChunk001Sub000Block029Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block029Part003CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block029Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block029Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block029Part003CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block029Part003SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block029Part003] using hcert

def TailChunk001Sub000Block029Part004SupportExplicit : Finset ℕ :=
  ([17697] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block029Part004 : ℚ :=
  (1071206659475 : ℚ) / 18788892069240766464

def SurrogateDiagonalTailChunk001Sub000Block029Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17697
    = surrogateDiagTailX0RatChunk001Sub000Block029Part004

theorem surrogateDiagonalTailChunk001Sub000Block029Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block029Part004CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block029Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block029Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block029Part004CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block029Part004SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block029Part004] using hcert

def TailChunk001Sub000Block029Part005SupportExplicit : Finset ℕ :=
  ([17698] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block029Part005 : ℚ :=
  (1223512515625 : ℚ) / 3831310266773348352

def SurrogateDiagonalTailChunk001Sub000Block029Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17698
    = surrogateDiagTailX0RatChunk001Sub000Block029Part005

theorem surrogateDiagonalTailChunk001Sub000Block029Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block029Part005CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block029Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block029Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block029Part005CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block029Part005SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block029Part005] using hcert

def TailChunk001Sub000Block029Part006SupportExplicit : Finset ℕ :=
  ([17699] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block029Part006 : ℚ :=
  (19509821737 : ℚ) / 6686995452560179200

def SurrogateDiagonalTailChunk001Sub000Block029Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17699
    = surrogateDiagTailX0RatChunk001Sub000Block029Part006

theorem surrogateDiagonalTailChunk001Sub000Block029Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block029Part006CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block029Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block029Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block029Part006CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block029Part006SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block029Part006] using hcert

def TailChunk001Sub000Block029Part007SupportExplicit : Finset ℕ :=
  ([17701] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block029Part007 : ℚ :=
  (1534592219 : ℚ) / 1710414176432400000

def SurrogateDiagonalTailChunk001Sub000Block029Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17701
    = surrogateDiagTailX0RatChunk001Sub000Block029Part007

theorem surrogateDiagonalTailChunk001Sub000Block029Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block029Part007CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block029Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block029Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block029Part007CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block029Part007SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block029Part007] using hcert

def TailChunk001Sub000Block029Part008SupportExplicit : Finset ℕ :=
  ([17702] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block029Part008 : ℚ :=
  (4722124742125 : ℚ) / 13882656742422693888

def SurrogateDiagonalTailChunk001Sub000Block029Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17702
    = surrogateDiagTailX0RatChunk001Sub000Block029Part008

theorem surrogateDiagonalTailChunk001Sub000Block029Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block029Part008CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block029Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block029Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block029Part008CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block029Part008SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block029Part008] using hcert

def TailChunk001Sub000Block029Part009SupportExplicit : Finset ℕ :=
  ([17705] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block029Part009 : ℚ :=
  (6275805959 : ℚ) / 804210722609725440

def SurrogateDiagonalTailChunk001Sub000Block029Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17705
    = surrogateDiagTailX0RatChunk001Sub000Block029Part009

theorem surrogateDiagonalTailChunk001Sub000Block029Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block029Part009CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block029Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block029Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block029Part009CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block029Part009SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block029Part009] using hcert

def TailChunk001Sub000Block029Part010SupportExplicit : Finset ℕ :=
  ([17706] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block029Part010 : ℚ :=
  (2427534341725 : ℚ) / 2164240811335385088

def SurrogateDiagonalTailChunk001Sub000Block029Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17706
    = surrogateDiagTailX0RatChunk001Sub000Block029Part010

theorem surrogateDiagonalTailChunk001Sub000Block029Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block029Part010CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block029Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block029Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block029Part010CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block029Part010SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block029Part010] using hcert

def TailChunk001Sub000Block029Part011SupportExplicit : Finset ℕ :=
  ([17707] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block029Part011 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block029Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17707
    = surrogateDiagTailX0RatChunk001Sub000Block029Part011

theorem surrogateDiagonalTailChunk001Sub000Block029Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block029Part011CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block029Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block029Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block029Part011CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block029Part011SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block029Part011] using hcert

def TailChunk001Sub000Block029Part012SupportExplicit : Finset ℕ :=
  ([17709] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block029Part012 : ℚ :=
  (1088862644975 : ℚ) / 24272452872446835264

def SurrogateDiagonalTailChunk001Sub000Block029Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17709
    = surrogateDiagTailX0RatChunk001Sub000Block029Part012

theorem surrogateDiagonalTailChunk001Sub000Block029Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block029Part012CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block029Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block029Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block029Part012CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block029Part012SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block029Part012] using hcert

def TailChunk001Sub000Block029Part013SupportExplicit : Finset ℕ :=
  ([17710] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block029Part013 : ℚ :=
  (94062502351 : ℚ) / 77736062759731200

def SurrogateDiagonalTailChunk001Sub000Block029Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17710
    = surrogateDiagTailX0RatChunk001Sub000Block029Part013

theorem surrogateDiagonalTailChunk001Sub000Block029Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block029Part013CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block029Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block029Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block029Part013CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block029Part013SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block029Part013] using hcert

def TailChunk001Sub000Block029Part014SupportExplicit : Finset ℕ :=
  ([17711] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block029Part014 : ℚ :=
  (88851115225 : ℚ) / 230472073210207961088

def SurrogateDiagonalTailChunk001Sub000Block029Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17711
    = surrogateDiagTailX0RatChunk001Sub000Block029Part014

theorem surrogateDiagonalTailChunk001Sub000Block029Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block029Part014CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block029Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block029Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block029Part014CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block029Part014SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block029Part014] using hcert

def TailChunk001Sub000Block029Part015SupportExplicit : Finset ℕ :=
  ([17713] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block029Part015 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block029Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17713
    = surrogateDiagTailX0RatChunk001Sub000Block029Part015

theorem surrogateDiagonalTailChunk001Sub000Block029Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block029Part015CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block029Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block029Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block029Part015CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block029Part015SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block029Part015] using hcert

def TailChunk001Sub000Block029Part016SupportExplicit : Finset ℕ :=
  ([17714] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block029Part016 : ℚ :=
  (179368471603 : ℚ) / 479269900989235200

def SurrogateDiagonalTailChunk001Sub000Block029Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17714
    = surrogateDiagTailX0RatChunk001Sub000Block029Part016

theorem surrogateDiagonalTailChunk001Sub000Block029Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block029Part016CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block029Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block029Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block029Part016CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block029Part016SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block029Part016] using hcert

def TailChunk001Sub000Block029Part017SupportExplicit : Finset ℕ :=
  ([17715] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block029Part017 : ℚ :=
  (19171543873 : ℚ) / 198570548792524800

def SurrogateDiagonalTailChunk001Sub000Block029Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17715
    = surrogateDiagTailX0RatChunk001Sub000Block029Part017

theorem surrogateDiagonalTailChunk001Sub000Block029Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block029Part017CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block029Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block029Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block029Part017CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block029Part017SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block029Part017] using hcert

def TailChunk001Sub000Block029Part018SupportExplicit : Finset ℕ :=
  ([17717] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block029Part018 : ℚ :=
  (16036545827 : ℚ) / 2655485539397697600

def SurrogateDiagonalTailChunk001Sub000Block029Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17717
    = surrogateDiagTailX0RatChunk001Sub000Block029Part018

theorem surrogateDiagonalTailChunk001Sub000Block029Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block029Part018CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block029Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block029Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block029Part018CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block029Part018SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block029Part018] using hcert

def TailChunk001Sub000Block029Part019SupportExplicit : Finset ℕ :=
  ([17718] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block029Part019 : ℚ :=
  (1362140289425 : ℚ) / 1519085640465137664

def SurrogateDiagonalTailChunk001Sub000Block029Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17718
    = surrogateDiagTailX0RatChunk001Sub000Block029Part019

theorem surrogateDiagonalTailChunk001Sub000Block029Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block029Part019CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block029Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block029Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block029Part019CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block029Part019SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block029Part019] using hcert

def TailChunk001Sub000Block029Part020SupportExplicit : Finset ℕ :=
  ([17719] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block029Part020 : ℚ :=
  (682180899625 : ℚ) / 142697148638833410048

def SurrogateDiagonalTailChunk001Sub000Block029Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17719
    = surrogateDiagTailX0RatChunk001Sub000Block029Part020

theorem surrogateDiagonalTailChunk001Sub000Block029Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block029Part020CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block029Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block029Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block029Part020CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block029Part020SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block029Part020] using hcert

def TailChunk001Sub000Block029Part021SupportExplicit : Finset ℕ :=
  ([17722] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block029Part021 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block029Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17722
    = surrogateDiagTailX0RatChunk001Sub000Block029Part021

theorem surrogateDiagonalTailChunk001Sub000Block029Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block029Part021CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block029Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block029Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block029Part021CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block029Part021SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block029Part021] using hcert

def TailChunk001Sub000Block029Part022SupportExplicit : Finset ℕ :=
  ([17723] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block029Part022 : ℚ :=
  (168008612125 : ℚ) / 219254466059261134848

def SurrogateDiagonalTailChunk001Sub000Block029Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17723
    = surrogateDiagTailX0RatChunk001Sub000Block029Part022

theorem surrogateDiagonalTailChunk001Sub000Block029Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block029Part022CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block029Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block029Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block029Part022CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block029Part022SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block029Part022] using hcert

def TailChunk001Sub000Block029Part023SupportExplicit : Finset ℕ :=
  ([17726] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block029Part023 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block029Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17726
    = surrogateDiagTailX0RatChunk001Sub000Block029Part023

theorem surrogateDiagonalTailChunk001Sub000Block029Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block029Part023CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block029Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block029Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block029Part023CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block029Part023SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block029Part023] using hcert

def TailChunk001Sub000Block029Part024SupportExplicit : Finset ℕ :=
  ([17727] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block029Part024 : ℚ :=
  (86214707533 : ℚ) / 1551470880065587200

def SurrogateDiagonalTailChunk001Sub000Block029Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17727
    = surrogateDiagTailX0RatChunk001Sub000Block029Part024

theorem surrogateDiagonalTailChunk001Sub000Block029Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block029Part024CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block029Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block029Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block029Part024CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block029Part024SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block029Part024] using hcert

def surrogateDiagonalTailChunk001Sub000Block029HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block029Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block029Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block029Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block029Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block029Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block029Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block029Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block029Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block029Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block029Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block029Head : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block029Part000
    + surrogateDiagTailX0RatChunk001Sub000Block029Part001
    + surrogateDiagTailX0RatChunk001Sub000Block029Part002
    + surrogateDiagTailX0RatChunk001Sub000Block029Part003
    + surrogateDiagTailX0RatChunk001Sub000Block029Part004
    + surrogateDiagTailX0RatChunk001Sub000Block029Part005
    + surrogateDiagTailX0RatChunk001Sub000Block029Part006
    + surrogateDiagTailX0RatChunk001Sub000Block029Part007
    + surrogateDiagTailX0RatChunk001Sub000Block029Part008
    + surrogateDiagTailX0RatChunk001Sub000Block029Part009

def surrogateDiagonalTailChunk001Sub000Block029MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block029Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block029Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block029Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block029Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block029Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block029Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block029Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block029Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block029Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block029Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block029Mid : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block029Part010
    + surrogateDiagTailX0RatChunk001Sub000Block029Part011
    + surrogateDiagTailX0RatChunk001Sub000Block029Part012
    + surrogateDiagTailX0RatChunk001Sub000Block029Part013
    + surrogateDiagTailX0RatChunk001Sub000Block029Part014
    + surrogateDiagTailX0RatChunk001Sub000Block029Part015
    + surrogateDiagTailX0RatChunk001Sub000Block029Part016
    + surrogateDiagTailX0RatChunk001Sub000Block029Part017
    + surrogateDiagTailX0RatChunk001Sub000Block029Part018
    + surrogateDiagTailX0RatChunk001Sub000Block029Part019

def surrogateDiagonalTailChunk001Sub000Block029TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block029Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block029Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block029Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block029Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block029Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block029Tail : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block029Part020
    + surrogateDiagTailX0RatChunk001Sub000Block029Part021
    + surrogateDiagTailX0RatChunk001Sub000Block029Part022
    + surrogateDiagTailX0RatChunk001Sub000Block029Part023
    + surrogateDiagTailX0RatChunk001Sub000Block029Part024

def surrogateDiagonalTailChunk001Sub000Block029Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk001Sub000Block029HeadSum X0
    + surrogateDiagonalTailChunk001Sub000Block029MidSum X0
    + surrogateDiagonalTailChunk001Sub000Block029TailSum X0

def surrogateDiagTailX0RatChunk001Sub000Block029 : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block029Part000
    + surrogateDiagTailX0RatChunk001Sub000Block029Part001
    + surrogateDiagTailX0RatChunk001Sub000Block029Part002
    + surrogateDiagTailX0RatChunk001Sub000Block029Part003
    + surrogateDiagTailX0RatChunk001Sub000Block029Part004
    + surrogateDiagTailX0RatChunk001Sub000Block029Part005
    + surrogateDiagTailX0RatChunk001Sub000Block029Part006
    + surrogateDiagTailX0RatChunk001Sub000Block029Part007
    + surrogateDiagTailX0RatChunk001Sub000Block029Part008
    + surrogateDiagTailX0RatChunk001Sub000Block029Part009
    + surrogateDiagTailX0RatChunk001Sub000Block029Part010
    + surrogateDiagTailX0RatChunk001Sub000Block029Part011
    + surrogateDiagTailX0RatChunk001Sub000Block029Part012
    + surrogateDiagTailX0RatChunk001Sub000Block029Part013
    + surrogateDiagTailX0RatChunk001Sub000Block029Part014
    + surrogateDiagTailX0RatChunk001Sub000Block029Part015
    + surrogateDiagTailX0RatChunk001Sub000Block029Part016
    + surrogateDiagTailX0RatChunk001Sub000Block029Part017
    + surrogateDiagTailX0RatChunk001Sub000Block029Part018
    + surrogateDiagTailX0RatChunk001Sub000Block029Part019
    + surrogateDiagTailX0RatChunk001Sub000Block029Part020
    + surrogateDiagTailX0RatChunk001Sub000Block029Part021
    + surrogateDiagTailX0RatChunk001Sub000Block029Part022
    + surrogateDiagTailX0RatChunk001Sub000Block029Part023
    + surrogateDiagTailX0RatChunk001Sub000Block029Part024

theorem surrogateDiagTailX0RatChunk001Sub000Block029_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk001Sub000Block029Head + surrogateDiagTailX0RatChunk001Sub000Block029Mid + surrogateDiagTailX0RatChunk001Sub000Block029Tail =
      surrogateDiagTailX0RatChunk001Sub000Block029 := by
  unfold surrogateDiagTailX0RatChunk001Sub000Block029Head surrogateDiagTailX0RatChunk001Sub000Block029Mid surrogateDiagTailX0RatChunk001Sub000Block029Tail surrogateDiagTailX0RatChunk001Sub000Block029
  ring

def SurrogateDiagonalTailChunk001Sub000Block029HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block029HeadSum X0 = surrogateDiagTailX0RatChunk001Sub000Block029Head

def SurrogateDiagonalTailChunk001Sub000Block029MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block029MidSum X0 = surrogateDiagTailX0RatChunk001Sub000Block029Mid

def SurrogateDiagonalTailChunk001Sub000Block029TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block029TailSum X0 = surrogateDiagTailX0RatChunk001Sub000Block029Tail

theorem surrogateDiagonalTailChunk001Sub000Block029_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk001Sub000Block029HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk001Sub000Block029MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk001Sub000Block029TailCertificateAt X0) :
    surrogateDiagonalTailChunk001Sub000Block029Sum X0 = surrogateDiagTailX0RatChunk001Sub000Block029 := by
  unfold SurrogateDiagonalTailChunk001Sub000Block029HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk001Sub000Block029MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk001Sub000Block029TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk001Sub000Block029Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk001Sub000Block029_eq_head_add_mid_add_tail

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

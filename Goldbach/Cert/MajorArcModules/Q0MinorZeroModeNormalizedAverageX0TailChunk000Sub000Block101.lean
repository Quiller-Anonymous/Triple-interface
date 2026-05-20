import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0TailPilot25

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

open scoped BigOperators

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

/- Generated direct-term certificate blocks for tail chunk 000, subchunk 000, blocks [101,102). -/

/- Block 101 covers tail-support indices [2525,2550) and q from 4202 to 4245. -/

def TailChunk000Sub000Block101Part000SupportExplicit : Finset ℕ :=
  ([4202] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block101Part000 : ℚ :=
  (29280024067 : ℚ) / 1303470642000000

def SurrogateDiagonalTailChunk000Sub000Block101Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4202
    = surrogateDiagTailX0RatChunk000Sub000Block101Part000

theorem surrogateDiagonalTailChunk000Sub000Block101Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block101Part000CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block101Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block101Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block101Part000CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block101Part000SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block101Part000] using hcert

def TailChunk000Sub000Block101Part001SupportExplicit : Finset ℕ :=
  ([4206] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block101Part001 : ℚ :=
  (19627907191 : ℚ) / 384236832000000

def SurrogateDiagonalTailChunk000Sub000Block101Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4206
    = surrogateDiagTailX0RatChunk000Sub000Block101Part001

theorem surrogateDiagonalTailChunk000Sub000Block101Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block101Part001CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block101Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block101Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block101Part001CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block101Part001SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block101Part001] using hcert

def TailChunk000Sub000Block101Part002SupportExplicit : Finset ℕ :=
  ([4207] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block101Part002 : ℚ :=
  (17796122731 : ℚ) / 4199879808000000

def SurrogateDiagonalTailChunk000Sub000Block101Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4207
    = surrogateDiagTailX0RatChunk000Sub000Block101Part002

theorem surrogateDiagonalTailChunk000Sub000Block101Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block101Part002CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block101Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block101Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block101Part002CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block101Part002SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block101Part002] using hcert

def TailChunk000Sub000Block101Part003SupportExplicit : Finset ℕ :=
  ([4209] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block101Part003 : ℚ :=
  (1170617263 : ℚ) / 202437663436800

def SurrogateDiagonalTailChunk000Sub000Block101Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4209
    = surrogateDiagTailX0RatChunk000Sub000Block101Part003

theorem surrogateDiagonalTailChunk000Sub000Block101Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block101Part003CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block101Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block101Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block101Part003CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block101Part003SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block101Part003] using hcert

def TailChunk000Sub000Block101Part004SupportExplicit : Finset ℕ :=
  ([4210] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block101Part004 : ℚ :=
  (2063921281 : ℚ) / 88528166092800

def SurrogateDiagonalTailChunk000Sub000Block101Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4210
    = surrogateDiagTailX0RatChunk000Sub000Block101Part004

theorem surrogateDiagonalTailChunk000Sub000Block101Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block101Part004CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block101Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block101Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block101Part004CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block101Part004SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block101Part004] using hcert

def TailChunk000Sub000Block101Part005SupportExplicit : Finset ℕ :=
  ([4211] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block101Part005 : ℚ :=
  (443313025 : ℚ) / 314206549554162

def SurrogateDiagonalTailChunk000Sub000Block101Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4211
    = surrogateDiagTailX0RatChunk000Sub000Block101Part005

theorem surrogateDiagonalTailChunk000Sub000Block101Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block101Part005CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block101Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block101Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block101Part005CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block101Part005SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block101Part005] using hcert

def TailChunk000Sub000Block101Part006SupportExplicit : Finset ℕ :=
  ([4213] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block101Part006 : ℚ :=
  (40991455261 : ℚ) / 21298072538755200

def SurrogateDiagonalTailChunk000Sub000Block101Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4213
    = surrogateDiagTailX0RatChunk000Sub000Block101Part006

theorem surrogateDiagonalTailChunk000Sub000Block101Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block101Part006CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block101Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block101Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block101Part006CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block101Part006SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block101Part006] using hcert

def TailChunk000Sub000Block101Part007SupportExplicit : Finset ℕ :=
  ([4215] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block101Part007 : ℚ :=
  (4623371103 : ℚ) / 419689083699200

def SurrogateDiagonalTailChunk000Sub000Block101Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4215
    = surrogateDiagTailX0RatChunk000Sub000Block101Part007

theorem surrogateDiagonalTailChunk000Sub000Block101Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block101Part007CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block101Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block101Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block101Part007CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block101Part007SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block101Part007] using hcert

def TailChunk000Sub000Block101Part008SupportExplicit : Finset ℕ :=
  ([4217] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block101Part008 : ℚ :=
  (277860765625 : ℚ) / 197500989748449792

def SurrogateDiagonalTailChunk000Sub000Block101Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4217
    = surrogateDiagTailX0RatChunk000Sub000Block101Part008

theorem surrogateDiagonalTailChunk000Sub000Block101Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block101Part008CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block101Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block101Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block101Part008CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block101Part008SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block101Part008] using hcert

def TailChunk000Sub000Block101Part009SupportExplicit : Finset ℕ :=
  ([4218] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block101Part009 : ℚ :=
  (373041703675 : ℚ) / 7054185323593728

def SurrogateDiagonalTailChunk000Sub000Block101Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4218
    = surrogateDiagTailX0RatChunk000Sub000Block101Part009

theorem surrogateDiagonalTailChunk000Sub000Block101Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block101Part009CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block101Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block101Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block101Part009CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block101Part009SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block101Part009] using hcert

def TailChunk000Sub000Block101Part010SupportExplicit : Finset ℕ :=
  ([4219] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block101Part010 : ℚ :=
  (278124390625 : ℚ) / 197876021192390322

def SurrogateDiagonalTailChunk000Sub000Block101Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4219
    = surrogateDiagTailX0RatChunk000Sub000Block101Part010

theorem surrogateDiagonalTailChunk000Sub000Block101Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block101Part010CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block101Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block101Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block101Part010CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block101Part010SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block101Part010] using hcert

def TailChunk000Sub000Block101Part011SupportExplicit : Finset ℕ :=
  ([4222] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block101Part011 : ℚ :=
  (11136346179 : ℚ) / 660838621629400

def SurrogateDiagonalTailChunk000Sub000Block101Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4222
    = surrogateDiagTailX0RatChunk000Sub000Block101Part011

theorem surrogateDiagonalTailChunk000Sub000Block101Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block101Part011CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block101Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block101Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block101Part011CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block101Part011SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block101Part011] using hcert

def TailChunk000Sub000Block101Part012SupportExplicit : Finset ℕ :=
  ([4223] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block101Part012 : ℚ :=
  (10835739067 : ℚ) / 6928951337164800

def SurrogateDiagonalTailChunk000Sub000Block101Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4223
    = surrogateDiagTailX0RatChunk000Sub000Block101Part012

theorem surrogateDiagonalTailChunk000Sub000Block101Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block101Part012CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block101Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block101Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block101Part012CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block101Part012SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block101Part012] using hcert

def TailChunk000Sub000Block101Part013SupportExplicit : Finset ℕ :=
  ([4226] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block101Part013 : ℚ :=
  (557984505775 : ℚ) / 49751080166227968

def SurrogateDiagonalTailChunk000Sub000Block101Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4226
    = surrogateDiagTailX0RatChunk000Sub000Block101Part013

theorem surrogateDiagonalTailChunk000Sub000Block101Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block101Part013CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block101Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block101Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block101Part013CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block101Part013SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block101Part013] using hcert

def TailChunk000Sub000Block101Part014SupportExplicit : Finset ℕ :=
  ([4227] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block101Part014 : ℚ :=
  (868101462025 : ℚ) / 157237981759930368

def SurrogateDiagonalTailChunk000Sub000Block101Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4227
    = surrogateDiagTailX0RatChunk000Sub000Block101Part014

theorem surrogateDiagonalTailChunk000Sub000Block101Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block101Part014CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block101Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block101Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block101Part014CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block101Part014SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block101Part014] using hcert

def TailChunk000Sub000Block101Part015SupportExplicit : Finset ℕ :=
  ([4229] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block101Part015 : ℚ :=
  (279444390625 : ℚ) / 199759196330656032

def SurrogateDiagonalTailChunk000Sub000Block101Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4229
    = surrogateDiagTailX0RatChunk000Sub000Block101Part015

theorem surrogateDiagonalTailChunk000Sub000Block101Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block101Part015CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block101Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block101Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block101Part015CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block101Part015SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block101Part015] using hcert

def TailChunk000Sub000Block101Part016SupportExplicit : Finset ℕ :=
  ([4231] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block101Part016 : ℚ :=
  (447534025 : ℚ) / 320219901584082

def SurrogateDiagonalTailChunk000Sub000Block101Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4231
    = surrogateDiagTailX0RatChunk000Sub000Block101Part016

theorem surrogateDiagonalTailChunk000Sub000Block101Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block101Part016CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block101Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block101Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block101Part016CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block101Part016SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block101Part016] using hcert

def TailChunk000Sub000Block101Part017SupportExplicit : Finset ℕ :=
  ([4233] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block101Part017 : ℚ :=
  (70330575 : ℚ) / 11852100665344

def SurrogateDiagonalTailChunk000Sub000Block101Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4233
    = surrogateDiagTailX0RatChunk000Sub000Block101Part017

theorem surrogateDiagonalTailChunk000Sub000Block101Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block101Part017CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block101Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block101Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block101Part017CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block101Part017SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block101Part017] using hcert

def TailChunk000Sub000Block101Part018SupportExplicit : Finset ℕ :=
  ([4234] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block101Part018 : ℚ :=
  (179381623375 : ℚ) / 13767900390752256

def SurrogateDiagonalTailChunk000Sub000Block101Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4234
    = surrogateDiagTailX0RatChunk000Sub000Block101Part018

theorem surrogateDiagonalTailChunk000Sub000Block101Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block101Part018CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block101Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block101Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block101Part018CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block101Part018SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block101Part018] using hcert

def TailChunk000Sub000Block101Part019SupportExplicit : Finset ℕ :=
  ([4237] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block101Part019 : ℚ :=
  (33390459125 : ℚ) / 19924103944004004

def SurrogateDiagonalTailChunk000Sub000Block101Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4237
    = surrogateDiagTailX0RatChunk000Sub000Block101Part019

theorem surrogateDiagonalTailChunk000Sub000Block101Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block101Part019CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block101Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block101Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block101Part019CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block101Part019SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block101Part019] using hcert

def TailChunk000Sub000Block101Part020SupportExplicit : Finset ℕ :=
  ([4238] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block101Part020 : ℚ :=
  (379185136475 : ℚ) / 17855906600346624

def SurrogateDiagonalTailChunk000Sub000Block101Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4238
    = surrogateDiagTailX0RatChunk000Sub000Block101Part020

theorem surrogateDiagonalTailChunk000Sub000Block101Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block101Part020CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block101Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block101Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block101Part020CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block101Part020SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block101Part020] using hcert

def TailChunk000Sub000Block101Part021SupportExplicit : Finset ℕ :=
  ([4241] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block101Part021 : ℚ :=
  (89912418919 : ℚ) / 32325874058035200

def SurrogateDiagonalTailChunk000Sub000Block101Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4241
    = surrogateDiagTailX0RatChunk000Sub000Block101Part021

theorem surrogateDiagonalTailChunk000Sub000Block101Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block101Part021CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block101Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block101Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block101Part021CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block101Part021SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block101Part021] using hcert

def TailChunk000Sub000Block101Part022SupportExplicit : Finset ℕ :=
  ([4242] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block101Part022 : ℚ :=
  (8300161967 : ℚ) / 103700736000000

def SurrogateDiagonalTailChunk000Sub000Block101Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4242
    = surrogateDiagTailX0RatChunk000Sub000Block101Part022

theorem surrogateDiagonalTailChunk000Sub000Block101Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block101Part022CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block101Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block101Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block101Part022CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block101Part022SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block101Part022] using hcert

def TailChunk000Sub000Block101Part023SupportExplicit : Finset ℕ :=
  ([4243] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block101Part023 : ℚ :=
  (2249931048775 : ℚ) / 809672736042015048

def SurrogateDiagonalTailChunk000Sub000Block101Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4243
    = surrogateDiagTailX0RatChunk000Sub000Block101Part023

theorem surrogateDiagonalTailChunk000Sub000Block101Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block101Part023CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block101Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block101Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block101Part023CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block101Part023SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block101Part023] using hcert

def TailChunk000Sub000Block101Part024SupportExplicit : Finset ℕ :=
  ([4245] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block101Part024 : ℚ :=
  (157217374375 : ℚ) / 16192848356646912

def SurrogateDiagonalTailChunk000Sub000Block101Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4245
    = surrogateDiagTailX0RatChunk000Sub000Block101Part024

theorem surrogateDiagonalTailChunk000Sub000Block101Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block101Part024CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block101Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block101Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block101Part024CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block101Part024SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block101Part024] using hcert

def surrogateDiagonalTailChunk000Sub000Block101HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block101Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block101Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block101Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block101Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block101Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block101Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block101Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block101Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block101Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block101Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block101Head : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block101Part000
    + surrogateDiagTailX0RatChunk000Sub000Block101Part001
    + surrogateDiagTailX0RatChunk000Sub000Block101Part002
    + surrogateDiagTailX0RatChunk000Sub000Block101Part003
    + surrogateDiagTailX0RatChunk000Sub000Block101Part004
    + surrogateDiagTailX0RatChunk000Sub000Block101Part005
    + surrogateDiagTailX0RatChunk000Sub000Block101Part006
    + surrogateDiagTailX0RatChunk000Sub000Block101Part007
    + surrogateDiagTailX0RatChunk000Sub000Block101Part008
    + surrogateDiagTailX0RatChunk000Sub000Block101Part009

def surrogateDiagonalTailChunk000Sub000Block101MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block101Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block101Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block101Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block101Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block101Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block101Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block101Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block101Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block101Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block101Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block101Mid : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block101Part010
    + surrogateDiagTailX0RatChunk000Sub000Block101Part011
    + surrogateDiagTailX0RatChunk000Sub000Block101Part012
    + surrogateDiagTailX0RatChunk000Sub000Block101Part013
    + surrogateDiagTailX0RatChunk000Sub000Block101Part014
    + surrogateDiagTailX0RatChunk000Sub000Block101Part015
    + surrogateDiagTailX0RatChunk000Sub000Block101Part016
    + surrogateDiagTailX0RatChunk000Sub000Block101Part017
    + surrogateDiagTailX0RatChunk000Sub000Block101Part018
    + surrogateDiagTailX0RatChunk000Sub000Block101Part019

def surrogateDiagonalTailChunk000Sub000Block101TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block101Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block101Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block101Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block101Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block101Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block101Tail : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block101Part020
    + surrogateDiagTailX0RatChunk000Sub000Block101Part021
    + surrogateDiagTailX0RatChunk000Sub000Block101Part022
    + surrogateDiagTailX0RatChunk000Sub000Block101Part023
    + surrogateDiagTailX0RatChunk000Sub000Block101Part024

def surrogateDiagonalTailChunk000Sub000Block101Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub000Block101HeadSum X0
    + surrogateDiagonalTailChunk000Sub000Block101MidSum X0
    + surrogateDiagonalTailChunk000Sub000Block101TailSum X0

def surrogateDiagTailX0RatChunk000Sub000Block101 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block101Part000
    + surrogateDiagTailX0RatChunk000Sub000Block101Part001
    + surrogateDiagTailX0RatChunk000Sub000Block101Part002
    + surrogateDiagTailX0RatChunk000Sub000Block101Part003
    + surrogateDiagTailX0RatChunk000Sub000Block101Part004
    + surrogateDiagTailX0RatChunk000Sub000Block101Part005
    + surrogateDiagTailX0RatChunk000Sub000Block101Part006
    + surrogateDiagTailX0RatChunk000Sub000Block101Part007
    + surrogateDiagTailX0RatChunk000Sub000Block101Part008
    + surrogateDiagTailX0RatChunk000Sub000Block101Part009
    + surrogateDiagTailX0RatChunk000Sub000Block101Part010
    + surrogateDiagTailX0RatChunk000Sub000Block101Part011
    + surrogateDiagTailX0RatChunk000Sub000Block101Part012
    + surrogateDiagTailX0RatChunk000Sub000Block101Part013
    + surrogateDiagTailX0RatChunk000Sub000Block101Part014
    + surrogateDiagTailX0RatChunk000Sub000Block101Part015
    + surrogateDiagTailX0RatChunk000Sub000Block101Part016
    + surrogateDiagTailX0RatChunk000Sub000Block101Part017
    + surrogateDiagTailX0RatChunk000Sub000Block101Part018
    + surrogateDiagTailX0RatChunk000Sub000Block101Part019
    + surrogateDiagTailX0RatChunk000Sub000Block101Part020
    + surrogateDiagTailX0RatChunk000Sub000Block101Part021
    + surrogateDiagTailX0RatChunk000Sub000Block101Part022
    + surrogateDiagTailX0RatChunk000Sub000Block101Part023
    + surrogateDiagTailX0RatChunk000Sub000Block101Part024

theorem surrogateDiagTailX0RatChunk000Sub000Block101_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk000Sub000Block101Head + surrogateDiagTailX0RatChunk000Sub000Block101Mid + surrogateDiagTailX0RatChunk000Sub000Block101Tail =
      surrogateDiagTailX0RatChunk000Sub000Block101 := by
  unfold surrogateDiagTailX0RatChunk000Sub000Block101Head surrogateDiagTailX0RatChunk000Sub000Block101Mid surrogateDiagTailX0RatChunk000Sub000Block101Tail surrogateDiagTailX0RatChunk000Sub000Block101
  ring

def SurrogateDiagonalTailChunk000Sub000Block101HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block101HeadSum X0 = surrogateDiagTailX0RatChunk000Sub000Block101Head

def SurrogateDiagonalTailChunk000Sub000Block101MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block101MidSum X0 = surrogateDiagTailX0RatChunk000Sub000Block101Mid

def SurrogateDiagonalTailChunk000Sub000Block101TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block101TailSum X0 = surrogateDiagTailX0RatChunk000Sub000Block101Tail

theorem surrogateDiagonalTailChunk000Sub000Block101_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk000Sub000Block101HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk000Sub000Block101MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk000Sub000Block101TailCertificateAt X0) :
    surrogateDiagonalTailChunk000Sub000Block101Sum X0 = surrogateDiagTailX0RatChunk000Sub000Block101 := by
  unfold SurrogateDiagonalTailChunk000Sub000Block101HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk000Sub000Block101MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk000Sub000Block101TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk000Sub000Block101Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk000Sub000Block101_eq_head_add_mid_add_tail

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

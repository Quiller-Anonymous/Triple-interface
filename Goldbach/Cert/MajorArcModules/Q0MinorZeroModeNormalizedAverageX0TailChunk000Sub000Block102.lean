import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0TailPilot25

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

open scoped BigOperators

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

/- Generated direct-term certificate blocks for tail chunk 000, subchunk 000, blocks [102,103). -/

/- Block 102 covers tail-support indices [2550,2575) and q from 4246 to 4285. -/

def TailChunk000Sub000Block102Part000SupportExplicit : Finset ℕ :=
  ([4246] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block102Part000 : ℚ :=
  (20772247591 : ℚ) / 1359226286899200

def SurrogateDiagonalTailChunk000Sub000Block102Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4246
    = surrogateDiagTailX0RatChunk000Sub000Block102Part000

theorem surrogateDiagonalTailChunk000Sub000Block102Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block102Part000CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block102Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block102Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block102Part000CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block102Part000SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block102Part000] using hcert

def TailChunk000Sub000Block102Part001SupportExplicit : Finset ℕ :=
  ([4247] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block102Part001 : ℚ :=
  (21830525429 : ℚ) / 13857902674329600

def SurrogateDiagonalTailChunk000Sub000Block102Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4247
    = surrogateDiagTailX0RatChunk000Sub000Block102Part001

theorem surrogateDiagonalTailChunk000Sub000Block102Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block102Part001CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block102Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block102Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block102Part001CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block102Part001SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block102Part001] using hcert

def TailChunk000Sub000Block102Part002SupportExplicit : Finset ℕ :=
  ([4249] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block102Part002 : ℚ :=
  (247252925875 : ℚ) / 109260294243070752

def SurrogateDiagonalTailChunk000Sub000Block102Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4249
    = surrogateDiagTailX0RatChunk000Sub000Block102Part002

theorem surrogateDiagonalTailChunk000Sub000Block102Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block102Part002CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block102Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block102Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block102Part002CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block102Part002SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block102Part002] using hcert

def TailChunk000Sub000Block102Part003SupportExplicit : Finset ℕ :=
  ([4251] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block102Part003 : ℚ :=
  (401818774625 : ℚ) / 56433482588749824

def SurrogateDiagonalTailChunk000Sub000Block102Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4251
    = surrogateDiagTailX0RatChunk000Sub000Block102Part003

theorem surrogateDiagonalTailChunk000Sub000Block102Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block102Part003CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block102Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block102Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block102Part003CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block102Part003SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block102Part003] using hcert

def TailChunk000Sub000Block102Part004SupportExplicit : Finset ℕ :=
  ([4253] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block102Part004 : ℚ :=
  (282625140625 : ℚ) / 204333649111870752

def SurrogateDiagonalTailChunk000Sub000Block102Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4253
    = surrogateDiagTailX0RatChunk000Sub000Block102Part004

theorem surrogateDiagonalTailChunk000Sub000Block102Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block102Part004CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block102Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block102Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block102Part004CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block102Part004SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block102Part004] using hcert

def TailChunk000Sub000Block102Part005SupportExplicit : Finset ℕ :=
  ([4254] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block102Part005 : ℚ :=
  (203988304625 : ℚ) / 5026317016310784

def SurrogateDiagonalTailChunk000Sub000Block102Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4254
    = surrogateDiagTailX0RatChunk000Sub000Block102Part005

theorem surrogateDiagonalTailChunk000Sub000Block102Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block102Part005CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block102Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block102Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block102Part005CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block102Part005SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block102Part005] using hcert

def TailChunk000Sub000Block102Part006SupportExplicit : Finset ℕ :=
  ([4255] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block102Part006 : ℚ :=
  (446274368975 : ℚ) / 125932421670764544

def SurrogateDiagonalTailChunk000Sub000Block102Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4255
    = surrogateDiagTailX0RatChunk000Sub000Block102Part006

theorem surrogateDiagonalTailChunk000Sub000Block102Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block102Part006CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block102Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block102Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block102Part006CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block102Part006SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block102Part006] using hcert

def TailChunk000Sub000Block102Part007SupportExplicit : Finset ℕ :=
  ([4258] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block102Part007 : ℚ :=
  (5779117275 : ℚ) / 348815695642624

def SurrogateDiagonalTailChunk000Sub000Block102Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4258
    = surrogateDiagTailX0RatChunk000Sub000Block102Part007

theorem surrogateDiagonalTailChunk000Sub000Block102Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block102Part007CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block102Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block102Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block102Part007CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block102Part007SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block102Part007] using hcert

def TailChunk000Sub000Block102Part008SupportExplicit : Finset ℕ :=
  ([4259] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block102Part008 : ℚ :=
  (283423140625 : ℚ) / 205489434017679762

def SurrogateDiagonalTailChunk000Sub000Block102Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4259
    = surrogateDiagTailX0RatChunk000Sub000Block102Part008

theorem surrogateDiagonalTailChunk000Sub000Block102Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block102Part008CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block102Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block102Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block102Part008CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block102Part008SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block102Part008] using hcert

def TailChunk000Sub000Block102Part009SupportExplicit : Finset ℕ :=
  ([4261] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block102Part009 : ℚ :=
  (453903025 : ℚ) / 329401252837152

def SurrogateDiagonalTailChunk000Sub000Block102Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4261
    = surrogateDiagTailX0RatChunk000Sub000Block102Part009

theorem surrogateDiagonalTailChunk000Sub000Block102Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block102Part009CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block102Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block102Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block102Part009CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block102Part009SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block102Part009] using hcert

def TailChunk000Sub000Block102Part010SupportExplicit : Finset ℕ :=
  ([4262] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block102Part010 : ℚ :=
  (22701263839 : ℚ) / 2058757830232200

def SurrogateDiagonalTailChunk000Sub000Block102Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4262
    = surrogateDiagTailX0RatChunk000Sub000Block102Part010

theorem surrogateDiagonalTailChunk000Sub000Block102Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block102Part010CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block102Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block102Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block102Part010CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block102Part010SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block102Part010] using hcert

def TailChunk000Sub000Block102Part011SupportExplicit : Finset ℕ :=
  ([4265] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block102Part011 : ℚ :=
  (954180306625 : ℚ) / 337306882905243648

def SurrogateDiagonalTailChunk000Sub000Block102Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4265
    = surrogateDiagTailX0RatChunk000Sub000Block102Part011

theorem surrogateDiagonalTailChunk000Sub000Block102Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block102Part011CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block102Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block102Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block102Part011CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block102Part011SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block102Part011] using hcert

def TailChunk000Sub000Block102Part012SupportExplicit : Finset ℕ :=
  ([4267] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block102Part012 : ℚ :=
  (10755055087 : ℚ) / 6401280000000000

def SurrogateDiagonalTailChunk000Sub000Block102Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4267
    = surrogateDiagTailX0RatChunk000Sub000Block102Part012

theorem surrogateDiagonalTailChunk000Sub000Block102Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block102Part012CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block102Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block102Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block102Part012CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block102Part012SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block102Part012] using hcert

def TailChunk000Sub000Block102Part013SupportExplicit : Finset ℕ :=
  ([4269] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block102Part013 : ℚ :=
  (25296875 : ℚ) / 5451764937408

def SurrogateDiagonalTailChunk000Sub000Block102Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4269
    = surrogateDiagTailX0RatChunk000Sub000Block102Part013

theorem surrogateDiagonalTailChunk000Sub000Block102Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block102Part013CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block102Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block102Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block102Part013CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block102Part013SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block102Part013] using hcert

def TailChunk000Sub000Block102Part014SupportExplicit : Finset ℕ :=
  ([4270] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block102Part014 : ℚ :=
  (1368894761 : ℚ) / 35838974361600

def SurrogateDiagonalTailChunk000Sub000Block102Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4270
    = surrogateDiagTailX0RatChunk000Sub000Block102Part014

theorem surrogateDiagonalTailChunk000Sub000Block102Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block102Part014CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block102Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block102Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block102Part014CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block102Part014SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block102Part014] using hcert

def TailChunk000Sub000Block102Part015SupportExplicit : Finset ℕ :=
  ([4271] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block102Part015 : ℚ :=
  (456036025 : ℚ) / 332505130138482

def SurrogateDiagonalTailChunk000Sub000Block102Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4271
    = surrogateDiagTailX0RatChunk000Sub000Block102Part015

theorem surrogateDiagonalTailChunk000Sub000Block102Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block102Part015CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block102Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block102Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block102Part015CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block102Part015SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block102Part015] using hcert

def TailChunk000Sub000Block102Part016SupportExplicit : Finset ℕ :=
  ([4273] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block102Part016 : ℚ :=
  (285289515625 : ℚ) / 208205330239660032

def SurrogateDiagonalTailChunk000Sub000Block102Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4273
    = surrogateDiagTailX0RatChunk000Sub000Block102Part016

theorem surrogateDiagonalTailChunk000Sub000Block102Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block102Part016CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block102Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block102Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block102Part016CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block102Part016SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block102Part016] using hcert

def TailChunk000Sub000Block102Part017SupportExplicit : Finset ℕ :=
  ([4274] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block102Part017 : ℚ :=
  (95102964425 : ℚ) / 5783481395546112

def SurrogateDiagonalTailChunk000Sub000Block102Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4274
    = surrogateDiagTailX0RatChunk000Sub000Block102Part017

theorem surrogateDiagonalTailChunk000Sub000Block102Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block102Part017CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block102Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block102Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block102Part017CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block102Part017SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block102Part017] using hcert

def TailChunk000Sub000Block102Part018SupportExplicit : Finset ℕ :=
  ([4277] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block102Part018 : ℚ :=
  (395123442175 : ℚ) / 75219108182433792

def SurrogateDiagonalTailChunk000Sub000Block102Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4277
    = surrogateDiagTailX0RatChunk000Sub000Block102Part018

theorem surrogateDiagonalTailChunk000Sub000Block102Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block102Part018CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block102Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block102Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block102Part018CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block102Part018SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block102Part018] using hcert

def TailChunk000Sub000Block102Part019SupportExplicit : Finset ℕ :=
  ([4278] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block102Part019 : ℚ :=
  (18645198133 : ℚ) / 303656495155200

def SurrogateDiagonalTailChunk000Sub000Block102Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4278
    = surrogateDiagTailX0RatChunk000Sub000Block102Part019

theorem surrogateDiagonalTailChunk000Sub000Block102Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block102Part019CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block102Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block102Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block102Part019CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block102Part019SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block102Part019] using hcert

def TailChunk000Sub000Block102Part020SupportExplicit : Finset ℕ :=
  ([4279] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block102Part020 : ℚ :=
  (15909268061 : ℚ) / 4533605727037440

def SurrogateDiagonalTailChunk000Sub000Block102Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4279
    = surrogateDiagTailX0RatChunk000Sub000Block102Part020

theorem surrogateDiagonalTailChunk000Sub000Block102Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block102Part020CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block102Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block102Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block102Part020CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block102Part020SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block102Part020] using hcert

def TailChunk000Sub000Block102Part021SupportExplicit : Finset ℕ :=
  ([4281] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block102Part021 : ℚ :=
  (76317825 : ℚ) / 16540098570304

def SurrogateDiagonalTailChunk000Sub000Block102Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4281
    = surrogateDiagTailX0RatChunk000Sub000Block102Part021

theorem surrogateDiagonalTailChunk000Sub000Block102Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block102Part021CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block102Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block102Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block102Part021CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block102Part021SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block102Part021] using hcert

def TailChunk000Sub000Block102Part022SupportExplicit : Finset ℕ :=
  ([4282] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block102Part022 : ℚ :=
  (22914821119 : ℚ) / 2097693070723200

def SurrogateDiagonalTailChunk000Sub000Block102Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4282
    = surrogateDiagTailX0RatChunk000Sub000Block102Part022

theorem surrogateDiagonalTailChunk000Sub000Block102Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block102Part022CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block102Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block102Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block102Part022CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block102Part022SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block102Part022] using hcert

def TailChunk000Sub000Block102Part023SupportExplicit : Finset ℕ :=
  ([4283] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block102Part023 : ℚ :=
  (286626390625 : ℚ) / 210161674151654322

def SurrogateDiagonalTailChunk000Sub000Block102Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4283
    = surrogateDiagTailX0RatChunk000Sub000Block102Part023

theorem surrogateDiagonalTailChunk000Sub000Block102Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block102Part023CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block102Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block102Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block102Part023CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block102Part023SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block102Part023] using hcert

def TailChunk000Sub000Block102Part024SupportExplicit : Finset ℕ :=
  ([4285] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block102Part024 : ℚ :=
  (321049671375 : ℚ) / 114562010902429696

def SurrogateDiagonalTailChunk000Sub000Block102Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4285
    = surrogateDiagTailX0RatChunk000Sub000Block102Part024

theorem surrogateDiagonalTailChunk000Sub000Block102Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block102Part024CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block102Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block102Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block102Part024CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block102Part024SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block102Part024] using hcert

def surrogateDiagonalTailChunk000Sub000Block102HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block102Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block102Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block102Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block102Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block102Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block102Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block102Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block102Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block102Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block102Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block102Head : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block102Part000
    + surrogateDiagTailX0RatChunk000Sub000Block102Part001
    + surrogateDiagTailX0RatChunk000Sub000Block102Part002
    + surrogateDiagTailX0RatChunk000Sub000Block102Part003
    + surrogateDiagTailX0RatChunk000Sub000Block102Part004
    + surrogateDiagTailX0RatChunk000Sub000Block102Part005
    + surrogateDiagTailX0RatChunk000Sub000Block102Part006
    + surrogateDiagTailX0RatChunk000Sub000Block102Part007
    + surrogateDiagTailX0RatChunk000Sub000Block102Part008
    + surrogateDiagTailX0RatChunk000Sub000Block102Part009

def surrogateDiagonalTailChunk000Sub000Block102MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block102Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block102Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block102Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block102Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block102Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block102Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block102Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block102Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block102Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block102Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block102Mid : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block102Part010
    + surrogateDiagTailX0RatChunk000Sub000Block102Part011
    + surrogateDiagTailX0RatChunk000Sub000Block102Part012
    + surrogateDiagTailX0RatChunk000Sub000Block102Part013
    + surrogateDiagTailX0RatChunk000Sub000Block102Part014
    + surrogateDiagTailX0RatChunk000Sub000Block102Part015
    + surrogateDiagTailX0RatChunk000Sub000Block102Part016
    + surrogateDiagTailX0RatChunk000Sub000Block102Part017
    + surrogateDiagTailX0RatChunk000Sub000Block102Part018
    + surrogateDiagTailX0RatChunk000Sub000Block102Part019

def surrogateDiagonalTailChunk000Sub000Block102TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block102Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block102Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block102Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block102Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block102Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block102Tail : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block102Part020
    + surrogateDiagTailX0RatChunk000Sub000Block102Part021
    + surrogateDiagTailX0RatChunk000Sub000Block102Part022
    + surrogateDiagTailX0RatChunk000Sub000Block102Part023
    + surrogateDiagTailX0RatChunk000Sub000Block102Part024

def surrogateDiagonalTailChunk000Sub000Block102Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub000Block102HeadSum X0
    + surrogateDiagonalTailChunk000Sub000Block102MidSum X0
    + surrogateDiagonalTailChunk000Sub000Block102TailSum X0

def surrogateDiagTailX0RatChunk000Sub000Block102 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block102Part000
    + surrogateDiagTailX0RatChunk000Sub000Block102Part001
    + surrogateDiagTailX0RatChunk000Sub000Block102Part002
    + surrogateDiagTailX0RatChunk000Sub000Block102Part003
    + surrogateDiagTailX0RatChunk000Sub000Block102Part004
    + surrogateDiagTailX0RatChunk000Sub000Block102Part005
    + surrogateDiagTailX0RatChunk000Sub000Block102Part006
    + surrogateDiagTailX0RatChunk000Sub000Block102Part007
    + surrogateDiagTailX0RatChunk000Sub000Block102Part008
    + surrogateDiagTailX0RatChunk000Sub000Block102Part009
    + surrogateDiagTailX0RatChunk000Sub000Block102Part010
    + surrogateDiagTailX0RatChunk000Sub000Block102Part011
    + surrogateDiagTailX0RatChunk000Sub000Block102Part012
    + surrogateDiagTailX0RatChunk000Sub000Block102Part013
    + surrogateDiagTailX0RatChunk000Sub000Block102Part014
    + surrogateDiagTailX0RatChunk000Sub000Block102Part015
    + surrogateDiagTailX0RatChunk000Sub000Block102Part016
    + surrogateDiagTailX0RatChunk000Sub000Block102Part017
    + surrogateDiagTailX0RatChunk000Sub000Block102Part018
    + surrogateDiagTailX0RatChunk000Sub000Block102Part019
    + surrogateDiagTailX0RatChunk000Sub000Block102Part020
    + surrogateDiagTailX0RatChunk000Sub000Block102Part021
    + surrogateDiagTailX0RatChunk000Sub000Block102Part022
    + surrogateDiagTailX0RatChunk000Sub000Block102Part023
    + surrogateDiagTailX0RatChunk000Sub000Block102Part024

theorem surrogateDiagTailX0RatChunk000Sub000Block102_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk000Sub000Block102Head + surrogateDiagTailX0RatChunk000Sub000Block102Mid + surrogateDiagTailX0RatChunk000Sub000Block102Tail =
      surrogateDiagTailX0RatChunk000Sub000Block102 := by
  unfold surrogateDiagTailX0RatChunk000Sub000Block102Head surrogateDiagTailX0RatChunk000Sub000Block102Mid surrogateDiagTailX0RatChunk000Sub000Block102Tail surrogateDiagTailX0RatChunk000Sub000Block102
  ring

def SurrogateDiagonalTailChunk000Sub000Block102HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block102HeadSum X0 = surrogateDiagTailX0RatChunk000Sub000Block102Head

def SurrogateDiagonalTailChunk000Sub000Block102MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block102MidSum X0 = surrogateDiagTailX0RatChunk000Sub000Block102Mid

def SurrogateDiagonalTailChunk000Sub000Block102TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block102TailSum X0 = surrogateDiagTailX0RatChunk000Sub000Block102Tail

theorem surrogateDiagonalTailChunk000Sub000Block102_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk000Sub000Block102HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk000Sub000Block102MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk000Sub000Block102TailCertificateAt X0) :
    surrogateDiagonalTailChunk000Sub000Block102Sum X0 = surrogateDiagTailX0RatChunk000Sub000Block102 := by
  unfold SurrogateDiagonalTailChunk000Sub000Block102HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk000Sub000Block102MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk000Sub000Block102TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk000Sub000Block102Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk000Sub000Block102_eq_head_add_mid_add_tail

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

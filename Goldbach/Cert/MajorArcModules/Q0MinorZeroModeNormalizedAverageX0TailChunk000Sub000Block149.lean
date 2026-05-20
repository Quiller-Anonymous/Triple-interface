import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0TailPilot25

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

open scoped BigOperators

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

/- Generated direct-term certificate blocks for tail chunk 000, subchunk 000, blocks [149,150). -/

/- Block 149 covers tail-support indices [3725,3750) and q from 6179 to 6215. -/

def TailChunk000Sub000Block149Part000SupportExplicit : Finset ℕ :=
  ([6179] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block149Part000 : ℚ :=
  (2291851146025 : ℚ) / 3189107905431717888

def SurrogateDiagonalTailChunk000Sub000Block149Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6179
    = surrogateDiagTailX0RatChunk000Sub000Block149Part000

theorem surrogateDiagonalTailChunk000Sub000Block149Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block149Part000CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block149Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block149Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block149Part000CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block149Part000SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block149Part000] using hcert

def TailChunk000Sub000Block149Part001SupportExplicit : Finset ℕ :=
  ([6181] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block149Part001 : ℚ :=
  (1947032156875 : ℚ) / 1961129176680094848

def SurrogateDiagonalTailChunk000Sub000Block149Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6181
    = surrogateDiagTailX0RatChunk000Sub000Block149Part001

theorem surrogateDiagonalTailChunk000Sub000Block149Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block149Part001CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block149Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block149Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block149Part001CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block149Part001SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block149Part001] using hcert

def TailChunk000Sub000Block149Part002SupportExplicit : Finset ℕ :=
  ([6182] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block149Part002 : ℚ :=
  (8493687983 : ℚ) / 1229557862400000

def SurrogateDiagonalTailChunk000Sub000Block149Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6182
    = surrogateDiagTailX0RatChunk000Sub000Block149Part002

theorem surrogateDiagonalTailChunk000Sub000Block149Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block149Part002CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block149Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block149Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block149Part002CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block149Part002SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block149Part002] using hcert

def TailChunk000Sub000Block149Part003SupportExplicit : Finset ℕ :=
  ([6185] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block149Part003 : ℚ :=
  (302622147775 : ℚ) / 248994329539166208

def SurrogateDiagonalTailChunk000Sub000Block149Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6185
    = surrogateDiagTailX0RatChunk000Sub000Block149Part003

theorem surrogateDiagonalTailChunk000Sub000Block149Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block149Part003CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block149Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block149Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block149Part003CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block149Part003SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block149Part003] using hcert

def TailChunk000Sub000Block149Part004SupportExplicit : Finset ℕ :=
  ([6186] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block149Part004 : ℚ :=
  (5841007193 : ℚ) / 360234851763840

def SurrogateDiagonalTailChunk000Sub000Block149Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6186
    = surrogateDiagTailX0RatChunk000Sub000Block149Part004

theorem surrogateDiagonalTailChunk000Sub000Block149Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block149Part004CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block149Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block149Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block149Part004CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block149Part004SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block149Part004] using hcert

def TailChunk000Sub000Block149Part005SupportExplicit : Finset ℕ :=
  ([6187] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block149Part005 : ℚ :=
  (753582398175 : ℚ) / 1007245889104254976

def SurrogateDiagonalTailChunk000Sub000Block149Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6187
    = surrogateDiagTailX0RatChunk000Sub000Block149Part005

theorem surrogateDiagonalTailChunk000Sub000Block149Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block149Part005CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block149Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block149Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block149Part005CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block149Part005SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block149Part005] using hcert

def TailChunk000Sub000Block149Part006SupportExplicit : Finset ℕ :=
  ([6189] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block149Part006 : ℚ :=
  (332384682025 : ℚ) / 180817930358160672

def SurrogateDiagonalTailChunk000Sub000Block149Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6189
    = surrogateDiagTailX0RatChunk000Sub000Block149Part006

theorem surrogateDiagonalTailChunk000Sub000Block149Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block149Part006CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block149Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block149Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block149Part006CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block149Part006SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block149Part006] using hcert

def TailChunk000Sub000Block149Part007SupportExplicit : Finset ℕ :=
  ([6190] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block149Part007 : ℚ :=
  (908480754175 : ℚ) / 93372873577187328

def SurrogateDiagonalTailChunk000Sub000Block149Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6190
    = surrogateDiagTailX0RatChunk000Sub000Block149Part007

theorem surrogateDiagonalTailChunk000Sub000Block149Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block149Part007CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block149Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block149Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block149Part007CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block149Part007SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block149Part007] using hcert

def TailChunk000Sub000Block149Part008SupportExplicit : Finset ℕ :=
  ([6191] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block149Part008 : ℚ :=
  (92313848299 : ℚ) / 129625920000000000

def SurrogateDiagonalTailChunk000Sub000Block149Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6191
    = surrogateDiagTailX0RatChunk000Sub000Block149Part008

theorem surrogateDiagonalTailChunk000Sub000Block149Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block149Part008CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block149Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block149Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block149Part008CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block149Part008SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block149Part008] using hcert

def TailChunk000Sub000Block149Part009SupportExplicit : Finset ℕ :=
  ([6193] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block149Part009 : ℚ :=
  (84628620511 : ℚ) / 99777383822467200

def SurrogateDiagonalTailChunk000Sub000Block149Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6193
    = surrogateDiagTailX0RatChunk000Sub000Block149Part009

theorem surrogateDiagonalTailChunk000Sub000Block149Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block149Part009CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block149Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block149Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block149Part009CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block149Part009SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block149Part009] using hcert

def TailChunk000Sub000Block149Part010SupportExplicit : Finset ℕ :=
  ([6194] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block149Part010 : ℚ :=
  (558117815225 : ℚ) / 90395527164254784

def SurrogateDiagonalTailChunk000Sub000Block149Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6194
    = surrogateDiagTailX0RatChunk000Sub000Block149Part010

theorem surrogateDiagonalTailChunk000Sub000Block149Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block149Part010CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block149Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block149Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block149Part010CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block149Part010SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block149Part010] using hcert

def TailChunk000Sub000Block149Part011SupportExplicit : Finset ℕ :=
  ([6195] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block149Part011 : ℚ :=
  (889976947675 : ℚ) / 150211707410055168

def SurrogateDiagonalTailChunk000Sub000Block149Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6195
    = surrogateDiagTailX0RatChunk000Sub000Block149Part011

theorem surrogateDiagonalTailChunk000Sub000Block149Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block149Part011CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block149Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block149Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block149Part011CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block149Part011SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block149Part011] using hcert

def TailChunk000Sub000Block149Part012SupportExplicit : Finset ℕ :=
  ([6197] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block149Part012 : ℚ :=
  (600043890625 : ℚ) / 921324253413241632

def SurrogateDiagonalTailChunk000Sub000Block149Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6197
    = surrogateDiagTailX0RatChunk000Sub000Block149Part012

theorem surrogateDiagonalTailChunk000Sub000Block149Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block149Part012CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block149Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block149Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block149Part012CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block149Part012SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block149Part012] using hcert

def TailChunk000Sub000Block149Part013SupportExplicit : Finset ℕ :=
  ([6198] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block149Part013 : ℚ :=
  (466652663425 : ℚ) / 45380119032004608

def SurrogateDiagonalTailChunk000Sub000Block149Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6198
    = surrogateDiagTailX0RatChunk000Sub000Block149Part013

theorem surrogateDiagonalTailChunk000Sub000Block149Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block149Part013CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block149Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block149Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block149Part013CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block149Part013SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block149Part013] using hcert

def TailChunk000Sub000Block149Part014SupportExplicit : Finset ℕ :=
  ([6199] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block149Part014 : ℚ :=
  (600431265625 : ℚ) / 922514402463305202

def SurrogateDiagonalTailChunk000Sub000Block149Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6199
    = surrogateDiagTailX0RatChunk000Sub000Block149Part014

theorem surrogateDiagonalTailChunk000Sub000Block149Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block149Part014CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block149Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block149Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block149Part014CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block149Part014SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block149Part014] using hcert

def TailChunk000Sub000Block149Part015SupportExplicit : Finset ℕ :=
  ([6202] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block149Part015 : ℚ :=
  (140904163525 : ℚ) / 30921527990744352

def SurrogateDiagonalTailChunk000Sub000Block149Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6202
    = surrogateDiagTailX0RatChunk000Sub000Block149Part015

theorem surrogateDiagonalTailChunk000Sub000Block149Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block149Part015CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block149Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block149Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block149Part015CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block149Part015SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block149Part015] using hcert

def TailChunk000Sub000Block149Part016SupportExplicit : Finset ℕ :=
  ([6203] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block149Part016 : ℚ :=
  (601206390625 : ℚ) / 924898159367354802

def SurrogateDiagonalTailChunk000Sub000Block149Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6203
    = surrogateDiagTailX0RatChunk000Sub000Block149Part016

theorem surrogateDiagonalTailChunk000Sub000Block149Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block149Part016CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block149Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block149Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block149Part016CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block149Part016SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block149Part016] using hcert

def TailChunk000Sub000Block149Part017SupportExplicit : Finset ℕ :=
  ([6205] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block149Part017 : ℚ :=
  (1679894405575 : ℚ) / 1127396651405672448

def SurrogateDiagonalTailChunk000Sub000Block149Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6205
    = surrogateDiagTailX0RatChunk000Sub000Block149Part017

theorem surrogateDiagonalTailChunk000Sub000Block149Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block149Part017CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block149Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block149Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block149Part017CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block149Part017SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block149Part017] using hcert

def TailChunk000Sub000Block149Part018SupportExplicit : Finset ℕ :=
  ([6206] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block149Part018 : ℚ :=
  (1724833825 : ℚ) / 565702796015616

def SurrogateDiagonalTailChunk000Sub000Block149Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6206
    = surrogateDiagTailX0RatChunk000Sub000Block149Part018

theorem surrogateDiagonalTailChunk000Sub000Block149Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block149Part018CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block149Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block149Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block149Part018CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block149Part018SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block149Part018] using hcert

def TailChunk000Sub000Block149Part019SupportExplicit : Finset ℕ :=
  ([6207] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block149Part019 : ℚ :=
  (160435875 : ℚ) / 73158051349504

def SurrogateDiagonalTailChunk000Sub000Block149Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6207
    = surrogateDiagTailX0RatChunk000Sub000Block149Part019

theorem surrogateDiagonalTailChunk000Sub000Block149Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block149Part019CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block149Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block149Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block149Part019CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block149Part019SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block149Part019] using hcert

def TailChunk000Sub000Block149Part020SupportExplicit : Finset ℕ :=
  ([6209] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block149Part020 : ℚ :=
  (2013816908575 : ℚ) / 1996947962582410368

def SurrogateDiagonalTailChunk000Sub000Block149Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6209
    = surrogateDiagTailX0RatChunk000Sub000Block149Part020

theorem surrogateDiagonalTailChunk000Sub000Block149Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block149Part020CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block149Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block149Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block149Part020CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block149Part020SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block149Part020] using hcert

def TailChunk000Sub000Block149Part021SupportExplicit : Finset ℕ :=
  ([6211] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block149Part021 : ℚ :=
  (964413025 : ℚ) / 1487487246771762

def SurrogateDiagonalTailChunk000Sub000Block149Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6211
    = surrogateDiagTailX0RatChunk000Sub000Block149Part021

theorem surrogateDiagonalTailChunk000Sub000Block149Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block149Part021CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block149Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block149Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block149Part021CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block149Part021SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block149Part021] using hcert

def TailChunk000Sub000Block149Part022SupportExplicit : Finset ℕ :=
  ([6213] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block149Part022 : ℚ :=
  (627511952375 : ℚ) / 285694505605545984

def SurrogateDiagonalTailChunk000Sub000Block149Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6213
    = surrogateDiagTailX0RatChunk000Sub000Block149Part022

theorem surrogateDiagonalTailChunk000Sub000Block149Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block149Part022CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block149Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block149Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block149Part022CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block149Part022SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block149Part022] using hcert

def TailChunk000Sub000Block149Part023SupportExplicit : Finset ℕ :=
  ([6214] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block149Part023 : ℚ :=
  (1087242723925 : ℚ) / 166364121605326848

def SurrogateDiagonalTailChunk000Sub000Block149Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6214
    = surrogateDiagTailX0RatChunk000Sub000Block149Part023

theorem surrogateDiagonalTailChunk000Sub000Block149Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block149Part023CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block149Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block149Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block149Part023CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block149Part023SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block149Part023] using hcert

def TailChunk000Sub000Block149Part024SupportExplicit : Finset ℕ :=
  ([6215] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block149Part024 : ℚ :=
  (13028109131 : ℚ) / 8058030407024640

def SurrogateDiagonalTailChunk000Sub000Block149Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6215
    = surrogateDiagTailX0RatChunk000Sub000Block149Part024

theorem surrogateDiagonalTailChunk000Sub000Block149Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block149Part024CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block149Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block149Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block149Part024CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block149Part024SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block149Part024] using hcert

def surrogateDiagonalTailChunk000Sub000Block149HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block149Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block149Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block149Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block149Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block149Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block149Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block149Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block149Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block149Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block149Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block149Head : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block149Part000
    + surrogateDiagTailX0RatChunk000Sub000Block149Part001
    + surrogateDiagTailX0RatChunk000Sub000Block149Part002
    + surrogateDiagTailX0RatChunk000Sub000Block149Part003
    + surrogateDiagTailX0RatChunk000Sub000Block149Part004
    + surrogateDiagTailX0RatChunk000Sub000Block149Part005
    + surrogateDiagTailX0RatChunk000Sub000Block149Part006
    + surrogateDiagTailX0RatChunk000Sub000Block149Part007
    + surrogateDiagTailX0RatChunk000Sub000Block149Part008
    + surrogateDiagTailX0RatChunk000Sub000Block149Part009

def surrogateDiagonalTailChunk000Sub000Block149MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block149Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block149Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block149Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block149Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block149Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block149Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block149Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block149Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block149Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block149Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block149Mid : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block149Part010
    + surrogateDiagTailX0RatChunk000Sub000Block149Part011
    + surrogateDiagTailX0RatChunk000Sub000Block149Part012
    + surrogateDiagTailX0RatChunk000Sub000Block149Part013
    + surrogateDiagTailX0RatChunk000Sub000Block149Part014
    + surrogateDiagTailX0RatChunk000Sub000Block149Part015
    + surrogateDiagTailX0RatChunk000Sub000Block149Part016
    + surrogateDiagTailX0RatChunk000Sub000Block149Part017
    + surrogateDiagTailX0RatChunk000Sub000Block149Part018
    + surrogateDiagTailX0RatChunk000Sub000Block149Part019

def surrogateDiagonalTailChunk000Sub000Block149TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block149Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block149Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block149Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block149Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block149Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block149Tail : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block149Part020
    + surrogateDiagTailX0RatChunk000Sub000Block149Part021
    + surrogateDiagTailX0RatChunk000Sub000Block149Part022
    + surrogateDiagTailX0RatChunk000Sub000Block149Part023
    + surrogateDiagTailX0RatChunk000Sub000Block149Part024

def surrogateDiagonalTailChunk000Sub000Block149Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub000Block149HeadSum X0
    + surrogateDiagonalTailChunk000Sub000Block149MidSum X0
    + surrogateDiagonalTailChunk000Sub000Block149TailSum X0

def surrogateDiagTailX0RatChunk000Sub000Block149 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block149Part000
    + surrogateDiagTailX0RatChunk000Sub000Block149Part001
    + surrogateDiagTailX0RatChunk000Sub000Block149Part002
    + surrogateDiagTailX0RatChunk000Sub000Block149Part003
    + surrogateDiagTailX0RatChunk000Sub000Block149Part004
    + surrogateDiagTailX0RatChunk000Sub000Block149Part005
    + surrogateDiagTailX0RatChunk000Sub000Block149Part006
    + surrogateDiagTailX0RatChunk000Sub000Block149Part007
    + surrogateDiagTailX0RatChunk000Sub000Block149Part008
    + surrogateDiagTailX0RatChunk000Sub000Block149Part009
    + surrogateDiagTailX0RatChunk000Sub000Block149Part010
    + surrogateDiagTailX0RatChunk000Sub000Block149Part011
    + surrogateDiagTailX0RatChunk000Sub000Block149Part012
    + surrogateDiagTailX0RatChunk000Sub000Block149Part013
    + surrogateDiagTailX0RatChunk000Sub000Block149Part014
    + surrogateDiagTailX0RatChunk000Sub000Block149Part015
    + surrogateDiagTailX0RatChunk000Sub000Block149Part016
    + surrogateDiagTailX0RatChunk000Sub000Block149Part017
    + surrogateDiagTailX0RatChunk000Sub000Block149Part018
    + surrogateDiagTailX0RatChunk000Sub000Block149Part019
    + surrogateDiagTailX0RatChunk000Sub000Block149Part020
    + surrogateDiagTailX0RatChunk000Sub000Block149Part021
    + surrogateDiagTailX0RatChunk000Sub000Block149Part022
    + surrogateDiagTailX0RatChunk000Sub000Block149Part023
    + surrogateDiagTailX0RatChunk000Sub000Block149Part024

theorem surrogateDiagTailX0RatChunk000Sub000Block149_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk000Sub000Block149Head + surrogateDiagTailX0RatChunk000Sub000Block149Mid + surrogateDiagTailX0RatChunk000Sub000Block149Tail =
      surrogateDiagTailX0RatChunk000Sub000Block149 := by
  unfold surrogateDiagTailX0RatChunk000Sub000Block149Head surrogateDiagTailX0RatChunk000Sub000Block149Mid surrogateDiagTailX0RatChunk000Sub000Block149Tail surrogateDiagTailX0RatChunk000Sub000Block149
  ring

def SurrogateDiagonalTailChunk000Sub000Block149HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block149HeadSum X0 = surrogateDiagTailX0RatChunk000Sub000Block149Head

def SurrogateDiagonalTailChunk000Sub000Block149MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block149MidSum X0 = surrogateDiagTailX0RatChunk000Sub000Block149Mid

def SurrogateDiagonalTailChunk000Sub000Block149TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block149TailSum X0 = surrogateDiagTailX0RatChunk000Sub000Block149Tail

theorem surrogateDiagonalTailChunk000Sub000Block149_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk000Sub000Block149HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk000Sub000Block149MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk000Sub000Block149TailCertificateAt X0) :
    surrogateDiagonalTailChunk000Sub000Block149Sum X0 = surrogateDiagTailX0RatChunk000Sub000Block149 := by
  unfold SurrogateDiagonalTailChunk000Sub000Block149HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk000Sub000Block149MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk000Sub000Block149TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk000Sub000Block149Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk000Sub000Block149_eq_head_add_mid_add_tail

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

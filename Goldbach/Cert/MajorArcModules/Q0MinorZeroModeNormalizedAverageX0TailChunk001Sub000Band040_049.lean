import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0TailPilot25

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

open scoped BigOperators

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

/- Generated direct-term certificate blocks for tail chunk 001, subchunk 000, blocks [40,50). -/

/-- Block 040 covers tail-support indices [11000,11025) and q from 18141 to 18181. -/

def TailChunk001Sub000Block040Part000SupportExplicit : Finset ℕ :=
  ([18141] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block040Part000 : ℚ :=
  (1142628643175 : ℚ) / 26729412744415285824

def SurrogateDiagonalTailChunk001Sub000Block040Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18141
    = surrogateDiagTailX0RatChunk001Sub000Block040Part000

theorem surrogateDiagonalTailChunk001Sub000Block040Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block040Part000CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block040Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block040Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block040Part000CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block040Part000SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block040Part000] using hcert

def TailChunk001Sub000Block040Part001SupportExplicit : Finset ℕ :=
  ([18142] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block040Part001 : ℚ :=
  (36964641425 : ℚ) / 7607344867043180544

def SurrogateDiagonalTailChunk001Sub000Block040Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18142
    = surrogateDiagTailX0RatChunk001Sub000Block040Part001

theorem surrogateDiagonalTailChunk001Sub000Block040Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block040Part001CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block040Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block040Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block040Part001CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block040Part001SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block040Part001] using hcert

def TailChunk001Sub000Block040Part002SupportExplicit : Finset ℕ :=
  ([18143] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block040Part002 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block040Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18143
    = surrogateDiagTailX0RatChunk001Sub000Block040Part002

theorem surrogateDiagonalTailChunk001Sub000Block040Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block040Part002CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block040Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block040Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block040Part002CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block040Part002SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block040Part002] using hcert

def TailChunk001Sub000Block040Part003SupportExplicit : Finset ℕ :=
  ([18145] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block040Part003 : ℚ :=
  (68296264411 : ℚ) / 3502928233333555200

def SurrogateDiagonalTailChunk001Sub000Block040Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18145
    = surrogateDiagTailX0RatChunk001Sub000Block040Part003

theorem surrogateDiagonalTailChunk001Sub000Block040Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block040Part003CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block040Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block040Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block040Part003CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block040Part003SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block040Part003] using hcert

def TailChunk001Sub000Block040Part004SupportExplicit : Finset ℕ :=
  ([18146] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block040Part004 : ℚ :=
  (6505721 : ℚ) / 1245446055403200

def SurrogateDiagonalTailChunk001Sub000Block040Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18146
    = surrogateDiagTailX0RatChunk001Sub000Block040Part004

theorem surrogateDiagonalTailChunk001Sub000Block040Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block040Part004CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block040Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block040Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block040Part004CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block040Part004SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block040Part004] using hcert

def TailChunk001Sub000Block040Part005SupportExplicit : Finset ℕ :=
  ([18147] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block040Part005 : ℚ :=
  (752459753025 : ℚ) / 14720463182607947776

def SurrogateDiagonalTailChunk001Sub000Block040Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18147
    = surrogateDiagTailX0RatChunk001Sub000Block040Part005

theorem surrogateDiagonalTailChunk001Sub000Block040Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block040Part005CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block040Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block040Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block040Part005CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block040Part005SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block040Part005] using hcert

def TailChunk001Sub000Block040Part006SupportExplicit : Finset ℕ :=
  ([18149] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block040Part006 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block040Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18149
    = surrogateDiagTailX0RatChunk001Sub000Block040Part006

theorem surrogateDiagonalTailChunk001Sub000Block040Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block040Part006CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block040Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block040Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block040Part006CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block040Part006SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block040Part006] using hcert

def TailChunk001Sub000Block040Part007SupportExplicit : Finset ℕ :=
  ([18151] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block040Part007 : ℚ :=
  (420757427675 : ℚ) / 73137793435019771904

def SurrogateDiagonalTailChunk001Sub000Block040Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18151
    = surrogateDiagTailX0RatChunk001Sub000Block040Part007

theorem surrogateDiagonalTailChunk001Sub000Block040Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block040Part007CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block040Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block040Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block040Part007CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block040Part007SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block040Part007] using hcert

def TailChunk001Sub000Block040Part008SupportExplicit : Finset ℕ :=
  ([18154] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block040Part008 : ℚ :=
  (17630358625 : ℚ) / 2427314833705402368

def SurrogateDiagonalTailChunk001Sub000Block040Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18154
    = surrogateDiagTailX0RatChunk001Sub000Block040Part008

theorem surrogateDiagonalTailChunk001Sub000Block040Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block040Part008CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block040Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block040Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block040Part008CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block040Part008SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block040Part008] using hcert

def TailChunk001Sub000Block040Part009SupportExplicit : Finset ℕ :=
  ([18155] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block040Part009 : ℚ :=
  (21973774843 : ℚ) / 1481944915189094400

def SurrogateDiagonalTailChunk001Sub000Block040Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18155
    = surrogateDiagTailX0RatChunk001Sub000Block040Part009

theorem surrogateDiagonalTailChunk001Sub000Block040Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block040Part009CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block040Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block040Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block040Part009CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block040Part009SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block040Part009] using hcert

def TailChunk001Sub000Block040Part010SupportExplicit : Finset ℕ :=
  ([18157] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block040Part010 : ℚ :=
  (227684839 : ℚ) / 560331636950606400

def SurrogateDiagonalTailChunk001Sub000Block040Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18157
    = surrogateDiagTailX0RatChunk001Sub000Block040Part010

theorem surrogateDiagonalTailChunk001Sub000Block040Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block040Part010CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block040Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block040Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block040Part010CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block040Part010SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block040Part010] using hcert

def TailChunk001Sub000Block040Part011SupportExplicit : Finset ℕ :=
  ([18158] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block040Part011 : ℚ :=
  (421526490325 : ℚ) / 9142224179377471488

def SurrogateDiagonalTailChunk001Sub000Block040Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18158
    = surrogateDiagTailX0RatChunk001Sub000Block040Part011

theorem surrogateDiagonalTailChunk001Sub000Block040Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block040Part011CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block040Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block040Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block040Part011CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block040Part011SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block040Part011] using hcert

def TailChunk001Sub000Block040Part012SupportExplicit : Finset ℕ :=
  ([18159] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block040Part012 : ℚ :=
  (286224254525 : ℚ) / 6708918744963983616

def SurrogateDiagonalTailChunk001Sub000Block040Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18159
    = surrogateDiagTailX0RatChunk001Sub000Block040Part012

theorem surrogateDiagonalTailChunk001Sub000Block040Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block040Part012CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block040Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block040Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block040Part012CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block040Part012SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block040Part012] using hcert

def TailChunk001Sub000Block040Part013SupportExplicit : Finset ℕ :=
  ([18161] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block040Part013 : ℚ :=
  (3578305777 : ℚ) / 522749967961374720

def SurrogateDiagonalTailChunk001Sub000Block040Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18161
    = surrogateDiagTailX0RatChunk001Sub000Block040Part013

theorem surrogateDiagonalTailChunk001Sub000Block040Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block040Part013CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block040Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block040Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block040Part013CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block040Part013SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block040Part013] using hcert

def TailChunk001Sub000Block040Part014SupportExplicit : Finset ℕ :=
  ([18163] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block040Part014 : ℚ :=
  (2930988299 : ℚ) / 4886364917055897600

def SurrogateDiagonalTailChunk001Sub000Block040Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18163
    = surrogateDiagTailX0RatChunk001Sub000Block040Part014

theorem surrogateDiagonalTailChunk001Sub000Block040Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block040Part014CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block040Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block040Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block040Part014CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block040Part014SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block040Part014] using hcert

def TailChunk001Sub000Block040Part015SupportExplicit : Finset ℕ :=
  ([18165] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block040Part015 : ℚ :=
  (2111357934625 : ℚ) / 11617310472193179648

def SurrogateDiagonalTailChunk001Sub000Block040Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18165
    = surrogateDiagTailX0RatChunk001Sub000Block040Part015

theorem surrogateDiagonalTailChunk001Sub000Block040Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block040Part015CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block040Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block040Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block040Part015CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block040Part015SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block040Part015] using hcert

def TailChunk001Sub000Block040Part016SupportExplicit : Finset ℕ :=
  ([18166] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block040Part016 : ℚ :=
  (265764779 : ℚ) / 39265579904071680

def SurrogateDiagonalTailChunk001Sub000Block040Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18166
    = surrogateDiagTailX0RatChunk001Sub000Block040Part016

theorem surrogateDiagonalTailChunk001Sub000Block040Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block040Part016CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block040Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block040Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block040Part016CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block040Part016SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block040Part016] using hcert

def TailChunk001Sub000Block040Part017SupportExplicit : Finset ℕ :=
  ([18167] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block040Part017 : ℚ :=
  (32206529 : ℚ) / 48422942634076416

def SurrogateDiagonalTailChunk001Sub000Block040Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18167
    = surrogateDiagTailX0RatChunk001Sub000Block040Part017

theorem surrogateDiagonalTailChunk001Sub000Block040Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block040Part017CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block040Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block040Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block040Part017CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block040Part017SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block040Part017] using hcert

def TailChunk001Sub000Block040Part018SupportExplicit : Finset ℕ :=
  ([18169] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block040Part018 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block040Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18169
    = surrogateDiagTailX0RatChunk001Sub000Block040Part018

theorem surrogateDiagonalTailChunk001Sub000Block040Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block040Part018CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block040Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block040Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block040Part018CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block040Part018SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block040Part018] using hcert

def TailChunk001Sub000Block040Part019SupportExplicit : Finset ℕ :=
  ([18170] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block040Part019 : ℚ :=
  (492987596875 : ℚ) / 5550549221201707008

def SurrogateDiagonalTailChunk001Sub000Block040Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18170
    = surrogateDiagTailX0RatChunk001Sub000Block040Part019

theorem surrogateDiagonalTailChunk001Sub000Block040Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block040Part019CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block040Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block040Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block040Part019CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block040Part019SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block040Part019] using hcert

def TailChunk001Sub000Block040Part020SupportExplicit : Finset ℕ :=
  ([18173] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block040Part020 : ℚ :=
  (361158451525 : ℚ) / 213202258165411872768

def SurrogateDiagonalTailChunk001Sub000Block040Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18173
    = surrogateDiagTailX0RatChunk001Sub000Block040Part020

theorem surrogateDiagonalTailChunk001Sub000Block040Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block040Part020CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block040Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block040Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block040Part020CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block040Part020SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block040Part020] using hcert

def TailChunk001Sub000Block040Part021SupportExplicit : Finset ℕ :=
  ([18174] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block040Part021 : ℚ :=
  (633220261975 : ℚ) / 2403387318560882688

def SurrogateDiagonalTailChunk001Sub000Block040Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18174
    = surrogateDiagTailX0RatChunk001Sub000Block040Part021

theorem surrogateDiagonalTailChunk001Sub000Block040Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block040Part021CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block040Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block040Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block040Part021CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block040Part021SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block040Part021] using hcert

def TailChunk001Sub000Block040Part022SupportExplicit : Finset ℕ :=
  ([18177] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block040Part022 : ℚ :=
  (189358706275 : ℚ) / 4050895041240367104

def SurrogateDiagonalTailChunk001Sub000Block040Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18177
    = surrogateDiagTailX0RatChunk001Sub000Block040Part022

theorem surrogateDiagonalTailChunk001Sub000Block040Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block040Part022CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block040Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block040Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block040Part022CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block040Part022SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block040Part022] using hcert

def TailChunk001Sub000Block040Part023SupportExplicit : Finset ℕ :=
  ([18178] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block040Part023 : ℚ :=
  (433289611 : ℚ) / 103654333377331200

def SurrogateDiagonalTailChunk001Sub000Block040Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18178
    = surrogateDiagTailX0RatChunk001Sub000Block040Part023

theorem surrogateDiagonalTailChunk001Sub000Block040Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block040Part023CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block040Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block040Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block040Part023CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block040Part023SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block040Part023] using hcert

def TailChunk001Sub000Block040Part024SupportExplicit : Finset ℕ :=
  ([18181] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block040Part024 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block040Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18181
    = surrogateDiagTailX0RatChunk001Sub000Block040Part024

theorem surrogateDiagonalTailChunk001Sub000Block040Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block040Part024CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block040Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block040Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block040Part024CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block040Part024SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block040Part024] using hcert

def surrogateDiagonalTailChunk001Sub000Block040HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block040Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block040Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block040Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block040Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block040Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block040Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block040Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block040Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block040Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block040Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block040Head : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block040Part000
    + surrogateDiagTailX0RatChunk001Sub000Block040Part001
    + surrogateDiagTailX0RatChunk001Sub000Block040Part002
    + surrogateDiagTailX0RatChunk001Sub000Block040Part003
    + surrogateDiagTailX0RatChunk001Sub000Block040Part004
    + surrogateDiagTailX0RatChunk001Sub000Block040Part005
    + surrogateDiagTailX0RatChunk001Sub000Block040Part006
    + surrogateDiagTailX0RatChunk001Sub000Block040Part007
    + surrogateDiagTailX0RatChunk001Sub000Block040Part008
    + surrogateDiagTailX0RatChunk001Sub000Block040Part009

def surrogateDiagonalTailChunk001Sub000Block040MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block040Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block040Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block040Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block040Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block040Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block040Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block040Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block040Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block040Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block040Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block040Mid : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block040Part010
    + surrogateDiagTailX0RatChunk001Sub000Block040Part011
    + surrogateDiagTailX0RatChunk001Sub000Block040Part012
    + surrogateDiagTailX0RatChunk001Sub000Block040Part013
    + surrogateDiagTailX0RatChunk001Sub000Block040Part014
    + surrogateDiagTailX0RatChunk001Sub000Block040Part015
    + surrogateDiagTailX0RatChunk001Sub000Block040Part016
    + surrogateDiagTailX0RatChunk001Sub000Block040Part017
    + surrogateDiagTailX0RatChunk001Sub000Block040Part018
    + surrogateDiagTailX0RatChunk001Sub000Block040Part019

def surrogateDiagonalTailChunk001Sub000Block040TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block040Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block040Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block040Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block040Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block040Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block040Tail : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block040Part020
    + surrogateDiagTailX0RatChunk001Sub000Block040Part021
    + surrogateDiagTailX0RatChunk001Sub000Block040Part022
    + surrogateDiagTailX0RatChunk001Sub000Block040Part023
    + surrogateDiagTailX0RatChunk001Sub000Block040Part024

def surrogateDiagonalTailChunk001Sub000Block040Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk001Sub000Block040HeadSum X0
    + surrogateDiagonalTailChunk001Sub000Block040MidSum X0
    + surrogateDiagonalTailChunk001Sub000Block040TailSum X0

def surrogateDiagTailX0RatChunk001Sub000Block040 : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block040Part000
    + surrogateDiagTailX0RatChunk001Sub000Block040Part001
    + surrogateDiagTailX0RatChunk001Sub000Block040Part002
    + surrogateDiagTailX0RatChunk001Sub000Block040Part003
    + surrogateDiagTailX0RatChunk001Sub000Block040Part004
    + surrogateDiagTailX0RatChunk001Sub000Block040Part005
    + surrogateDiagTailX0RatChunk001Sub000Block040Part006
    + surrogateDiagTailX0RatChunk001Sub000Block040Part007
    + surrogateDiagTailX0RatChunk001Sub000Block040Part008
    + surrogateDiagTailX0RatChunk001Sub000Block040Part009
    + surrogateDiagTailX0RatChunk001Sub000Block040Part010
    + surrogateDiagTailX0RatChunk001Sub000Block040Part011
    + surrogateDiagTailX0RatChunk001Sub000Block040Part012
    + surrogateDiagTailX0RatChunk001Sub000Block040Part013
    + surrogateDiagTailX0RatChunk001Sub000Block040Part014
    + surrogateDiagTailX0RatChunk001Sub000Block040Part015
    + surrogateDiagTailX0RatChunk001Sub000Block040Part016
    + surrogateDiagTailX0RatChunk001Sub000Block040Part017
    + surrogateDiagTailX0RatChunk001Sub000Block040Part018
    + surrogateDiagTailX0RatChunk001Sub000Block040Part019
    + surrogateDiagTailX0RatChunk001Sub000Block040Part020
    + surrogateDiagTailX0RatChunk001Sub000Block040Part021
    + surrogateDiagTailX0RatChunk001Sub000Block040Part022
    + surrogateDiagTailX0RatChunk001Sub000Block040Part023
    + surrogateDiagTailX0RatChunk001Sub000Block040Part024

theorem surrogateDiagTailX0RatChunk001Sub000Block040_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk001Sub000Block040Head + surrogateDiagTailX0RatChunk001Sub000Block040Mid + surrogateDiagTailX0RatChunk001Sub000Block040Tail =
      surrogateDiagTailX0RatChunk001Sub000Block040 := by
  unfold surrogateDiagTailX0RatChunk001Sub000Block040Head surrogateDiagTailX0RatChunk001Sub000Block040Mid surrogateDiagTailX0RatChunk001Sub000Block040Tail surrogateDiagTailX0RatChunk001Sub000Block040
  ring

def SurrogateDiagonalTailChunk001Sub000Block040HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block040HeadSum X0 = surrogateDiagTailX0RatChunk001Sub000Block040Head

def SurrogateDiagonalTailChunk001Sub000Block040MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block040MidSum X0 = surrogateDiagTailX0RatChunk001Sub000Block040Mid

def SurrogateDiagonalTailChunk001Sub000Block040TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block040TailSum X0 = surrogateDiagTailX0RatChunk001Sub000Block040Tail

theorem surrogateDiagonalTailChunk001Sub000Block040_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk001Sub000Block040HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk001Sub000Block040MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk001Sub000Block040TailCertificateAt X0) :
    surrogateDiagonalTailChunk001Sub000Block040Sum X0 = surrogateDiagTailX0RatChunk001Sub000Block040 := by
  unfold SurrogateDiagonalTailChunk001Sub000Block040HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk001Sub000Block040MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk001Sub000Block040TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk001Sub000Block040Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk001Sub000Block040_eq_head_add_mid_add_tail

/-- Block 041 covers tail-support indices [11025,11050) and q from 18182 to 18218. -/

def TailChunk001Sub000Block041Part000SupportExplicit : Finset ℕ :=
  ([18182] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block041Part000 : ℚ :=
  (2066157025 : ℚ) / 6828768390191922

def SurrogateDiagonalTailChunk001Sub000Block041Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18182
    = surrogateDiagTailX0RatChunk001Sub000Block041Part000

theorem surrogateDiagonalTailChunk001Sub000Block041Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block041Part000CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block041Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block041Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block041Part000CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block041Part000SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block041Part000] using hcert

def TailChunk001Sub000Block041Part001SupportExplicit : Finset ℕ :=
  ([18183] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block041Part001 : ℚ :=
  (21292174147 : ℚ) / 258148132326604800

def SurrogateDiagonalTailChunk001Sub000Block041Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18183
    = surrogateDiagTailX0RatChunk001Sub000Block041Part001

theorem surrogateDiagonalTailChunk001Sub000Block041Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block041Part001CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block041Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block041Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block041Part001CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block041Part001SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block041Part001] using hcert

def TailChunk001Sub000Block041Part002SupportExplicit : Finset ℕ :=
  ([18185] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block041Part002 : ℚ :=
  (827531732875 : ℚ) / 111882541304904450048

def SurrogateDiagonalTailChunk001Sub000Block041Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18185
    = surrogateDiagTailX0RatChunk001Sub000Block041Part002

theorem surrogateDiagonalTailChunk001Sub000Block041Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block041Part002CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block041Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block041Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block041Part002CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block041Part002SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block041Part002] using hcert

def TailChunk001Sub000Block041Part003SupportExplicit : Finset ℕ :=
  ([18186] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block041Part003 : ℚ :=
  (2325222574975 : ℚ) / 1805871442839994368

def SurrogateDiagonalTailChunk001Sub000Block041Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18186
    = surrogateDiagTailX0RatChunk001Sub000Block041Part003

theorem surrogateDiagonalTailChunk001Sub000Block041Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block041Part003CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block041Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block041Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block041Part003CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block041Part003SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block041Part003] using hcert

def TailChunk001Sub000Block041Part004SupportExplicit : Finset ℕ :=
  ([18187] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block041Part004 : ℚ :=
  (92514374575 : ℚ) / 49513147787426959872

def SurrogateDiagonalTailChunk001Sub000Block041Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18187
    = surrogateDiagTailX0RatChunk001Sub000Block041Part004

theorem surrogateDiagonalTailChunk001Sub000Block041Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block041Part004CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block041Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block041Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block041Part004CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block041Part004SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block041Part004] using hcert

def TailChunk001Sub000Block041Part005SupportExplicit : Finset ℕ :=
  ([18190] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block041Part005 : ℚ :=
  (842842503625 : ℚ) / 1324067801417121792

def SurrogateDiagonalTailChunk001Sub000Block041Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18190
    = surrogateDiagTailX0RatChunk001Sub000Block041Part005

theorem surrogateDiagonalTailChunk001Sub000Block041Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block041Part005CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block041Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block041Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block041Part005CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block041Part005SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block041Part005] using hcert

def TailChunk001Sub000Block041Part006SupportExplicit : Finset ℕ :=
  ([18191] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block041Part006 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block041Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18191
    = surrogateDiagTailX0RatChunk001Sub000Block041Part006

theorem surrogateDiagonalTailChunk001Sub000Block041Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block041Part006CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block041Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block041Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block041Part006CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block041Part006SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block041Part006] using hcert

def TailChunk001Sub000Block041Part007SupportExplicit : Finset ℕ :=
  ([18193] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block041Part007 : ℚ :=
  (7798987775 : ℚ) / 933221433430573056

def SurrogateDiagonalTailChunk001Sub000Block041Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18193
    = surrogateDiagTailX0RatChunk001Sub000Block041Part007

theorem surrogateDiagonalTailChunk001Sub000Block041Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block041Part007CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block041Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block041Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block041Part007CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block041Part007SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block041Part007] using hcert

def TailChunk001Sub000Block041Part008SupportExplicit : Finset ℕ :=
  ([18194] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block041Part008 : ℚ :=
  (2987493573 : ℚ) / 7759894004733920

def SurrogateDiagonalTailChunk001Sub000Block041Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18194
    = surrogateDiagTailX0RatChunk001Sub000Block041Part008

theorem surrogateDiagonalTailChunk001Sub000Block041Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block041Part008CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block041Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block041Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block041Part008CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block041Part008SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block041Part008] using hcert

def TailChunk001Sub000Block041Part009SupportExplicit : Finset ℕ :=
  ([18195] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block041Part009 : ℚ :=
  (168534012275 : ℚ) / 1841687922714476544

def SurrogateDiagonalTailChunk001Sub000Block041Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18195
    = surrogateDiagTailX0RatChunk001Sub000Block041Part009

theorem surrogateDiagonalTailChunk001Sub000Block041Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block041Part009CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block041Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block041Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block041Part009CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block041Part009SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block041Part009] using hcert

def TailChunk001Sub000Block041Part010SupportExplicit : Finset ℕ :=
  ([18197] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block041Part010 : ℚ :=
  (8088455383 : ℚ) / 9553496155263619200

def SurrogateDiagonalTailChunk001Sub000Block041Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18197
    = surrogateDiagTailX0RatChunk001Sub000Block041Part010

theorem surrogateDiagonalTailChunk001Sub000Block041Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block041Part010CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block041Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block041Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block041Part010CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block041Part010SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block041Part010] using hcert

def TailChunk001Sub000Block041Part011SupportExplicit : Finset ℕ :=
  ([18199] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block041Part011 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block041Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18199
    = surrogateDiagTailX0RatChunk001Sub000Block041Part011

theorem surrogateDiagonalTailChunk001Sub000Block041Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block041Part011CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block041Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block041Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block041Part011CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block041Part011SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block041Part011] using hcert

def TailChunk001Sub000Block041Part012SupportExplicit : Finset ℕ :=
  ([18201] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block041Part012 : ℚ :=
  (1150198642925 : ℚ) / 27084852184834234944

def SurrogateDiagonalTailChunk001Sub000Block041Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18201
    = surrogateDiagTailX0RatChunk001Sub000Block041Part012

theorem surrogateDiagonalTailChunk001Sub000Block041Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block041Part012CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block041Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block041Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block041Part012CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block041Part012SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block041Part012] using hcert

def TailChunk001Sub000Block041Part013SupportExplicit : Finset ℕ :=
  ([18202] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block041Part013 : ℚ :=
  (1193993901175 : ℚ) / 3425851032175955232

def SurrogateDiagonalTailChunk001Sub000Block041Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18202
    = surrogateDiagTailX0RatChunk001Sub000Block041Part013

theorem surrogateDiagonalTailChunk001Sub000Block041Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block041Part013CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block041Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block041Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block041Part013CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block041Part013SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block041Part013] using hcert

def TailChunk001Sub000Block041Part014SupportExplicit : Finset ℕ :=
  ([18203] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block041Part014 : ℚ :=
  (83509123225 : ℚ) / 258317740339969148928

def SurrogateDiagonalTailChunk001Sub000Block041Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18203
    = surrogateDiagTailX0RatChunk001Sub000Block041Part014

theorem surrogateDiagonalTailChunk001Sub000Block041Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block041Part014CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block041Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block041Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block041Part014CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block041Part014SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block041Part014] using hcert

def TailChunk001Sub000Block041Part015SupportExplicit : Finset ℕ :=
  ([18205] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block041Part015 : ℚ :=
  (5473748273 : ℚ) / 379570618944000000

def SurrogateDiagonalTailChunk001Sub000Block041Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18205
    = surrogateDiagTailX0RatChunk001Sub000Block041Part015

theorem surrogateDiagonalTailChunk001Sub000Block041Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block041Part015CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block041Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block041Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block041Part015CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block041Part015SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block041Part015] using hcert

def TailChunk001Sub000Block041Part016SupportExplicit : Finset ℕ :=
  ([18206] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block041Part016 : ℚ :=
  (1294759515625 : ℚ) / 4290562100663976402

def SurrogateDiagonalTailChunk001Sub000Block041Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18206
    = surrogateDiagTailX0RatChunk001Sub000Block041Part016

theorem surrogateDiagonalTailChunk001Sub000Block041Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block041Part016CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block041Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block041Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block041Part016CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block041Part016SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block041Part016] using hcert

def TailChunk001Sub000Block041Part017SupportExplicit : Finset ℕ :=
  ([18209] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block041Part017 : ℚ :=
  (132801547 : ℚ) / 414416078086128768

def SurrogateDiagonalTailChunk001Sub000Block041Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18209
    = surrogateDiagTailX0RatChunk001Sub000Block041Part017

theorem surrogateDiagonalTailChunk001Sub000Block041Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block041Part017CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block041Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block041Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block041Part017CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block041Part017SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block041Part017] using hcert

def TailChunk001Sub000Block041Part018SupportExplicit : Finset ℕ :=
  ([18210] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block041Part018 : ℚ :=
  (2114449897225 : ℚ) / 1381265942035857408

def SurrogateDiagonalTailChunk001Sub000Block041Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18210
    = surrogateDiagTailX0RatChunk001Sub000Block041Part018

theorem surrogateDiagonalTailChunk001Sub000Block041Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block041Part018CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block041Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block041Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block041Part018CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block041Part018SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block041Part018] using hcert

def TailChunk001Sub000Block041Part019SupportExplicit : Finset ℕ :=
  ([18211] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block041Part019 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block041Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18211
    = surrogateDiagTailX0RatChunk001Sub000Block041Part019

theorem surrogateDiagonalTailChunk001Sub000Block041Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block041Part019CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block041Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block041Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block041Part019CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block041Part019SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block041Part019] using hcert

def TailChunk001Sub000Block041Part020SupportExplicit : Finset ℕ :=
  ([18213] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block041Part020 : ℚ :=
  (3233764075 : ℚ) / 55967810423980032

def SurrogateDiagonalTailChunk001Sub000Block041Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18213
    = surrogateDiagTailX0RatChunk001Sub000Block041Part020

theorem surrogateDiagonalTailChunk001Sub000Block041Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block041Part020CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block041Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block041Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block041Part020CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block041Part020SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block041Part020] using hcert

def TailChunk001Sub000Block041Part021SupportExplicit : Finset ℕ :=
  ([18214] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block041Part021 : ℚ :=
  (9159734531 : ℚ) / 20568032784000000

def SurrogateDiagonalTailChunk001Sub000Block041Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18214
    = surrogateDiagTailX0RatChunk001Sub000Block041Part021

theorem surrogateDiagonalTailChunk001Sub000Block041Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block041Part021CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block041Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block041Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block041Part021CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block041Part021SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block041Part021] using hcert

def TailChunk001Sub000Block041Part022SupportExplicit : Finset ℕ :=
  ([18215] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block041Part022 : ℚ :=
  (830260982125 : ℚ) / 112622869906060658688

def SurrogateDiagonalTailChunk001Sub000Block041Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18215
    = surrogateDiagTailX0RatChunk001Sub000Block041Part022

theorem surrogateDiagonalTailChunk001Sub000Block041Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block041Part022CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block041Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block041Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block041Part022CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block041Part022SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block041Part022] using hcert

def TailChunk001Sub000Block041Part023SupportExplicit : Finset ℕ :=
  ([18217] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block041Part023 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block041Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18217
    = surrogateDiagTailX0RatChunk001Sub000Block041Part023

theorem surrogateDiagonalTailChunk001Sub000Block041Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block041Part023CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block041Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block041Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block041Part023CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block041Part023SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block041Part023] using hcert

def TailChunk001Sub000Block041Part024SupportExplicit : Finset ℕ :=
  ([18218] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block041Part024 : ℚ :=
  (1296466890625 : ℚ) / 4301886573824270112

def SurrogateDiagonalTailChunk001Sub000Block041Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18218
    = surrogateDiagTailX0RatChunk001Sub000Block041Part024

theorem surrogateDiagonalTailChunk001Sub000Block041Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block041Part024CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block041Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block041Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block041Part024CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block041Part024SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block041Part024] using hcert

def surrogateDiagonalTailChunk001Sub000Block041HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block041Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block041Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block041Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block041Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block041Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block041Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block041Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block041Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block041Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block041Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block041Head : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block041Part000
    + surrogateDiagTailX0RatChunk001Sub000Block041Part001
    + surrogateDiagTailX0RatChunk001Sub000Block041Part002
    + surrogateDiagTailX0RatChunk001Sub000Block041Part003
    + surrogateDiagTailX0RatChunk001Sub000Block041Part004
    + surrogateDiagTailX0RatChunk001Sub000Block041Part005
    + surrogateDiagTailX0RatChunk001Sub000Block041Part006
    + surrogateDiagTailX0RatChunk001Sub000Block041Part007
    + surrogateDiagTailX0RatChunk001Sub000Block041Part008
    + surrogateDiagTailX0RatChunk001Sub000Block041Part009

def surrogateDiagonalTailChunk001Sub000Block041MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block041Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block041Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block041Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block041Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block041Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block041Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block041Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block041Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block041Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block041Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block041Mid : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block041Part010
    + surrogateDiagTailX0RatChunk001Sub000Block041Part011
    + surrogateDiagTailX0RatChunk001Sub000Block041Part012
    + surrogateDiagTailX0RatChunk001Sub000Block041Part013
    + surrogateDiagTailX0RatChunk001Sub000Block041Part014
    + surrogateDiagTailX0RatChunk001Sub000Block041Part015
    + surrogateDiagTailX0RatChunk001Sub000Block041Part016
    + surrogateDiagTailX0RatChunk001Sub000Block041Part017
    + surrogateDiagTailX0RatChunk001Sub000Block041Part018
    + surrogateDiagTailX0RatChunk001Sub000Block041Part019

def surrogateDiagonalTailChunk001Sub000Block041TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block041Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block041Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block041Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block041Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block041Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block041Tail : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block041Part020
    + surrogateDiagTailX0RatChunk001Sub000Block041Part021
    + surrogateDiagTailX0RatChunk001Sub000Block041Part022
    + surrogateDiagTailX0RatChunk001Sub000Block041Part023
    + surrogateDiagTailX0RatChunk001Sub000Block041Part024

def surrogateDiagonalTailChunk001Sub000Block041Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk001Sub000Block041HeadSum X0
    + surrogateDiagonalTailChunk001Sub000Block041MidSum X0
    + surrogateDiagonalTailChunk001Sub000Block041TailSum X0

def surrogateDiagTailX0RatChunk001Sub000Block041 : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block041Part000
    + surrogateDiagTailX0RatChunk001Sub000Block041Part001
    + surrogateDiagTailX0RatChunk001Sub000Block041Part002
    + surrogateDiagTailX0RatChunk001Sub000Block041Part003
    + surrogateDiagTailX0RatChunk001Sub000Block041Part004
    + surrogateDiagTailX0RatChunk001Sub000Block041Part005
    + surrogateDiagTailX0RatChunk001Sub000Block041Part006
    + surrogateDiagTailX0RatChunk001Sub000Block041Part007
    + surrogateDiagTailX0RatChunk001Sub000Block041Part008
    + surrogateDiagTailX0RatChunk001Sub000Block041Part009
    + surrogateDiagTailX0RatChunk001Sub000Block041Part010
    + surrogateDiagTailX0RatChunk001Sub000Block041Part011
    + surrogateDiagTailX0RatChunk001Sub000Block041Part012
    + surrogateDiagTailX0RatChunk001Sub000Block041Part013
    + surrogateDiagTailX0RatChunk001Sub000Block041Part014
    + surrogateDiagTailX0RatChunk001Sub000Block041Part015
    + surrogateDiagTailX0RatChunk001Sub000Block041Part016
    + surrogateDiagTailX0RatChunk001Sub000Block041Part017
    + surrogateDiagTailX0RatChunk001Sub000Block041Part018
    + surrogateDiagTailX0RatChunk001Sub000Block041Part019
    + surrogateDiagTailX0RatChunk001Sub000Block041Part020
    + surrogateDiagTailX0RatChunk001Sub000Block041Part021
    + surrogateDiagTailX0RatChunk001Sub000Block041Part022
    + surrogateDiagTailX0RatChunk001Sub000Block041Part023
    + surrogateDiagTailX0RatChunk001Sub000Block041Part024

theorem surrogateDiagTailX0RatChunk001Sub000Block041_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk001Sub000Block041Head + surrogateDiagTailX0RatChunk001Sub000Block041Mid + surrogateDiagTailX0RatChunk001Sub000Block041Tail =
      surrogateDiagTailX0RatChunk001Sub000Block041 := by
  unfold surrogateDiagTailX0RatChunk001Sub000Block041Head surrogateDiagTailX0RatChunk001Sub000Block041Mid surrogateDiagTailX0RatChunk001Sub000Block041Tail surrogateDiagTailX0RatChunk001Sub000Block041
  ring

def SurrogateDiagonalTailChunk001Sub000Block041HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block041HeadSum X0 = surrogateDiagTailX0RatChunk001Sub000Block041Head

def SurrogateDiagonalTailChunk001Sub000Block041MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block041MidSum X0 = surrogateDiagTailX0RatChunk001Sub000Block041Mid

def SurrogateDiagonalTailChunk001Sub000Block041TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block041TailSum X0 = surrogateDiagTailX0RatChunk001Sub000Block041Tail

theorem surrogateDiagonalTailChunk001Sub000Block041_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk001Sub000Block041HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk001Sub000Block041MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk001Sub000Block041TailCertificateAt X0) :
    surrogateDiagonalTailChunk001Sub000Block041Sum X0 = surrogateDiagTailX0RatChunk001Sub000Block041 := by
  unfold SurrogateDiagonalTailChunk001Sub000Block041HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk001Sub000Block041MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk001Sub000Block041TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk001Sub000Block041Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk001Sub000Block041_eq_head_add_mid_add_tail

/-- Block 042 covers tail-support indices [11050,11075) and q from 18219 to 18257. -/

def TailChunk001Sub000Block042Part000SupportExplicit : Finset ℕ :=
  ([18219] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block042Part000 : ℚ :=
  (576237258925 : ℚ) / 13596085961716211712

def SurrogateDiagonalTailChunk001Sub000Block042Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18219
    = surrogateDiagTailX0RatChunk001Sub000Block042Part000

theorem surrogateDiagonalTailChunk001Sub000Block042Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block042Part000CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block042Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block042Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block042Part000CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block042Part000SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block042Part000] using hcert

def TailChunk001Sub000Block042Part001SupportExplicit : Finset ℕ :=
  ([18221] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block042Part001 : ℚ :=
  (1025030838175 : ℚ) / 116379775291233927168

def SurrogateDiagonalTailChunk001Sub000Block042Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18221
    = surrogateDiagTailX0RatChunk001Sub000Block042Part001

theorem surrogateDiagonalTailChunk001Sub000Block042Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block042Part001CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block042Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block042Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block042Part001CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block042Part001SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block042Part001] using hcert

def TailChunk001Sub000Block042Part002SupportExplicit : Finset ℕ :=
  ([18222] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block042Part002 : ℚ :=
  (1440745363175 : ℚ) / 1699510745214526464

def SurrogateDiagonalTailChunk001Sub000Block042Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18222
    = surrogateDiagTailX0RatChunk001Sub000Block042Part002

theorem surrogateDiagonalTailChunk001Sub000Block042Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block042Part002CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block042Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block042Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block042Part002CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block042Part002SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block042Part002] using hcert

def TailChunk001Sub000Block042Part003SupportExplicit : Finset ℕ :=
  ([18223] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block042Part003 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block042Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18223
    = surrogateDiagTailX0RatChunk001Sub000Block042Part003

theorem surrogateDiagonalTailChunk001Sub000Block042Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block042Part003CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block042Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block042Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block042Part003CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block042Part003SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block042Part003] using hcert

def TailChunk001Sub000Block042Part004SupportExplicit : Finset ℕ :=
  ([18226] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block042Part004 : ℚ :=
  (183927716551 : ℚ) / 497970934272000000

def SurrogateDiagonalTailChunk001Sub000Block042Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18226
    = surrogateDiagTailX0RatChunk001Sub000Block042Part004

theorem surrogateDiagonalTailChunk001Sub000Block042Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block042Part004CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block042Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block042Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block042Part004CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block042Part004SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block042Part004] using hcert

def TailChunk001Sub000Block042Part005SupportExplicit : Finset ℕ :=
  ([18227] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block042Part005 : ℚ :=
  (20684390713 : ℚ) / 7521910818243379200

def SurrogateDiagonalTailChunk001Sub000Block042Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18227
    = surrogateDiagTailX0RatChunk001Sub000Block042Part005

theorem surrogateDiagonalTailChunk001Sub000Block042Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block042Part005CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block042Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block042Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block042Part005CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block042Part005SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block042Part005] using hcert

def TailChunk001Sub000Block042Part006SupportExplicit : Finset ℕ :=
  ([18229] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block042Part006 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block042Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18229
    = surrogateDiagTailX0RatChunk001Sub000Block042Part006

theorem surrogateDiagonalTailChunk001Sub000Block042Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block042Part006CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block042Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block042Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block042Part006CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block042Part006SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block042Part006] using hcert

def TailChunk001Sub000Block042Part007SupportExplicit : Finset ℕ :=
  ([18230] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block042Part007 : ℚ :=
  (1245491917275 : ℚ) / 2351467929648633856

def SurrogateDiagonalTailChunk001Sub000Block042Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18230
    = surrogateDiagTailX0RatChunk001Sub000Block042Part007

theorem surrogateDiagonalTailChunk001Sub000Block042Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block042Part007CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block042Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block042Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block042Part007CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block042Part007SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block042Part007] using hcert

def TailChunk001Sub000Block042Part008SupportExplicit : Finset ℕ :=
  ([18231] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block042Part008 : ℚ :=
  (28219177375 : ℚ) / 605026621074229248

def SurrogateDiagonalTailChunk001Sub000Block042Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18231
    = surrogateDiagTailX0RatChunk001Sub000Block042Part008

theorem surrogateDiagonalTailChunk001Sub000Block042Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block042Part008CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block042Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block042Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block042Part008CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block042Part008SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block042Part008] using hcert

def TailChunk001Sub000Block042Part009SupportExplicit : Finset ℕ :=
  ([18233] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block042Part009 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block042Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18233
    = surrogateDiagTailX0RatChunk001Sub000Block042Part009

theorem surrogateDiagonalTailChunk001Sub000Block042Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block042Part009CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block042Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block042Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block042Part009CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block042Part009SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block042Part009] using hcert

def TailChunk001Sub000Block042Part010SupportExplicit : Finset ℕ :=
  ([18235] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block042Part010 : ℚ :=
  (51003553753 : ℚ) / 2426303873758003200

def SurrogateDiagonalTailChunk001Sub000Block042Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18235
    = surrogateDiagTailX0RatChunk001Sub000Block042Part010

theorem surrogateDiagonalTailChunk001Sub000Block042Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block042Part010CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block042Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block042Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block042Part010CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block042Part010SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block042Part010] using hcert

def TailChunk001Sub000Block042Part011SupportExplicit : Finset ℕ :=
  ([18237] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block042Part011 : ℚ :=
  (1154752642775 : ℚ) / 27299810275542172224

def SurrogateDiagonalTailChunk001Sub000Block042Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18237
    = surrogateDiagTailX0RatChunk001Sub000Block042Part011

theorem surrogateDiagonalTailChunk001Sub000Block042Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block042Part011CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block042Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block042Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block042Part011CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block042Part011SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block042Part011] using hcert

def TailChunk001Sub000Block042Part012SupportExplicit : Finset ℕ :=
  ([18238] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block042Part012 : ℚ :=
  (18011809669 : ℚ) / 47011942614021120

def SurrogateDiagonalTailChunk001Sub000Block042Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18238
    = surrogateDiagTailX0RatChunk001Sub000Block042Part012

theorem surrogateDiagonalTailChunk001Sub000Block042Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block042Part012CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block042Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block042Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block042Part012CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block042Part012SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block042Part012] using hcert

def TailChunk001Sub000Block042Part013SupportExplicit : Finset ℕ :=
  ([18239] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block042Part013 : ℚ :=
  (24667842733 : ℚ) / 6296621083538227200

def SurrogateDiagonalTailChunk001Sub000Block042Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18239
    = surrogateDiagTailX0RatChunk001Sub000Block042Part013

theorem surrogateDiagonalTailChunk001Sub000Block042Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block042Part013CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block042Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block042Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block042Part013CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block042Part013SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block042Part013] using hcert

def TailChunk001Sub000Block042Part014SupportExplicit : Finset ℕ :=
  ([18241] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block042Part014 : ℚ :=
  (630884280475 : ℚ) / 169179960001563721728

def SurrogateDiagonalTailChunk001Sub000Block042Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18241
    = surrogateDiagTailX0RatChunk001Sub000Block042Part014

theorem surrogateDiagonalTailChunk001Sub000Block042Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block042Part014CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block042Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block042Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block042Part014CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block042Part014SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block042Part014] using hcert

def TailChunk001Sub000Block042Part015SupportExplicit : Finset ℕ :=
  ([18242] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block042Part015 : ℚ :=
  (229698179975 : ℚ) / 517372442088538176

def SurrogateDiagonalTailChunk001Sub000Block042Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18242
    = surrogateDiagTailX0RatChunk001Sub000Block042Part015

theorem surrogateDiagonalTailChunk001Sub000Block042Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block042Part015CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block042Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block042Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block042Part015CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block042Part015SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block042Part015] using hcert

def TailChunk001Sub000Block042Part016SupportExplicit : Finset ℕ :=
  ([18245] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block042Part016 : ℚ :=
  (9307139689 : ℚ) / 982737385999564800

def SurrogateDiagonalTailChunk001Sub000Block042Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18245
    = surrogateDiagTailX0RatChunk001Sub000Block042Part016

theorem surrogateDiagonalTailChunk001Sub000Block042Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block042Part016CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block042Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block042Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block042Part016CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block042Part016SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block042Part016] using hcert

def TailChunk001Sub000Block042Part017SupportExplicit : Finset ℕ :=
  ([18246] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block042Part017 : ℚ :=
  (57781738829 : ℚ) / 68339401595289600

def SurrogateDiagonalTailChunk001Sub000Block042Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18246
    = surrogateDiagTailX0RatChunk001Sub000Block042Part017

theorem surrogateDiagonalTailChunk001Sub000Block042Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block042Part017CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block042Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block042Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block042Part017CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block042Part017SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block042Part017] using hcert

def TailChunk001Sub000Block042Part018SupportExplicit : Finset ℕ :=
  ([18247] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block042Part018 : ℚ :=
  (992941399 : ℚ) / 2578569730247884800

def SurrogateDiagonalTailChunk001Sub000Block042Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18247
    = surrogateDiagTailX0RatChunk001Sub000Block042Part018

theorem surrogateDiagonalTailChunk001Sub000Block042Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block042Part018CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block042Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block042Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block042Part018CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block042Part018SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block042Part018] using hcert

def TailChunk001Sub000Block042Part019SupportExplicit : Finset ℕ :=
  ([18249] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block042Part019 : ℚ :=
  (20941357729 : ℚ) / 191924427514060800

def SurrogateDiagonalTailChunk001Sub000Block042Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18249
    = surrogateDiagTailX0RatChunk001Sub000Block042Part019

theorem surrogateDiagonalTailChunk001Sub000Block042Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block042Part019CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block042Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block042Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block042Part019CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block042Part019SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block042Part019] using hcert

def TailChunk001Sub000Block042Part020SupportExplicit : Finset ℕ :=
  ([18251] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block042Part020 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block042Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18251
    = surrogateDiagTailX0RatChunk001Sub000Block042Part020

theorem surrogateDiagonalTailChunk001Sub000Block042Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block042Part020CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block042Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block042Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block042Part020CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block042Part020SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block042Part020] using hcert

def TailChunk001Sub000Block042Part021SupportExplicit : Finset ℕ :=
  ([18253] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block042Part021 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block042Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18253
    = surrogateDiagTailX0RatChunk001Sub000Block042Part021

theorem surrogateDiagonalTailChunk001Sub000Block042Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block042Part021CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block042Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block042Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block042Part021CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block042Part021SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block042Part021] using hcert

def TailChunk001Sub000Block042Part022SupportExplicit : Finset ℕ :=
  ([18254] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block042Part022 : ℚ :=
  (1301595765625 : ℚ) / 4335994526489807922

def SurrogateDiagonalTailChunk001Sub000Block042Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18254
    = surrogateDiagTailX0RatChunk001Sub000Block042Part022

theorem surrogateDiagonalTailChunk001Sub000Block042Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block042Part022CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block042Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block042Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block042Part022CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block042Part022SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block042Part022] using hcert

def TailChunk001Sub000Block042Part023SupportExplicit : Finset ℕ :=
  ([18255] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block042Part023 : ℚ :=
  (4064786775 : ℚ) / 98216908398002176

def SurrogateDiagonalTailChunk001Sub000Block042Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18255
    = surrogateDiagTailX0RatChunk001Sub000Block042Part023

theorem surrogateDiagonalTailChunk001Sub000Block042Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block042Part023CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block042Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block042Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block042Part023CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block042Part023SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block042Part023] using hcert

def TailChunk001Sub000Block042Part024SupportExplicit : Finset ℕ :=
  ([18257] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block042Part024 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block042Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18257
    = surrogateDiagTailX0RatChunk001Sub000Block042Part024

theorem surrogateDiagonalTailChunk001Sub000Block042Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block042Part024CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block042Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block042Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block042Part024CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block042Part024SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block042Part024] using hcert

def surrogateDiagonalTailChunk001Sub000Block042HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block042Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block042Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block042Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block042Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block042Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block042Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block042Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block042Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block042Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block042Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block042Head : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block042Part000
    + surrogateDiagTailX0RatChunk001Sub000Block042Part001
    + surrogateDiagTailX0RatChunk001Sub000Block042Part002
    + surrogateDiagTailX0RatChunk001Sub000Block042Part003
    + surrogateDiagTailX0RatChunk001Sub000Block042Part004
    + surrogateDiagTailX0RatChunk001Sub000Block042Part005
    + surrogateDiagTailX0RatChunk001Sub000Block042Part006
    + surrogateDiagTailX0RatChunk001Sub000Block042Part007
    + surrogateDiagTailX0RatChunk001Sub000Block042Part008
    + surrogateDiagTailX0RatChunk001Sub000Block042Part009

def surrogateDiagonalTailChunk001Sub000Block042MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block042Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block042Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block042Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block042Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block042Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block042Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block042Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block042Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block042Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block042Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block042Mid : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block042Part010
    + surrogateDiagTailX0RatChunk001Sub000Block042Part011
    + surrogateDiagTailX0RatChunk001Sub000Block042Part012
    + surrogateDiagTailX0RatChunk001Sub000Block042Part013
    + surrogateDiagTailX0RatChunk001Sub000Block042Part014
    + surrogateDiagTailX0RatChunk001Sub000Block042Part015
    + surrogateDiagTailX0RatChunk001Sub000Block042Part016
    + surrogateDiagTailX0RatChunk001Sub000Block042Part017
    + surrogateDiagTailX0RatChunk001Sub000Block042Part018
    + surrogateDiagTailX0RatChunk001Sub000Block042Part019

def surrogateDiagonalTailChunk001Sub000Block042TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block042Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block042Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block042Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block042Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block042Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block042Tail : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block042Part020
    + surrogateDiagTailX0RatChunk001Sub000Block042Part021
    + surrogateDiagTailX0RatChunk001Sub000Block042Part022
    + surrogateDiagTailX0RatChunk001Sub000Block042Part023
    + surrogateDiagTailX0RatChunk001Sub000Block042Part024

def surrogateDiagonalTailChunk001Sub000Block042Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk001Sub000Block042HeadSum X0
    + surrogateDiagonalTailChunk001Sub000Block042MidSum X0
    + surrogateDiagonalTailChunk001Sub000Block042TailSum X0

def surrogateDiagTailX0RatChunk001Sub000Block042 : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block042Part000
    + surrogateDiagTailX0RatChunk001Sub000Block042Part001
    + surrogateDiagTailX0RatChunk001Sub000Block042Part002
    + surrogateDiagTailX0RatChunk001Sub000Block042Part003
    + surrogateDiagTailX0RatChunk001Sub000Block042Part004
    + surrogateDiagTailX0RatChunk001Sub000Block042Part005
    + surrogateDiagTailX0RatChunk001Sub000Block042Part006
    + surrogateDiagTailX0RatChunk001Sub000Block042Part007
    + surrogateDiagTailX0RatChunk001Sub000Block042Part008
    + surrogateDiagTailX0RatChunk001Sub000Block042Part009
    + surrogateDiagTailX0RatChunk001Sub000Block042Part010
    + surrogateDiagTailX0RatChunk001Sub000Block042Part011
    + surrogateDiagTailX0RatChunk001Sub000Block042Part012
    + surrogateDiagTailX0RatChunk001Sub000Block042Part013
    + surrogateDiagTailX0RatChunk001Sub000Block042Part014
    + surrogateDiagTailX0RatChunk001Sub000Block042Part015
    + surrogateDiagTailX0RatChunk001Sub000Block042Part016
    + surrogateDiagTailX0RatChunk001Sub000Block042Part017
    + surrogateDiagTailX0RatChunk001Sub000Block042Part018
    + surrogateDiagTailX0RatChunk001Sub000Block042Part019
    + surrogateDiagTailX0RatChunk001Sub000Block042Part020
    + surrogateDiagTailX0RatChunk001Sub000Block042Part021
    + surrogateDiagTailX0RatChunk001Sub000Block042Part022
    + surrogateDiagTailX0RatChunk001Sub000Block042Part023
    + surrogateDiagTailX0RatChunk001Sub000Block042Part024

theorem surrogateDiagTailX0RatChunk001Sub000Block042_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk001Sub000Block042Head + surrogateDiagTailX0RatChunk001Sub000Block042Mid + surrogateDiagTailX0RatChunk001Sub000Block042Tail =
      surrogateDiagTailX0RatChunk001Sub000Block042 := by
  unfold surrogateDiagTailX0RatChunk001Sub000Block042Head surrogateDiagTailX0RatChunk001Sub000Block042Mid surrogateDiagTailX0RatChunk001Sub000Block042Tail surrogateDiagTailX0RatChunk001Sub000Block042
  ring

def SurrogateDiagonalTailChunk001Sub000Block042HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block042HeadSum X0 = surrogateDiagTailX0RatChunk001Sub000Block042Head

def SurrogateDiagonalTailChunk001Sub000Block042MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block042MidSum X0 = surrogateDiagTailX0RatChunk001Sub000Block042Mid

def SurrogateDiagonalTailChunk001Sub000Block042TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block042TailSum X0 = surrogateDiagTailX0RatChunk001Sub000Block042Tail

theorem surrogateDiagonalTailChunk001Sub000Block042_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk001Sub000Block042HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk001Sub000Block042MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk001Sub000Block042TailCertificateAt X0) :
    surrogateDiagonalTailChunk001Sub000Block042Sum X0 = surrogateDiagTailX0RatChunk001Sub000Block042 := by
  unfold SurrogateDiagonalTailChunk001Sub000Block042HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk001Sub000Block042MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk001Sub000Block042TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk001Sub000Block042Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk001Sub000Block042_eq_head_add_mid_add_tail

/-- Block 043 covers tail-support indices [11075,11100) and q from 18258 to 18301. -/

def TailChunk001Sub000Block043Part000SupportExplicit : Finset ℕ :=
  ([18258] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block043Part000 : ℚ :=
  (2138635049275 : ℚ) / 2632126644017430528

def SurrogateDiagonalTailChunk001Sub000Block043Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18258
    = surrogateDiagTailX0RatChunk001Sub000Block043Part000

theorem surrogateDiagonalTailChunk001Sub000Block043Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block043Part000CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block043Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block043Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block043Part000CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block043Part000SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block043Part000] using hcert

def TailChunk001Sub000Block043Part001SupportExplicit : Finset ℕ :=
  ([18262] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block043Part001 : ℚ :=
  (2434451935325 : ℚ) / 7202252287818998784

def SurrogateDiagonalTailChunk001Sub000Block043Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18262
    = surrogateDiagTailX0RatChunk001Sub000Block043Part001

theorem surrogateDiagonalTailChunk001Sub000Block043Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block043Part001CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block043Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block043Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block043Part001CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block043Part001SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block043Part001] using hcert

def TailChunk001Sub000Block043Part002SupportExplicit : Finset ℕ :=
  ([18263] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block043Part002 : ℚ :=
  (425956388075 : ℚ) / 74960454826758242304

def SurrogateDiagonalTailChunk001Sub000Block043Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18263
    = surrogateDiagTailX0RatChunk001Sub000Block043Part002

theorem surrogateDiagonalTailChunk001Sub000Block043Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block043Part002CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block043Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block043Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block043Part002CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block043Part002SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block043Part002] using hcert

def TailChunk001Sub000Block043Part003SupportExplicit : Finset ℕ :=
  ([18265] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block043Part003 : ℚ :=
  (321103337 : ℚ) / 14569206762700800

def SurrogateDiagonalTailChunk001Sub000Block043Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18265
    = surrogateDiagTailX0RatChunk001Sub000Block043Part003

theorem surrogateDiagonalTailChunk001Sub000Block043Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block043Part003CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block043Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block043Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block043Part003CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block043Part003SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block043Part003] using hcert

def TailChunk001Sub000Block043Part004SupportExplicit : Finset ℕ :=
  ([18266] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block043Part004 : ℚ :=
  (1303307640625 : ℚ) / 4347408786923165472

def SurrogateDiagonalTailChunk001Sub000Block043Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18266
    = surrogateDiagTailX0RatChunk001Sub000Block043Part004

theorem surrogateDiagonalTailChunk001Sub000Block043Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block043Part004CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block043Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block043Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block043Part004CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block043Part004SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block043Part004] using hcert

def TailChunk001Sub000Block043Part005SupportExplicit : Finset ℕ :=
  ([18267] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block043Part005 : ℚ :=
  (125025 : ℚ) / 10989768954380288

def SurrogateDiagonalTailChunk001Sub000Block043Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18267
    = surrogateDiagTailX0RatChunk001Sub000Block043Part005

theorem surrogateDiagonalTailChunk001Sub000Block043Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block043Part005CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block043Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block043Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block043Part005CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block043Part005SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block043Part005] using hcert

def TailChunk001Sub000Block043Part006SupportExplicit : Finset ℕ :=
  ([18269] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block043Part006 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block043Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18269
    = surrogateDiagTailX0RatChunk001Sub000Block043Part006

theorem surrogateDiagonalTailChunk001Sub000Block043Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block043Part006CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block043Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block043Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block043Part006CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block043Part006SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block043Part006] using hcert

def TailChunk001Sub000Block043Part007SupportExplicit : Finset ℕ :=
  ([18273] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block043Part007 : ℚ :=
  (1667 : ℚ) / 146722897238400

def SurrogateDiagonalTailChunk001Sub000Block043Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18273
    = surrogateDiagTailX0RatChunk001Sub000Block043Part007

theorem surrogateDiagonalTailChunk001Sub000Block043Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block043Part007CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block043Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block043Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block043Part007CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block043Part007SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block043Part007] using hcert

def TailChunk001Sub000Block043Part008SupportExplicit : Finset ℕ :=
  ([18274] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block043Part008 : ℚ :=
  (1304449515625 : ℚ) / 4355030803568074752

def SurrogateDiagonalTailChunk001Sub000Block043Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18274
    = surrogateDiagTailX0RatChunk001Sub000Block043Part008

theorem surrogateDiagonalTailChunk001Sub000Block043Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block043Part008CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block043Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block043Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block043Part008CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block043Part008SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block043Part008] using hcert

def TailChunk001Sub000Block043Part009SupportExplicit : Finset ℕ :=
  ([18278] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block043Part009 : ℚ :=
  (457273556825 : ℚ) / 1015802686597496832

def SurrogateDiagonalTailChunk001Sub000Block043Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18278
    = surrogateDiagTailX0RatChunk001Sub000Block043Part009

theorem surrogateDiagonalTailChunk001Sub000Block043Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block043Part009CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block043Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block043Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block043Part009CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block043Part009SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block043Part009] using hcert

def TailChunk001Sub000Block043Part010SupportExplicit : Finset ℕ :=
  ([18281] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block043Part010 : ℚ :=
  (3517921717 : ℚ) / 10499699520000000000

def SurrogateDiagonalTailChunk001Sub000Block043Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18281
    = surrogateDiagTailX0RatChunk001Sub000Block043Part010

theorem surrogateDiagonalTailChunk001Sub000Block043Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block043Part010CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block043Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block043Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block043Part010CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block043Part010SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block043Part010] using hcert

def TailChunk001Sub000Block043Part011SupportExplicit : Finset ℕ :=
  ([18282] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block043Part011 : ℚ :=
  (82517479951 : ℚ) / 92863096521523200

def SurrogateDiagonalTailChunk001Sub000Block043Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18282
    = surrogateDiagTailX0RatChunk001Sub000Block043Part011

theorem surrogateDiagonalTailChunk001Sub000Block043Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block043Part011CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block043Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block043Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block043Part011CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block043Part011SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block043Part011] using hcert

def TailChunk001Sub000Block043Part012SupportExplicit : Finset ℕ :=
  ([18283] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block043Part012 : ℚ :=
  (136350685075 : ℚ) / 253737752051976849408

def SurrogateDiagonalTailChunk001Sub000Block043Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18283
    = surrogateDiagTailX0RatChunk001Sub000Block043Part012

theorem surrogateDiagonalTailChunk001Sub000Block043Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block043Part012CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block043Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block043Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block043Part012CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block043Part012SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block043Part012] using hcert

def TailChunk001Sub000Block043Part013SupportExplicit : Finset ℕ :=
  ([18285] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block043Part013 : ℚ :=
  (334739784375 : ℚ) / 5847492183652827136

def SurrogateDiagonalTailChunk001Sub000Block043Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18285
    = surrogateDiagTailX0RatChunk001Sub000Block043Part013

theorem surrogateDiagonalTailChunk001Sub000Block043Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block043Part013CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block043Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block043Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block043Part013CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block043Part013SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block043Part013] using hcert

def TailChunk001Sub000Block043Part014SupportExplicit : Finset ℕ :=
  ([18286] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block043Part014 : ℚ :=
  (66750209021 : ℚ) / 207308666754662400

def SurrogateDiagonalTailChunk001Sub000Block043Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18286
    = surrogateDiagTailX0RatChunk001Sub000Block043Part014

theorem surrogateDiagonalTailChunk001Sub000Block043Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block043Part014CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block043Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block043Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block043Part014CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block043Part014SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block043Part014] using hcert

def TailChunk001Sub000Block043Part015SupportExplicit : Finset ℕ :=
  ([18287] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block043Part015 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block043Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18287
    = surrogateDiagTailX0RatChunk001Sub000Block043Part015

theorem surrogateDiagonalTailChunk001Sub000Block043Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block043Part015CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block043Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block043Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block043Part015CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block043Part015SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block043Part015] using hcert

def TailChunk001Sub000Block043Part016SupportExplicit : Finset ℕ :=
  ([18289] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block043Part016 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block043Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18289
    = surrogateDiagTailX0RatChunk001Sub000Block043Part016

theorem surrogateDiagonalTailChunk001Sub000Block043Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block043Part016CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block043Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block043Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block043Part016CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block043Part016SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block043Part016] using hcert

def TailChunk001Sub000Block043Part017SupportExplicit : Finset ℕ :=
  ([18290] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block043Part017 : ℚ :=
  (140454942901 : ℚ) / 234705792828211200

def SurrogateDiagonalTailChunk001Sub000Block043Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18290
    = surrogateDiagTailX0RatChunk001Sub000Block043Part017

theorem surrogateDiagonalTailChunk001Sub000Block043Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block043Part017CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block043Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block043Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block043Part017CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block043Part017SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block043Part017] using hcert

def TailChunk001Sub000Block043Part018SupportExplicit : Finset ℕ :=
  ([18291] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block043Part018 : ℚ :=
  (25734805675 : ℚ) / 755594530024587264

def SurrogateDiagonalTailChunk001Sub000Block043Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18291
    = surrogateDiagTailX0RatChunk001Sub000Block043Part018

theorem surrogateDiagonalTailChunk001Sub000Block043Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block043Part018CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block043Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block043Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block043Part018CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block043Part018SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block043Part018] using hcert

def TailChunk001Sub000Block043Part019SupportExplicit : Finset ℕ :=
  ([18293] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block043Part019 : ℚ :=
  (20833640863 : ℚ) / 7631517913919107200

def SurrogateDiagonalTailChunk001Sub000Block043Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18293
    = surrogateDiagTailX0RatChunk001Sub000Block043Part019

theorem surrogateDiagonalTailChunk001Sub000Block043Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block043Part019CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block043Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block043Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block043Part019CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block043Part019SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block043Part019] using hcert

def TailChunk001Sub000Block043Part020SupportExplicit : Finset ℕ :=
  ([18294] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block043Part020 : ℚ :=
  (1452154688225 : ℚ) / 1726540207241969664

def SurrogateDiagonalTailChunk001Sub000Block043Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18294
    = surrogateDiagTailX0RatChunk001Sub000Block043Part020

theorem surrogateDiagonalTailChunk001Sub000Block043Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block043Part020CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block043Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block043Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block043Part020CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block043Part020SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block043Part020] using hcert

def TailChunk001Sub000Block043Part021SupportExplicit : Finset ℕ :=
  ([18295] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block043Part021 : ℚ :=
  (1673536003225 : ℚ) / 114615044869638309888

def SurrogateDiagonalTailChunk001Sub000Block043Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18295
    = surrogateDiagTailX0RatChunk001Sub000Block043Part021

theorem surrogateDiagonalTailChunk001Sub000Block043Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block043Part021CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block043Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block043Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block043Part021CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block043Part021SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block043Part021] using hcert

def TailChunk001Sub000Block043Part022SupportExplicit : Finset ℕ :=
  ([18298] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block043Part022 : ℚ :=
  (231111063875 : ℚ) / 523759680599201856

def SurrogateDiagonalTailChunk001Sub000Block043Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18298
    = surrogateDiagTailX0RatChunk001Sub000Block043Part022

theorem surrogateDiagonalTailChunk001Sub000Block043Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block043Part022CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block043Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block043Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block043Part022CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block043Part022SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block043Part022] using hcert

def TailChunk001Sub000Block043Part023SupportExplicit : Finset ℕ :=
  ([18299] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block043Part023 : ℚ :=
  (4138077161 : ℚ) / 4842294263407641600

def SurrogateDiagonalTailChunk001Sub000Block043Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18299
    = surrogateDiagTailX0RatChunk001Sub000Block043Part023

theorem surrogateDiagonalTailChunk001Sub000Block043Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block043Part023CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block043Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block043Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block043Part023CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block043Part023SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block043Part023] using hcert

def TailChunk001Sub000Block043Part024SupportExplicit : Finset ℕ :=
  ([18301] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block043Part024 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block043Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18301
    = surrogateDiagTailX0RatChunk001Sub000Block043Part024

theorem surrogateDiagonalTailChunk001Sub000Block043Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block043Part024CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block043Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block043Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block043Part024CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block043Part024SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block043Part024] using hcert

def surrogateDiagonalTailChunk001Sub000Block043HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block043Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block043Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block043Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block043Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block043Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block043Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block043Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block043Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block043Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block043Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block043Head : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block043Part000
    + surrogateDiagTailX0RatChunk001Sub000Block043Part001
    + surrogateDiagTailX0RatChunk001Sub000Block043Part002
    + surrogateDiagTailX0RatChunk001Sub000Block043Part003
    + surrogateDiagTailX0RatChunk001Sub000Block043Part004
    + surrogateDiagTailX0RatChunk001Sub000Block043Part005
    + surrogateDiagTailX0RatChunk001Sub000Block043Part006
    + surrogateDiagTailX0RatChunk001Sub000Block043Part007
    + surrogateDiagTailX0RatChunk001Sub000Block043Part008
    + surrogateDiagTailX0RatChunk001Sub000Block043Part009

def surrogateDiagonalTailChunk001Sub000Block043MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block043Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block043Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block043Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block043Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block043Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block043Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block043Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block043Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block043Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block043Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block043Mid : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block043Part010
    + surrogateDiagTailX0RatChunk001Sub000Block043Part011
    + surrogateDiagTailX0RatChunk001Sub000Block043Part012
    + surrogateDiagTailX0RatChunk001Sub000Block043Part013
    + surrogateDiagTailX0RatChunk001Sub000Block043Part014
    + surrogateDiagTailX0RatChunk001Sub000Block043Part015
    + surrogateDiagTailX0RatChunk001Sub000Block043Part016
    + surrogateDiagTailX0RatChunk001Sub000Block043Part017
    + surrogateDiagTailX0RatChunk001Sub000Block043Part018
    + surrogateDiagTailX0RatChunk001Sub000Block043Part019

def surrogateDiagonalTailChunk001Sub000Block043TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block043Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block043Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block043Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block043Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block043Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block043Tail : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block043Part020
    + surrogateDiagTailX0RatChunk001Sub000Block043Part021
    + surrogateDiagTailX0RatChunk001Sub000Block043Part022
    + surrogateDiagTailX0RatChunk001Sub000Block043Part023
    + surrogateDiagTailX0RatChunk001Sub000Block043Part024

def surrogateDiagonalTailChunk001Sub000Block043Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk001Sub000Block043HeadSum X0
    + surrogateDiagonalTailChunk001Sub000Block043MidSum X0
    + surrogateDiagonalTailChunk001Sub000Block043TailSum X0

def surrogateDiagTailX0RatChunk001Sub000Block043 : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block043Part000
    + surrogateDiagTailX0RatChunk001Sub000Block043Part001
    + surrogateDiagTailX0RatChunk001Sub000Block043Part002
    + surrogateDiagTailX0RatChunk001Sub000Block043Part003
    + surrogateDiagTailX0RatChunk001Sub000Block043Part004
    + surrogateDiagTailX0RatChunk001Sub000Block043Part005
    + surrogateDiagTailX0RatChunk001Sub000Block043Part006
    + surrogateDiagTailX0RatChunk001Sub000Block043Part007
    + surrogateDiagTailX0RatChunk001Sub000Block043Part008
    + surrogateDiagTailX0RatChunk001Sub000Block043Part009
    + surrogateDiagTailX0RatChunk001Sub000Block043Part010
    + surrogateDiagTailX0RatChunk001Sub000Block043Part011
    + surrogateDiagTailX0RatChunk001Sub000Block043Part012
    + surrogateDiagTailX0RatChunk001Sub000Block043Part013
    + surrogateDiagTailX0RatChunk001Sub000Block043Part014
    + surrogateDiagTailX0RatChunk001Sub000Block043Part015
    + surrogateDiagTailX0RatChunk001Sub000Block043Part016
    + surrogateDiagTailX0RatChunk001Sub000Block043Part017
    + surrogateDiagTailX0RatChunk001Sub000Block043Part018
    + surrogateDiagTailX0RatChunk001Sub000Block043Part019
    + surrogateDiagTailX0RatChunk001Sub000Block043Part020
    + surrogateDiagTailX0RatChunk001Sub000Block043Part021
    + surrogateDiagTailX0RatChunk001Sub000Block043Part022
    + surrogateDiagTailX0RatChunk001Sub000Block043Part023
    + surrogateDiagTailX0RatChunk001Sub000Block043Part024

theorem surrogateDiagTailX0RatChunk001Sub000Block043_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk001Sub000Block043Head + surrogateDiagTailX0RatChunk001Sub000Block043Mid + surrogateDiagTailX0RatChunk001Sub000Block043Tail =
      surrogateDiagTailX0RatChunk001Sub000Block043 := by
  unfold surrogateDiagTailX0RatChunk001Sub000Block043Head surrogateDiagTailX0RatChunk001Sub000Block043Mid surrogateDiagTailX0RatChunk001Sub000Block043Tail surrogateDiagTailX0RatChunk001Sub000Block043
  ring

def SurrogateDiagonalTailChunk001Sub000Block043HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block043HeadSum X0 = surrogateDiagTailX0RatChunk001Sub000Block043Head

def SurrogateDiagonalTailChunk001Sub000Block043MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block043MidSum X0 = surrogateDiagTailX0RatChunk001Sub000Block043Mid

def SurrogateDiagonalTailChunk001Sub000Block043TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block043TailSum X0 = surrogateDiagTailX0RatChunk001Sub000Block043Tail

theorem surrogateDiagonalTailChunk001Sub000Block043_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk001Sub000Block043HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk001Sub000Block043MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk001Sub000Block043TailCertificateAt X0) :
    surrogateDiagonalTailChunk001Sub000Block043Sum X0 = surrogateDiagTailX0RatChunk001Sub000Block043 := by
  unfold SurrogateDiagonalTailChunk001Sub000Block043HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk001Sub000Block043MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk001Sub000Block043TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk001Sub000Block043Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk001Sub000Block043_eq_head_add_mid_add_tail

/-- Block 044 covers tail-support indices [11100,11125) and q from 18302 to 18341. -/

def TailChunk001Sub000Block044Part000SupportExplicit : Finset ℕ :=
  ([18302] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block044Part000 : ℚ :=
  (83740801 : ℚ) / 280434355906050

def SurrogateDiagonalTailChunk001Sub000Block044Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18302
    = surrogateDiagTailX0RatChunk001Sub000Block044Part000

theorem surrogateDiagonalTailChunk001Sub000Block044Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block044Part000CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block044Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block044Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block044Part000CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block044Part000SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block044Part000] using hcert

def TailChunk001Sub000Block044Part001SupportExplicit : Finset ℕ :=
  ([18303] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block044Part001 : ℚ :=
  (465250007 : ℚ) / 11078888134560000

def SurrogateDiagonalTailChunk001Sub000Block044Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18303
    = surrogateDiagTailX0RatChunk001Sub000Block044Part001

theorem surrogateDiagonalTailChunk001Sub000Block044Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block044Part001CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block044Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block044Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block044Part001CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block044Part001SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block044Part001] using hcert

def TailChunk001Sub000Block044Part002SupportExplicit : Finset ℕ :=
  ([18305] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block044Part002 : ℚ :=
  (1267773348175 : ℚ) / 61596188269835747328

def SurrogateDiagonalTailChunk001Sub000Block044Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18305
    = surrogateDiagTailX0RatChunk001Sub000Block044Part002

theorem surrogateDiagonalTailChunk001Sub000Block044Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block044Part002CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block044Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block044Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block044Part002CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block044Part002SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block044Part002] using hcert

def TailChunk001Sub000Block044Part003SupportExplicit : Finset ℕ :=
  ([18307] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block044Part003 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block044Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18307
    = surrogateDiagTailX0RatChunk001Sub000Block044Part003

theorem surrogateDiagonalTailChunk001Sub000Block044Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block044Part003CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block044Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block044Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block044Part003CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block044Part003SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block044Part003] using hcert

def TailChunk001Sub000Block044Part004SupportExplicit : Finset ℕ :=
  ([18309] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block044Part004 : ℚ :=
  (188412396375 : ℚ) / 3589034496967573504

def SurrogateDiagonalTailChunk001Sub000Block044Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18309
    = surrogateDiagTailX0RatChunk001Sub000Block044Part004

theorem surrogateDiagonalTailChunk001Sub000Block044Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block044Part004CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block044Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block044Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block044Part004CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block044Part004SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block044Part004] using hcert

def TailChunk001Sub000Block044Part005SupportExplicit : Finset ℕ :=
  ([18310] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block044Part005 : ℚ :=
  (142391658589 : ℚ) / 287164780447795200

def SurrogateDiagonalTailChunk001Sub000Block044Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18310
    = surrogateDiagTailX0RatChunk001Sub000Block044Part005

theorem surrogateDiagonalTailChunk001Sub000Block044Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block044Part005CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block044Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block044Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block044Part005CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block044Part005SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block044Part005] using hcert

def TailChunk001Sub000Block044Part006SupportExplicit : Finset ℕ :=
  ([18311] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block044Part006 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block044Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18311
    = surrogateDiagTailX0RatChunk001Sub000Block044Part006

theorem surrogateDiagonalTailChunk001Sub000Block044Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block044Part006CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block044Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block044Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block044Part006CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block044Part006SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block044Part006] using hcert

def TailChunk001Sub000Block044Part007SupportExplicit : Finset ℕ :=
  ([18313] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block044Part007 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block044Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18313
    = surrogateDiagTailX0RatChunk001Sub000Block044Part007

theorem surrogateDiagonalTailChunk001Sub000Block044Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block044Part007CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block044Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block044Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block044Part007CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block044Part007SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block044Part007] using hcert

def TailChunk001Sub000Block044Part008SupportExplicit : Finset ℕ :=
  ([18314] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block044Part008 : ℚ :=
  (1310166390625 : ℚ) / 4393291332080462112

def SurrogateDiagonalTailChunk001Sub000Block044Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18314
    = surrogateDiagTailX0RatChunk001Sub000Block044Part008

theorem surrogateDiagonalTailChunk001Sub000Block044Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block044Part008CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block044Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block044Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block044Part008CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block044Part008SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block044Part008] using hcert

def TailChunk001Sub000Block044Part009SupportExplicit : Finset ℕ :=
  ([18317] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block044Part009 : ℚ :=
  (83178583975 : ℚ) / 33963404060144959488

def SurrogateDiagonalTailChunk001Sub000Block044Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18317
    = surrogateDiagTailX0RatChunk001Sub000Block044Part009

theorem surrogateDiagonalTailChunk001Sub000Block044Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block044Part009CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block044Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block044Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block044Part009CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block044Part009SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block044Part009] using hcert

def TailChunk001Sub000Block044Part010SupportExplicit : Finset ℕ :=
  ([18318] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block044Part010 : ℚ :=
  (110737739407 : ℚ) / 119562821318707200

def SurrogateDiagonalTailChunk001Sub000Block044Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18318
    = surrogateDiagTailX0RatChunk001Sub000Block044Part010

theorem surrogateDiagonalTailChunk001Sub000Block044Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block044Part010CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block044Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block044Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block044Part010CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block044Part010SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block044Part010] using hcert

def TailChunk001Sub000Block044Part011SupportExplicit : Finset ℕ :=
  ([18319] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block044Part011 : ℚ :=
  (429590880625 : ℚ) / 151768911390288150528

def SurrogateDiagonalTailChunk001Sub000Block044Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18319
    = surrogateDiagTailX0RatChunk001Sub000Block044Part011

theorem surrogateDiagonalTailChunk001Sub000Block044Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block044Part011CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block044Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block044Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block044Part011CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block044Part011SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block044Part011] using hcert

def TailChunk001Sub000Block044Part012SupportExplicit : Finset ℕ :=
  ([18321] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block044Part012 : ℚ :=
  (13113601237 : ℚ) / 273286448728473600

def SurrogateDiagonalTailChunk001Sub000Block044Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18321
    = surrogateDiagTailX0RatChunk001Sub000Block044Part012

theorem surrogateDiagonalTailChunk001Sub000Block044Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block044Part012CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block044Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block044Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block044Part012CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block044Part012SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block044Part012] using hcert

def TailChunk001Sub000Block044Part013SupportExplicit : Finset ℕ :=
  ([18322] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block044Part013 : ℚ :=
  (2098098025 : ℚ) / 7041557741302272

def SurrogateDiagonalTailChunk001Sub000Block044Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18322
    = surrogateDiagTailX0RatChunk001Sub000Block044Part013

theorem surrogateDiagonalTailChunk001Sub000Block044Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block044Part013CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block044Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block044Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block044Part013CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block044Part013SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block044Part013] using hcert

def TailChunk001Sub000Block044Part014SupportExplicit : Finset ℕ :=
  ([18323] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block044Part014 : ℚ :=
  (3851891551 : ℚ) / 10499699520000000000

def SurrogateDiagonalTailChunk001Sub000Block044Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18323
    = surrogateDiagTailX0RatChunk001Sub000Block044Part014

theorem surrogateDiagonalTailChunk001Sub000Block044Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block044Part014CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block044Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block044Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block044Part014CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block044Part014SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block044Part014] using hcert

def TailChunk001Sub000Block044Part015SupportExplicit : Finset ℕ :=
  ([18327] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block044Part015 : ℚ :=
  (92219563237 : ℚ) / 1965593284784947200

def SurrogateDiagonalTailChunk001Sub000Block044Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18327
    = surrogateDiagTailX0RatChunk001Sub000Block044Part015

theorem surrogateDiagonalTailChunk001Sub000Block044Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block044Part015CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block044Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block044Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block044Part015CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block044Part015SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block044Part015] using hcert

def TailChunk001Sub000Block044Part016SupportExplicit : Finset ℕ :=
  ([18329] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block044Part016 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block044Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18329
    = surrogateDiagTailX0RatChunk001Sub000Block044Part016

theorem surrogateDiagonalTailChunk001Sub000Block044Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block044Part016CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block044Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block044Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block044Part016CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block044Part016SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block044Part016] using hcert

def TailChunk001Sub000Block044Part017SupportExplicit : Finset ℕ :=
  ([18330] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block044Part017 : ℚ :=
  (235034577575 : ℚ) / 118864763547549696

def SurrogateDiagonalTailChunk001Sub000Block044Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18330
    = surrogateDiagTailX0RatChunk001Sub000Block044Part017

theorem surrogateDiagonalTailChunk001Sub000Block044Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block044Part017CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block044Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block044Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block044Part017CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block044Part017SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block044Part017] using hcert

def TailChunk001Sub000Block044Part018SupportExplicit : Finset ℕ :=
  ([18331] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block044Part018 : ℚ :=
  (244233118975 : ℚ) / 235163466341062330368

def SurrogateDiagonalTailChunk001Sub000Block044Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18331
    = surrogateDiagTailX0RatChunk001Sub000Block044Part018

theorem surrogateDiagonalTailChunk001Sub000Block044Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block044Part018CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block044Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block044Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block044Part018CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block044Part018SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block044Part018] using hcert

def TailChunk001Sub000Block044Part019SupportExplicit : Finset ℕ :=
  ([18334] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block044Part019 : ℚ :=
  (231559596775 : ℚ) / 737794738381307904

def SurrogateDiagonalTailChunk001Sub000Block044Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18334
    = surrogateDiagTailX0RatChunk001Sub000Block044Part019

theorem surrogateDiagonalTailChunk001Sub000Block044Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block044Part019CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block044Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block044Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block044Part019CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block044Part019SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block044Part019] using hcert

def TailChunk001Sub000Block044Part020SupportExplicit : Finset ℕ :=
  ([18335] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block044Part020 : ℚ :=
  (124903786325 : ℚ) / 11414891095482433536

def SurrogateDiagonalTailChunk001Sub000Block044Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18335
    = surrogateDiagTailX0RatChunk001Sub000Block044Part020

theorem surrogateDiagonalTailChunk001Sub000Block044Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block044Part020CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block044Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block044Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block044Part020CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block044Part020SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block044Part020] using hcert

def TailChunk001Sub000Block044Part021SupportExplicit : Finset ℕ :=
  ([18337] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block044Part021 : ℚ :=
  (2990491549 : ℚ) / 1100750264479689600

def SurrogateDiagonalTailChunk001Sub000Block044Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18337
    = surrogateDiagTailX0RatChunk001Sub000Block044Part021

theorem surrogateDiagonalTailChunk001Sub000Block044Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block044Part021CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block044Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block044Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block044Part021CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block044Part021SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block044Part021] using hcert

def TailChunk001Sub000Block044Part022SupportExplicit : Finset ℕ :=
  ([18338] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block044Part022 : ℚ :=
  (5068460432725 : ℚ) / 16001254070038069248

def SurrogateDiagonalTailChunk001Sub000Block044Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18338
    = surrogateDiagTailX0RatChunk001Sub000Block044Part022

theorem surrogateDiagonalTailChunk001Sub000Block044Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block044Part022CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block044Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block044Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block044Part022CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block044Part022SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block044Part022] using hcert

def TailChunk001Sub000Block044Part023SupportExplicit : Finset ℕ :=
  ([18339] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block044Part023 : ℚ :=
  (583852258675 : ℚ) / 13957904818998607872

def SurrogateDiagonalTailChunk001Sub000Block044Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18339
    = surrogateDiagTailX0RatChunk001Sub000Block044Part023

theorem surrogateDiagonalTailChunk001Sub000Block044Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block044Part023CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block044Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block044Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block044Part023CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block044Part023SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block044Part023] using hcert

def TailChunk001Sub000Block044Part024SupportExplicit : Finset ℕ :=
  ([18341] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block044Part024 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block044Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18341
    = surrogateDiagTailX0RatChunk001Sub000Block044Part024

theorem surrogateDiagonalTailChunk001Sub000Block044Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block044Part024CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block044Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block044Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block044Part024CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block044Part024SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block044Part024] using hcert

def surrogateDiagonalTailChunk001Sub000Block044HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block044Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block044Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block044Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block044Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block044Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block044Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block044Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block044Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block044Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block044Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block044Head : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block044Part000
    + surrogateDiagTailX0RatChunk001Sub000Block044Part001
    + surrogateDiagTailX0RatChunk001Sub000Block044Part002
    + surrogateDiagTailX0RatChunk001Sub000Block044Part003
    + surrogateDiagTailX0RatChunk001Sub000Block044Part004
    + surrogateDiagTailX0RatChunk001Sub000Block044Part005
    + surrogateDiagTailX0RatChunk001Sub000Block044Part006
    + surrogateDiagTailX0RatChunk001Sub000Block044Part007
    + surrogateDiagTailX0RatChunk001Sub000Block044Part008
    + surrogateDiagTailX0RatChunk001Sub000Block044Part009

def surrogateDiagonalTailChunk001Sub000Block044MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block044Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block044Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block044Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block044Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block044Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block044Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block044Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block044Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block044Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block044Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block044Mid : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block044Part010
    + surrogateDiagTailX0RatChunk001Sub000Block044Part011
    + surrogateDiagTailX0RatChunk001Sub000Block044Part012
    + surrogateDiagTailX0RatChunk001Sub000Block044Part013
    + surrogateDiagTailX0RatChunk001Sub000Block044Part014
    + surrogateDiagTailX0RatChunk001Sub000Block044Part015
    + surrogateDiagTailX0RatChunk001Sub000Block044Part016
    + surrogateDiagTailX0RatChunk001Sub000Block044Part017
    + surrogateDiagTailX0RatChunk001Sub000Block044Part018
    + surrogateDiagTailX0RatChunk001Sub000Block044Part019

def surrogateDiagonalTailChunk001Sub000Block044TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block044Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block044Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block044Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block044Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block044Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block044Tail : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block044Part020
    + surrogateDiagTailX0RatChunk001Sub000Block044Part021
    + surrogateDiagTailX0RatChunk001Sub000Block044Part022
    + surrogateDiagTailX0RatChunk001Sub000Block044Part023
    + surrogateDiagTailX0RatChunk001Sub000Block044Part024

def surrogateDiagonalTailChunk001Sub000Block044Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk001Sub000Block044HeadSum X0
    + surrogateDiagonalTailChunk001Sub000Block044MidSum X0
    + surrogateDiagonalTailChunk001Sub000Block044TailSum X0

def surrogateDiagTailX0RatChunk001Sub000Block044 : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block044Part000
    + surrogateDiagTailX0RatChunk001Sub000Block044Part001
    + surrogateDiagTailX0RatChunk001Sub000Block044Part002
    + surrogateDiagTailX0RatChunk001Sub000Block044Part003
    + surrogateDiagTailX0RatChunk001Sub000Block044Part004
    + surrogateDiagTailX0RatChunk001Sub000Block044Part005
    + surrogateDiagTailX0RatChunk001Sub000Block044Part006
    + surrogateDiagTailX0RatChunk001Sub000Block044Part007
    + surrogateDiagTailX0RatChunk001Sub000Block044Part008
    + surrogateDiagTailX0RatChunk001Sub000Block044Part009
    + surrogateDiagTailX0RatChunk001Sub000Block044Part010
    + surrogateDiagTailX0RatChunk001Sub000Block044Part011
    + surrogateDiagTailX0RatChunk001Sub000Block044Part012
    + surrogateDiagTailX0RatChunk001Sub000Block044Part013
    + surrogateDiagTailX0RatChunk001Sub000Block044Part014
    + surrogateDiagTailX0RatChunk001Sub000Block044Part015
    + surrogateDiagTailX0RatChunk001Sub000Block044Part016
    + surrogateDiagTailX0RatChunk001Sub000Block044Part017
    + surrogateDiagTailX0RatChunk001Sub000Block044Part018
    + surrogateDiagTailX0RatChunk001Sub000Block044Part019
    + surrogateDiagTailX0RatChunk001Sub000Block044Part020
    + surrogateDiagTailX0RatChunk001Sub000Block044Part021
    + surrogateDiagTailX0RatChunk001Sub000Block044Part022
    + surrogateDiagTailX0RatChunk001Sub000Block044Part023
    + surrogateDiagTailX0RatChunk001Sub000Block044Part024

theorem surrogateDiagTailX0RatChunk001Sub000Block044_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk001Sub000Block044Head + surrogateDiagTailX0RatChunk001Sub000Block044Mid + surrogateDiagTailX0RatChunk001Sub000Block044Tail =
      surrogateDiagTailX0RatChunk001Sub000Block044 := by
  unfold surrogateDiagTailX0RatChunk001Sub000Block044Head surrogateDiagTailX0RatChunk001Sub000Block044Mid surrogateDiagTailX0RatChunk001Sub000Block044Tail surrogateDiagTailX0RatChunk001Sub000Block044
  ring

def SurrogateDiagonalTailChunk001Sub000Block044HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block044HeadSum X0 = surrogateDiagTailX0RatChunk001Sub000Block044Head

def SurrogateDiagonalTailChunk001Sub000Block044MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block044MidSum X0 = surrogateDiagTailX0RatChunk001Sub000Block044Mid

def SurrogateDiagonalTailChunk001Sub000Block044TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block044TailSum X0 = surrogateDiagTailX0RatChunk001Sub000Block044Tail

theorem surrogateDiagonalTailChunk001Sub000Block044_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk001Sub000Block044HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk001Sub000Block044MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk001Sub000Block044TailCertificateAt X0) :
    surrogateDiagonalTailChunk001Sub000Block044Sum X0 = surrogateDiagTailX0RatChunk001Sub000Block044 := by
  unfold SurrogateDiagonalTailChunk001Sub000Block044HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk001Sub000Block044MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk001Sub000Block044TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk001Sub000Block044Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk001Sub000Block044_eq_head_add_mid_add_tail

/-- Block 045 covers tail-support indices [11125,11150) and q from 18343 to 18382. -/

def TailChunk001Sub000Block045Part000SupportExplicit : Finset ℕ :=
  ([18343] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block045Part000 : ℚ :=
  (353904179375 : ℚ) / 76816972633891405824

def SurrogateDiagonalTailChunk001Sub000Block045Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18343
    = surrogateDiagTailX0RatChunk001Sub000Block045Part000

theorem surrogateDiagonalTailChunk001Sub000Block045Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block045Part000CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block045Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block045Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block045Part000CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block045Part000SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block045Part000] using hcert

def TailChunk001Sub000Block045Part001SupportExplicit : Finset ℕ :=
  ([18345] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block045Part001 : ℚ :=
  (128492342425 : ℚ) / 1427419573809235968

def SurrogateDiagonalTailChunk001Sub000Block045Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18345
    = surrogateDiagTailX0RatChunk001Sub000Block045Part001

theorem surrogateDiagonalTailChunk001Sub000Block045Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block045Part001CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block045Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block045Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block045Part001CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block045Part001SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block045Part001] using hcert

def TailChunk001Sub000Block045Part002SupportExplicit : Finset ℕ :=
  ([18346] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block045Part002 : ℚ :=
  (1314748890625 : ℚ) / 4424080816323577632

def SurrogateDiagonalTailChunk001Sub000Block045Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18346
    = surrogateDiagTailX0RatChunk001Sub000Block045Part002

theorem surrogateDiagonalTailChunk001Sub000Block045Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block045Part002CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block045Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block045Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block045Part002CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block045Part002SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block045Part002] using hcert

def TailChunk001Sub000Block045Part003SupportExplicit : Finset ℕ :=
  ([18347] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block045Part003 : ℚ :=
  (17195064167 : ℚ) / 3053985855964185600

def SurrogateDiagonalTailChunk001Sub000Block045Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18347
    = surrogateDiagTailX0RatChunk001Sub000Block045Part003

theorem surrogateDiagonalTailChunk001Sub000Block045Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block045Part003CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block045Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block045Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block045Part003CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block045Part003SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block045Part003] using hcert

def TailChunk001Sub000Block045Part004SupportExplicit : Finset ℕ :=
  ([18349] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block045Part004 : ℚ :=
  (455956417 : ℚ) / 1045311190675648320

def SurrogateDiagonalTailChunk001Sub000Block045Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18349
    = surrogateDiagTailX0RatChunk001Sub000Block045Part004

theorem surrogateDiagonalTailChunk001Sub000Block045Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block045Part004CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block045Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block045Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block045Part004CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block045Part004SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block045Part004] using hcert

def TailChunk001Sub000Block045Part005SupportExplicit : Finset ℕ :=
  ([18353] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block045Part005 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block045Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18353
    = surrogateDiagTailX0RatChunk001Sub000Block045Part005

theorem surrogateDiagonalTailChunk001Sub000Block045Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block045Part005CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block045Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block045Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block045Part005CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block045Part005SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block045Part005] using hcert

def TailChunk001Sub000Block045Part006SupportExplicit : Finset ℕ :=
  ([18354] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block045Part006 : ℚ :=
  (2074408448125 : ℚ) / 1275065769416491008

def SurrogateDiagonalTailChunk001Sub000Block045Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18354
    = surrogateDiagTailX0RatChunk001Sub000Block045Part006

theorem surrogateDiagonalTailChunk001Sub000Block045Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block045Part006CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block045Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block045Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block045Part006CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block045Part006SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block045Part006] using hcert

def TailChunk001Sub000Block045Part007SupportExplicit : Finset ℕ :=
  ([18355] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block045Part007 : ℚ :=
  (2248151943 : ℚ) / 309670484417607680

def SurrogateDiagonalTailChunk001Sub000Block045Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18355
    = surrogateDiagTailX0RatChunk001Sub000Block045Part007

theorem surrogateDiagonalTailChunk001Sub000Block045Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block045Part007CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block045Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block045Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block045Part007CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block045Part007SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block045Part007] using hcert

def TailChunk001Sub000Block045Part008SupportExplicit : Finset ℕ :=
  ([18357] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block045Part008 : ℚ :=
  (1025689093 : ℚ) / 21255612678881280

def SurrogateDiagonalTailChunk001Sub000Block045Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18357
    = surrogateDiagTailX0RatChunk001Sub000Block045Part008

theorem surrogateDiagonalTailChunk001Sub000Block045Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block045Part008CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block045Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block045Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block045Part008CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block045Part008SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block045Part008] using hcert

def TailChunk001Sub000Block045Part009SupportExplicit : Finset ℕ :=
  ([18358] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block045Part009 : ℚ :=
  (566490550375 : ℚ) / 1803498249376530432

def SurrogateDiagonalTailChunk001Sub000Block045Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18358
    = surrogateDiagTailX0RatChunk001Sub000Block045Part009

theorem surrogateDiagonalTailChunk001Sub000Block045Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block045Part009CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block045Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block045Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block045Part009CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block045Part009SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block045Part009] using hcert

def TailChunk001Sub000Block045Part010SupportExplicit : Finset ℕ :=
  ([18359] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block045Part010 : ℚ :=
  (20983430797 : ℚ) / 7742318540253235200

def SurrogateDiagonalTailChunk001Sub000Block045Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18359
    = surrogateDiagTailX0RatChunk001Sub000Block045Part010

theorem surrogateDiagonalTailChunk001Sub000Block045Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block045Part010CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block045Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block045Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block045Part010CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block045Part010SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block045Part010] using hcert

def TailChunk001Sub000Block045Part011SupportExplicit : Finset ℕ :=
  ([18361] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block045Part011 : ℚ :=
  (39295352989 : ℚ) / 5227499679613747200

def SurrogateDiagonalTailChunk001Sub000Block045Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18361
    = surrogateDiagTailX0RatChunk001Sub000Block045Part011

theorem surrogateDiagonalTailChunk001Sub000Block045Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block045Part011CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block045Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block045Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block045Part011CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block045Part011SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block045Part011] using hcert

def TailChunk001Sub000Block045Part012SupportExplicit : Finset ℕ :=
  ([18362] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block045Part012 : ℚ :=
  (2107269025 : ℚ) / 7103257769240352

def SurrogateDiagonalTailChunk001Sub000Block045Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18362
    = surrogateDiagTailX0RatChunk001Sub000Block045Part012

theorem surrogateDiagonalTailChunk001Sub000Block045Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block045Part012CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block045Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block045Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block045Part012CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block045Part012SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block045Part012] using hcert

def TailChunk001Sub000Block045Part013SupportExplicit : Finset ℕ :=
  ([18363] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block045Part013 : ℚ :=
  (4683050069 : ℚ) / 112249011662069760

def SurrogateDiagonalTailChunk001Sub000Block045Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18363
    = surrogateDiagTailX0RatChunk001Sub000Block045Part013

theorem surrogateDiagonalTailChunk001Sub000Block045Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block045Part013CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block045Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block045Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block045Part013CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block045Part013SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block045Part013] using hcert

def TailChunk001Sub000Block045Part014SupportExplicit : Finset ℕ :=
  ([18365] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block045Part014 : ℚ :=
  (843974728375 : ℚ) / 116379775291233927168

def SurrogateDiagonalTailChunk001Sub000Block045Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18365
    = surrogateDiagTailX0RatChunk001Sub000Block045Part014

theorem surrogateDiagonalTailChunk001Sub000Block045Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block045Part014CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block045Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block045Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block045Part014CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block045Part014SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block045Part014] using hcert

def TailChunk001Sub000Block045Part015SupportExplicit : Finset ℕ :=
  ([18366] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block045Part015 : ℚ :=
  (585850111 : ℚ) / 3507781614439680

def SurrogateDiagonalTailChunk001Sub000Block045Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18366
    = surrogateDiagTailX0RatChunk001Sub000Block045Part015

theorem surrogateDiagonalTailChunk001Sub000Block045Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block045Part015CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block045Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block045Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block045Part015CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block045Part015SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block045Part015] using hcert

def TailChunk001Sub000Block045Part016SupportExplicit : Finset ℕ :=
  ([18367] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block045Part016 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block045Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18367
    = surrogateDiagTailX0RatChunk001Sub000Block045Part016

theorem surrogateDiagonalTailChunk001Sub000Block045Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block045Part016CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block045Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block045Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block045Part016CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block045Part016SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block045Part016] using hcert

def TailChunk001Sub000Block045Part017SupportExplicit : Finset ℕ :=
  ([18370] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block045Part017 : ℚ :=
  (7444977927 : ℚ) / 64809386890854400

def SurrogateDiagonalTailChunk001Sub000Block045Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18370
    = surrogateDiagTailX0RatChunk001Sub000Block045Part017

theorem surrogateDiagonalTailChunk001Sub000Block045Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block045Part017CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block045Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block045Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block045Part017CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block045Part017SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block045Part017] using hcert

def TailChunk001Sub000Block045Part018SupportExplicit : Finset ℕ :=
  ([18371] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block045Part018 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block045Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18371
    = surrogateDiagTailX0RatChunk001Sub000Block045Part018

theorem surrogateDiagonalTailChunk001Sub000Block045Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block045Part018CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block045Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block045Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block045Part018CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block045Part018SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block045Part018] using hcert

def TailChunk001Sub000Block045Part019SupportExplicit : Finset ℕ :=
  ([18373] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block045Part019 : ℚ :=
  (148500263525 : ℚ) / 114286620143968017984

def SurrogateDiagonalTailChunk001Sub000Block045Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18373
    = surrogateDiagTailX0RatChunk001Sub000Block045Part019

theorem surrogateDiagonalTailChunk001Sub000Block045Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block045Part019CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block045Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block045Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block045Part019CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block045Part019SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block045Part019] using hcert

def TailChunk001Sub000Block045Part020SupportExplicit : Finset ℕ :=
  ([18374] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block045Part020 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block045Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18374
    = surrogateDiagTailX0RatChunk001Sub000Block045Part020

theorem surrogateDiagonalTailChunk001Sub000Block045Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block045Part020CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block045Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block045Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block045Part020CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block045Part020SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block045Part020] using hcert

def TailChunk001Sub000Block045Part021SupportExplicit : Finset ℕ :=
  ([18377] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block045Part021 : ℚ :=
  (113414862075 : ℚ) / 28646897170365022208

def SurrogateDiagonalTailChunk001Sub000Block045Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18377
    = surrogateDiagTailX0RatChunk001Sub000Block045Part021

theorem surrogateDiagonalTailChunk001Sub000Block045Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block045Part021CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block045Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block045Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block045Part021CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block045Part021SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block045Part021] using hcert

def TailChunk001Sub000Block045Part022SupportExplicit : Finset ℕ :=
  ([18379] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block045Part022 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block045Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18379
    = surrogateDiagTailX0RatChunk001Sub000Block045Part022

theorem surrogateDiagonalTailChunk001Sub000Block045Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block045Part022CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block045Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block045Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block045Part022CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block045Part022SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block045Part022] using hcert

def TailChunk001Sub000Block045Part023SupportExplicit : Finset ℕ :=
  ([18381] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block045Part023 : ℚ :=
  (30223920657 : ℚ) / 509782290716262400

def SurrogateDiagonalTailChunk001Sub000Block045Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18381
    = surrogateDiagTailX0RatChunk001Sub000Block045Part023

theorem surrogateDiagonalTailChunk001Sub000Block045Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block045Part023CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block045Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block045Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block045Part023CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block045Part023SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block045Part023] using hcert

def TailChunk001Sub000Block045Part024SupportExplicit : Finset ℕ :=
  ([18382] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block045Part024 : ℚ :=
  (835735847 : ℚ) / 9955270656000000

def SurrogateDiagonalTailChunk001Sub000Block045Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18382
    = surrogateDiagTailX0RatChunk001Sub000Block045Part024

theorem surrogateDiagonalTailChunk001Sub000Block045Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block045Part024CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block045Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block045Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block045Part024CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block045Part024SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block045Part024] using hcert

def surrogateDiagonalTailChunk001Sub000Block045HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block045Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block045Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block045Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block045Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block045Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block045Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block045Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block045Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block045Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block045Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block045Head : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block045Part000
    + surrogateDiagTailX0RatChunk001Sub000Block045Part001
    + surrogateDiagTailX0RatChunk001Sub000Block045Part002
    + surrogateDiagTailX0RatChunk001Sub000Block045Part003
    + surrogateDiagTailX0RatChunk001Sub000Block045Part004
    + surrogateDiagTailX0RatChunk001Sub000Block045Part005
    + surrogateDiagTailX0RatChunk001Sub000Block045Part006
    + surrogateDiagTailX0RatChunk001Sub000Block045Part007
    + surrogateDiagTailX0RatChunk001Sub000Block045Part008
    + surrogateDiagTailX0RatChunk001Sub000Block045Part009

def surrogateDiagonalTailChunk001Sub000Block045MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block045Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block045Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block045Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block045Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block045Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block045Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block045Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block045Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block045Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block045Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block045Mid : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block045Part010
    + surrogateDiagTailX0RatChunk001Sub000Block045Part011
    + surrogateDiagTailX0RatChunk001Sub000Block045Part012
    + surrogateDiagTailX0RatChunk001Sub000Block045Part013
    + surrogateDiagTailX0RatChunk001Sub000Block045Part014
    + surrogateDiagTailX0RatChunk001Sub000Block045Part015
    + surrogateDiagTailX0RatChunk001Sub000Block045Part016
    + surrogateDiagTailX0RatChunk001Sub000Block045Part017
    + surrogateDiagTailX0RatChunk001Sub000Block045Part018
    + surrogateDiagTailX0RatChunk001Sub000Block045Part019

def surrogateDiagonalTailChunk001Sub000Block045TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block045Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block045Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block045Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block045Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block045Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block045Tail : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block045Part020
    + surrogateDiagTailX0RatChunk001Sub000Block045Part021
    + surrogateDiagTailX0RatChunk001Sub000Block045Part022
    + surrogateDiagTailX0RatChunk001Sub000Block045Part023
    + surrogateDiagTailX0RatChunk001Sub000Block045Part024

def surrogateDiagonalTailChunk001Sub000Block045Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk001Sub000Block045HeadSum X0
    + surrogateDiagonalTailChunk001Sub000Block045MidSum X0
    + surrogateDiagonalTailChunk001Sub000Block045TailSum X0

def surrogateDiagTailX0RatChunk001Sub000Block045 : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block045Part000
    + surrogateDiagTailX0RatChunk001Sub000Block045Part001
    + surrogateDiagTailX0RatChunk001Sub000Block045Part002
    + surrogateDiagTailX0RatChunk001Sub000Block045Part003
    + surrogateDiagTailX0RatChunk001Sub000Block045Part004
    + surrogateDiagTailX0RatChunk001Sub000Block045Part005
    + surrogateDiagTailX0RatChunk001Sub000Block045Part006
    + surrogateDiagTailX0RatChunk001Sub000Block045Part007
    + surrogateDiagTailX0RatChunk001Sub000Block045Part008
    + surrogateDiagTailX0RatChunk001Sub000Block045Part009
    + surrogateDiagTailX0RatChunk001Sub000Block045Part010
    + surrogateDiagTailX0RatChunk001Sub000Block045Part011
    + surrogateDiagTailX0RatChunk001Sub000Block045Part012
    + surrogateDiagTailX0RatChunk001Sub000Block045Part013
    + surrogateDiagTailX0RatChunk001Sub000Block045Part014
    + surrogateDiagTailX0RatChunk001Sub000Block045Part015
    + surrogateDiagTailX0RatChunk001Sub000Block045Part016
    + surrogateDiagTailX0RatChunk001Sub000Block045Part017
    + surrogateDiagTailX0RatChunk001Sub000Block045Part018
    + surrogateDiagTailX0RatChunk001Sub000Block045Part019
    + surrogateDiagTailX0RatChunk001Sub000Block045Part020
    + surrogateDiagTailX0RatChunk001Sub000Block045Part021
    + surrogateDiagTailX0RatChunk001Sub000Block045Part022
    + surrogateDiagTailX0RatChunk001Sub000Block045Part023
    + surrogateDiagTailX0RatChunk001Sub000Block045Part024

theorem surrogateDiagTailX0RatChunk001Sub000Block045_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk001Sub000Block045Head + surrogateDiagTailX0RatChunk001Sub000Block045Mid + surrogateDiagTailX0RatChunk001Sub000Block045Tail =
      surrogateDiagTailX0RatChunk001Sub000Block045 := by
  unfold surrogateDiagTailX0RatChunk001Sub000Block045Head surrogateDiagTailX0RatChunk001Sub000Block045Mid surrogateDiagTailX0RatChunk001Sub000Block045Tail surrogateDiagTailX0RatChunk001Sub000Block045
  ring

def SurrogateDiagonalTailChunk001Sub000Block045HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block045HeadSum X0 = surrogateDiagTailX0RatChunk001Sub000Block045Head

def SurrogateDiagonalTailChunk001Sub000Block045MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block045MidSum X0 = surrogateDiagTailX0RatChunk001Sub000Block045Mid

def SurrogateDiagonalTailChunk001Sub000Block045TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block045TailSum X0 = surrogateDiagTailX0RatChunk001Sub000Block045Tail

theorem surrogateDiagonalTailChunk001Sub000Block045_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk001Sub000Block045HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk001Sub000Block045MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk001Sub000Block045TailCertificateAt X0) :
    surrogateDiagonalTailChunk001Sub000Block045Sum X0 = surrogateDiagTailX0RatChunk001Sub000Block045 := by
  unfold SurrogateDiagonalTailChunk001Sub000Block045HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk001Sub000Block045MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk001Sub000Block045TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk001Sub000Block045Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk001Sub000Block045_eq_head_add_mid_add_tail

/-- Block 046 covers tail-support indices [11150,11175) and q from 18383 to 18422. -/

def TailChunk001Sub000Block046Part000SupportExplicit : Finset ℕ :=
  ([18383] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block046Part000 : ℚ :=
  (75011 : ℚ) / 101224934938800

def SurrogateDiagonalTailChunk001Sub000Block046Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18383
    = surrogateDiagTailX0RatChunk001Sub000Block046Part000

theorem surrogateDiagonalTailChunk001Sub000Block046Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block046Part000CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block046Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block046Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block046Part000CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block046Part000SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block046Part000] using hcert

def TailChunk001Sub000Block046Part001SupportExplicit : Finset ℕ :=
  ([18385] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block046Part001 : ℚ :=
  (1690034197525 : ℚ) / 116887705907616841728

def SurrogateDiagonalTailChunk001Sub000Block046Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18385
    = surrogateDiagTailX0RatChunk001Sub000Block046Part001

theorem surrogateDiagonalTailChunk001Sub000Block046Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block046Part001CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block046Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block046Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block046Part001CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block046Part001SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block046Part001] using hcert

def TailChunk001Sub000Block046Part002SupportExplicit : Finset ℕ :=
  ([18386] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block046Part002 : ℚ :=
  (7734757925 : ℚ) / 1094660076220956672

def SurrogateDiagonalTailChunk001Sub000Block046Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18386
    = surrogateDiagTailX0RatChunk001Sub000Block046Part002

theorem surrogateDiagonalTailChunk001Sub000Block046Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block046Part002CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block046Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block046Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block046Part002CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block046Part002SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block046Part002] using hcert

def TailChunk001Sub000Block046Part003SupportExplicit : Finset ℕ :=
  ([18389] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block046Part003 : ℚ :=
  (403310477 : ℚ) / 53341833465446400

def SurrogateDiagonalTailChunk001Sub000Block046Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18389
    = surrogateDiagTailX0RatChunk001Sub000Block046Part003

theorem surrogateDiagonalTailChunk001Sub000Block046Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block046Part003CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block046Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block046Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block046Part003CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block046Part003SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block046Part003] using hcert

def TailChunk001Sub000Block046Part004SupportExplicit : Finset ℕ :=
  ([18390] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block046Part004 : ℚ :=
  (751568264425 : ℚ) / 1436787349274492928

def SurrogateDiagonalTailChunk001Sub000Block046Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18390
    = surrogateDiagTailX0RatChunk001Sub000Block046Part004

theorem surrogateDiagonalTailChunk001Sub000Block046Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block046Part004CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block046Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block046Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block046Part004CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block046Part004SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block046Part004] using hcert

def TailChunk001Sub000Block046Part005SupportExplicit : Finset ℕ :=
  ([18391] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block046Part005 : ℚ :=
  (128277067375 : ℚ) / 262026145698039810048

def SurrogateDiagonalTailChunk001Sub000Block046Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18391
    = surrogateDiagTailX0RatChunk001Sub000Block046Part005

theorem surrogateDiagonalTailChunk001Sub000Block046Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block046Part005CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block046Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block046Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block046Part005CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block046Part005SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block046Part005] using hcert

def TailChunk001Sub000Block046Part006SupportExplicit : Finset ℕ :=
  ([18393] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block046Part006 : ℚ :=
  (9396725137 : ℚ) / 225968930926835520

def SurrogateDiagonalTailChunk001Sub000Block046Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18393
    = surrogateDiagTailX0RatChunk001Sub000Block046Part006

theorem surrogateDiagonalTailChunk001Sub000Block046Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block046Part006CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block046Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block046Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block046Part006CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block046Part006SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block046Part006] using hcert

def TailChunk001Sub000Block046Part007SupportExplicit : Finset ℕ :=
  ([18394] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block046Part007 : ℚ :=
  (250015489 : ℚ) / 20643249232281600

def SurrogateDiagonalTailChunk001Sub000Block046Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18394
    = surrogateDiagTailX0RatChunk001Sub000Block046Part007

theorem surrogateDiagonalTailChunk001Sub000Block046Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block046Part007CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block046Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block046Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block046Part007CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block046Part007SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block046Part007] using hcert

def TailChunk001Sub000Block046Part008SupportExplicit : Finset ℕ :=
  ([18395] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block046Part008 : ℚ :=
  (1749431171725 : ℚ) / 83943725880857591808

def SurrogateDiagonalTailChunk001Sub000Block046Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18395
    = surrogateDiagTailX0RatChunk001Sub000Block046Part008

theorem surrogateDiagonalTailChunk001Sub000Block046Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block046Part008CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block046Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block046Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block046Part008CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block046Part008SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block046Part008] using hcert

def TailChunk001Sub000Block046Part009SupportExplicit : Finset ℕ :=
  ([18397] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block046Part009 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block046Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18397
    = surrogateDiagTailX0RatChunk001Sub000Block046Part009

theorem surrogateDiagonalTailChunk001Sub000Block046Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block046Part009CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block046Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block046Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block046Part009CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block046Part009SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block046Part009] using hcert

def TailChunk001Sub000Block046Part010SupportExplicit : Finset ℕ :=
  ([18398] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block046Part010 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block046Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18398
    = surrogateDiagTailX0RatChunk001Sub000Block046Part010

theorem surrogateDiagonalTailChunk001Sub000Block046Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block046Part010CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block046Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block046Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block046Part010CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block046Part010SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block046Part010] using hcert

def TailChunk001Sub000Block046Part011SupportExplicit : Finset ℕ :=
  ([18399] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block046Part011 : ℚ :=
  (5996719475 : ℚ) / 144301006147463424

def SurrogateDiagonalTailChunk001Sub000Block046Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18399
    = surrogateDiagTailX0RatChunk001Sub000Block046Part011

theorem surrogateDiagonalTailChunk001Sub000Block046Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block046Part011CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block046Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block046Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block046Part011CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block046Part011SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block046Part011] using hcert

def TailChunk001Sub000Block046Part012SupportExplicit : Finset ℕ :=
  ([18401] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block046Part012 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block046Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18401
    = surrogateDiagTailX0RatChunk001Sub000Block046Part012

theorem surrogateDiagonalTailChunk001Sub000Block046Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block046Part012CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block046Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block046Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block046Part012CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block046Part012SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block046Part012] using hcert

def TailChunk001Sub000Block046Part013SupportExplicit : Finset ℕ :=
  ([18402] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block046Part013 : ℚ :=
  (42010525775 : ℚ) / 252526760758060992

def SurrogateDiagonalTailChunk001Sub000Block046Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18402
    = surrogateDiagTailX0RatChunk001Sub000Block046Part013

theorem surrogateDiagonalTailChunk001Sub000Block046Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block046Part013CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block046Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block046Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block046Part013CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block046Part013SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block046Part013] using hcert

def TailChunk001Sub000Block046Part014SupportExplicit : Finset ℕ :=
  ([18403] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block046Part014 : ℚ :=
  (1859361919 : ℚ) / 166364121605326848

def SurrogateDiagonalTailChunk001Sub000Block046Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18403
    = surrogateDiagTailX0RatChunk001Sub000Block046Part014

theorem surrogateDiagonalTailChunk001Sub000Block046Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block046Part014CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block046Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block046Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block046Part014CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block046Part014SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block046Part014] using hcert

def TailChunk001Sub000Block046Part015SupportExplicit : Finset ℕ :=
  ([18406] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block046Part015 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block046Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18406
    = surrogateDiagTailX0RatChunk001Sub000Block046Part015

theorem surrogateDiagonalTailChunk001Sub000Block046Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block046Part015CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block046Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block046Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block046Part015CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block046Part015SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block046Part015] using hcert

def TailChunk001Sub000Block046Part016SupportExplicit : Finset ℕ :=
  ([18407] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block046Part016 : ℚ :=
  (48982637075 : ℚ) / 134068642979330801664

def SurrogateDiagonalTailChunk001Sub000Block046Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18407
    = surrogateDiagTailX0RatChunk001Sub000Block046Part016

theorem surrogateDiagonalTailChunk001Sub000Block046Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block046Part016CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block046Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block046Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block046Part016CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block046Part016SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block046Part016] using hcert

def TailChunk001Sub000Block046Part017SupportExplicit : Finset ℕ :=
  ([18409] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block046Part017 : ℚ :=
  (3004266053 : ℚ) / 5157139460495769600

def SurrogateDiagonalTailChunk001Sub000Block046Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18409
    = surrogateDiagTailX0RatChunk001Sub000Block046Part017

theorem surrogateDiagonalTailChunk001Sub000Block046Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block046Part017CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block046Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block046Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block046Part017CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block046Part017SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block046Part017] using hcert

def TailChunk001Sub000Block046Part018SupportExplicit : Finset ℕ :=
  ([18410] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block046Part018 : ℚ :=
  (199160008975 : ℚ) / 977275473908539392

def SurrogateDiagonalTailChunk001Sub000Block046Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18410
    = surrogateDiagTailX0RatChunk001Sub000Block046Part018

theorem surrogateDiagonalTailChunk001Sub000Block046Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block046Part018CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block046Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block046Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block046Part018CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block046Part018SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block046Part018] using hcert

def TailChunk001Sub000Block046Part019SupportExplicit : Finset ℕ :=
  ([18413] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block046Part019 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block046Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18413
    = surrogateDiagTailX0RatChunk001Sub000Block046Part019

theorem surrogateDiagonalTailChunk001Sub000Block046Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block046Part019CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block046Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block046Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block046Part019CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block046Part019SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block046Part019] using hcert

def TailChunk001Sub000Block046Part020SupportExplicit : Finset ℕ :=
  ([18415] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block046Part020 : ℚ :=
  (96989377525 : ℚ) / 5509454806366027776

def SurrogateDiagonalTailChunk001Sub000Block046Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18415
    = surrogateDiagTailX0RatChunk001Sub000Block046Part020

theorem surrogateDiagonalTailChunk001Sub000Block046Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block046Part020CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block046Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block046Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block046Part020CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block046Part020SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block046Part020] using hcert

def TailChunk001Sub000Block046Part021SupportExplicit : Finset ℕ :=
  ([18417] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block046Part021 : ℚ :=
  (2066242048525 : ℚ) / 30532914933406138368

def SurrogateDiagonalTailChunk001Sub000Block046Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18417
    = surrogateDiagTailX0RatChunk001Sub000Block046Part021

theorem surrogateDiagonalTailChunk001Sub000Block046Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block046Part021CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block046Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block046Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block046Part021CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block046Part021SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block046Part021] using hcert

def TailChunk001Sub000Block046Part022SupportExplicit : Finset ℕ :=
  ([18418] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block046Part022 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block046Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18418
    = surrogateDiagTailX0RatChunk001Sub000Block046Part022

theorem surrogateDiagonalTailChunk001Sub000Block046Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block046Part022CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block046Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block046Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block046Part022CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block046Part022SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block046Part022] using hcert

def TailChunk001Sub000Block046Part023SupportExplicit : Finset ℕ :=
  ([18419] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block046Part023 : ℚ :=
  (5382686875 : ℚ) / 16937098961948540928

def SurrogateDiagonalTailChunk001Sub000Block046Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18419
    = surrogateDiagTailX0RatChunk001Sub000Block046Part023

theorem surrogateDiagonalTailChunk001Sub000Block046Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block046Part023CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block046Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block046Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block046Part023CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block046Part023SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block046Part023] using hcert

def TailChunk001Sub000Block046Part024SupportExplicit : Finset ℕ :=
  ([18422] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block046Part024 : ℚ :=
  (518913233 : ℚ) / 131246244000000000

def SurrogateDiagonalTailChunk001Sub000Block046Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18422
    = surrogateDiagTailX0RatChunk001Sub000Block046Part024

theorem surrogateDiagonalTailChunk001Sub000Block046Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block046Part024CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block046Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block046Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block046Part024CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block046Part024SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block046Part024] using hcert

def surrogateDiagonalTailChunk001Sub000Block046HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block046Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block046Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block046Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block046Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block046Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block046Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block046Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block046Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block046Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block046Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block046Head : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block046Part000
    + surrogateDiagTailX0RatChunk001Sub000Block046Part001
    + surrogateDiagTailX0RatChunk001Sub000Block046Part002
    + surrogateDiagTailX0RatChunk001Sub000Block046Part003
    + surrogateDiagTailX0RatChunk001Sub000Block046Part004
    + surrogateDiagTailX0RatChunk001Sub000Block046Part005
    + surrogateDiagTailX0RatChunk001Sub000Block046Part006
    + surrogateDiagTailX0RatChunk001Sub000Block046Part007
    + surrogateDiagTailX0RatChunk001Sub000Block046Part008
    + surrogateDiagTailX0RatChunk001Sub000Block046Part009

def surrogateDiagonalTailChunk001Sub000Block046MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block046Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block046Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block046Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block046Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block046Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block046Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block046Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block046Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block046Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block046Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block046Mid : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block046Part010
    + surrogateDiagTailX0RatChunk001Sub000Block046Part011
    + surrogateDiagTailX0RatChunk001Sub000Block046Part012
    + surrogateDiagTailX0RatChunk001Sub000Block046Part013
    + surrogateDiagTailX0RatChunk001Sub000Block046Part014
    + surrogateDiagTailX0RatChunk001Sub000Block046Part015
    + surrogateDiagTailX0RatChunk001Sub000Block046Part016
    + surrogateDiagTailX0RatChunk001Sub000Block046Part017
    + surrogateDiagTailX0RatChunk001Sub000Block046Part018
    + surrogateDiagTailX0RatChunk001Sub000Block046Part019

def surrogateDiagonalTailChunk001Sub000Block046TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block046Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block046Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block046Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block046Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block046Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block046Tail : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block046Part020
    + surrogateDiagTailX0RatChunk001Sub000Block046Part021
    + surrogateDiagTailX0RatChunk001Sub000Block046Part022
    + surrogateDiagTailX0RatChunk001Sub000Block046Part023
    + surrogateDiagTailX0RatChunk001Sub000Block046Part024

def surrogateDiagonalTailChunk001Sub000Block046Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk001Sub000Block046HeadSum X0
    + surrogateDiagonalTailChunk001Sub000Block046MidSum X0
    + surrogateDiagonalTailChunk001Sub000Block046TailSum X0

def surrogateDiagTailX0RatChunk001Sub000Block046 : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block046Part000
    + surrogateDiagTailX0RatChunk001Sub000Block046Part001
    + surrogateDiagTailX0RatChunk001Sub000Block046Part002
    + surrogateDiagTailX0RatChunk001Sub000Block046Part003
    + surrogateDiagTailX0RatChunk001Sub000Block046Part004
    + surrogateDiagTailX0RatChunk001Sub000Block046Part005
    + surrogateDiagTailX0RatChunk001Sub000Block046Part006
    + surrogateDiagTailX0RatChunk001Sub000Block046Part007
    + surrogateDiagTailX0RatChunk001Sub000Block046Part008
    + surrogateDiagTailX0RatChunk001Sub000Block046Part009
    + surrogateDiagTailX0RatChunk001Sub000Block046Part010
    + surrogateDiagTailX0RatChunk001Sub000Block046Part011
    + surrogateDiagTailX0RatChunk001Sub000Block046Part012
    + surrogateDiagTailX0RatChunk001Sub000Block046Part013
    + surrogateDiagTailX0RatChunk001Sub000Block046Part014
    + surrogateDiagTailX0RatChunk001Sub000Block046Part015
    + surrogateDiagTailX0RatChunk001Sub000Block046Part016
    + surrogateDiagTailX0RatChunk001Sub000Block046Part017
    + surrogateDiagTailX0RatChunk001Sub000Block046Part018
    + surrogateDiagTailX0RatChunk001Sub000Block046Part019
    + surrogateDiagTailX0RatChunk001Sub000Block046Part020
    + surrogateDiagTailX0RatChunk001Sub000Block046Part021
    + surrogateDiagTailX0RatChunk001Sub000Block046Part022
    + surrogateDiagTailX0RatChunk001Sub000Block046Part023
    + surrogateDiagTailX0RatChunk001Sub000Block046Part024

theorem surrogateDiagTailX0RatChunk001Sub000Block046_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk001Sub000Block046Head + surrogateDiagTailX0RatChunk001Sub000Block046Mid + surrogateDiagTailX0RatChunk001Sub000Block046Tail =
      surrogateDiagTailX0RatChunk001Sub000Block046 := by
  unfold surrogateDiagTailX0RatChunk001Sub000Block046Head surrogateDiagTailX0RatChunk001Sub000Block046Mid surrogateDiagTailX0RatChunk001Sub000Block046Tail surrogateDiagTailX0RatChunk001Sub000Block046
  ring

def SurrogateDiagonalTailChunk001Sub000Block046HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block046HeadSum X0 = surrogateDiagTailX0RatChunk001Sub000Block046Head

def SurrogateDiagonalTailChunk001Sub000Block046MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block046MidSum X0 = surrogateDiagTailX0RatChunk001Sub000Block046Mid

def SurrogateDiagonalTailChunk001Sub000Block046TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block046TailSum X0 = surrogateDiagTailX0RatChunk001Sub000Block046Tail

theorem surrogateDiagonalTailChunk001Sub000Block046_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk001Sub000Block046HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk001Sub000Block046MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk001Sub000Block046TailCertificateAt X0) :
    surrogateDiagonalTailChunk001Sub000Block046Sum X0 = surrogateDiagTailX0RatChunk001Sub000Block046 := by
  unfold SurrogateDiagonalTailChunk001Sub000Block046HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk001Sub000Block046MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk001Sub000Block046TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk001Sub000Block046Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk001Sub000Block046_eq_head_add_mid_add_tail

/-- Block 047 covers tail-support indices [11175,11200) and q from 18426 to 18462. -/

def TailChunk001Sub000Block047Part000SupportExplicit : Finset ℕ :=
  ([18426] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block047Part000 : ℚ :=
  (1160947060225 : ℚ) / 3038171280930275328

def SurrogateDiagonalTailChunk001Sub000Block047Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18426
    = surrogateDiagTailX0RatChunk001Sub000Block047Part000

theorem surrogateDiagonalTailChunk001Sub000Block047Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block047Part000CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block047Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block047Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block047Part000CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block047Part000SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block047Part000] using hcert

def TailChunk001Sub000Block047Part001SupportExplicit : Finset ℕ :=
  ([18427] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block047Part001 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block047Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18427
    = surrogateDiagTailX0RatChunk001Sub000Block047Part001

theorem surrogateDiagonalTailChunk001Sub000Block047Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block047Part001CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block047Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block047Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block047Part001CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block047Part001SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block047Part001] using hcert

def TailChunk001Sub000Block047Part002SupportExplicit : Finset ℕ :=
  ([18429] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block047Part002 : ℚ :=
  (1179192641975 : ℚ) / 28467943440175915584

def SurrogateDiagonalTailChunk001Sub000Block047Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18429
    = surrogateDiagTailX0RatChunk001Sub000Block047Part002

theorem surrogateDiagonalTailChunk001Sub000Block047Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block047Part002CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block047Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block047Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block047Part002CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block047Part002SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block047Part002] using hcert

def TailChunk001Sub000Block047Part003SupportExplicit : Finset ℕ :=
  ([18430] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block047Part003 : ℚ :=
  (705094935175 : ℚ) / 5707445547741216768

def SurrogateDiagonalTailChunk001Sub000Block047Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18430
    = surrogateDiagTailX0RatChunk001Sub000Block047Part003

theorem surrogateDiagonalTailChunk001Sub000Block047Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block047Part003CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block047Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block047Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block047Part003CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block047Part003SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block047Part003] using hcert

def TailChunk001Sub000Block047Part004SupportExplicit : Finset ℕ :=
  ([18431] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block047Part004 : ℚ :=
  (433814816675 : ℚ) / 77758057808618471424

def SurrogateDiagonalTailChunk001Sub000Block047Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18431
    = surrogateDiagTailX0RatChunk001Sub000Block047Part004

theorem surrogateDiagonalTailChunk001Sub000Block047Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block047Part004CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block047Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block047Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block047Part004CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block047Part004SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block047Part004] using hcert

def TailChunk001Sub000Block047Part005SupportExplicit : Finset ℕ :=
  ([18433] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block047Part005 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block047Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18433
    = surrogateDiagTailX0RatChunk001Sub000Block047Part005

theorem surrogateDiagonalTailChunk001Sub000Block047Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block047Part005CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block047Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block047Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block047Part005CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block047Part005SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block047Part005] using hcert

def TailChunk001Sub000Block047Part006SupportExplicit : Finset ℕ :=
  ([18434] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block047Part006 : ℚ :=
  (55698071275 : ℚ) / 3257053426569388032

def SurrogateDiagonalTailChunk001Sub000Block047Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18434
    = surrogateDiagTailX0RatChunk001Sub000Block047Part006

theorem surrogateDiagonalTailChunk001Sub000Block047Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block047Part006CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block047Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block047Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block047Part006CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block047Part006SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block047Part006] using hcert

def TailChunk001Sub000Block047Part007SupportExplicit : Finset ℕ :=
  ([18435] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block047Part007 : ℚ :=
  (519022771225 : ℚ) / 5822644601356419072

def SurrogateDiagonalTailChunk001Sub000Block047Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18435
    = surrogateDiagTailX0RatChunk001Sub000Block047Part007

theorem surrogateDiagonalTailChunk001Sub000Block047Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block047Part007CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block047Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block047Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block047Part007CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block047Part007SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block047Part007] using hcert

def TailChunk001Sub000Block047Part008SupportExplicit : Finset ℕ :=
  ([18437] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block047Part008 : ℚ :=
  (43338652775 : ℚ) / 135855604585520668224

def SurrogateDiagonalTailChunk001Sub000Block047Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18437
    = surrogateDiagTailX0RatChunk001Sub000Block047Part008

theorem surrogateDiagonalTailChunk001Sub000Block047Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block047Part008CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block047Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block047Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block047Part008CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block047Part008SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block047Part008] using hcert

def TailChunk001Sub000Block047Part009SupportExplicit : Finset ℕ :=
  ([18438] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block047Part009 : ℚ :=
  (565290249425 : ℚ) / 954153591668941824

def SurrogateDiagonalTailChunk001Sub000Block047Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18438
    = surrogateDiagTailX0RatChunk001Sub000Block047Part009

theorem surrogateDiagonalTailChunk001Sub000Block047Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block047Part009CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block047Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block047Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block047Part009CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block047Part009SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block047Part009] using hcert

def TailChunk001Sub000Block047Part010SupportExplicit : Finset ℕ :=
  ([18439] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block047Part010 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block047Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18439
    = surrogateDiagTailX0RatChunk001Sub000Block047Part010

theorem surrogateDiagonalTailChunk001Sub000Block047Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block047Part010CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block047Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block047Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block047Part010CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block047Part010SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block047Part010] using hcert

def TailChunk001Sub000Block047Part011SupportExplicit : Finset ℕ :=
  ([18442] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block047Part011 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block047Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18442
    = surrogateDiagTailX0RatChunk001Sub000Block047Part011

theorem surrogateDiagonalTailChunk001Sub000Block047Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block047Part011CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block047Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block047Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block047Part011CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block047Part011SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block047Part011] using hcert

def TailChunk001Sub000Block047Part012SupportExplicit : Finset ℕ :=
  ([18443] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block047Part012 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block047Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18443
    = surrogateDiagTailX0RatChunk001Sub000Block047Part012

theorem surrogateDiagonalTailChunk001Sub000Block047Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block047Part012CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block047Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block047Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block047Part012CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block047Part012SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block047Part012] using hcert

def TailChunk001Sub000Block047Part013SupportExplicit : Finset ℕ :=
  ([18445] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block047Part013 : ℚ :=
  (789410161 : ℚ) / 24466073164185600

def SurrogateDiagonalTailChunk001Sub000Block047Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18445
    = surrogateDiagTailX0RatChunk001Sub000Block047Part013

theorem surrogateDiagonalTailChunk001Sub000Block047Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block047Part013CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block047Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block047Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block047Part013CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block047Part013SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block047Part013] using hcert

def TailChunk001Sub000Block047Part014SupportExplicit : Finset ℕ :=
  ([18446] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block047Part014 : ℚ :=
  (1092411359 : ℚ) / 119963059814400000

def SurrogateDiagonalTailChunk001Sub000Block047Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18446
    = surrogateDiagTailX0RatChunk001Sub000Block047Part014

theorem surrogateDiagonalTailChunk001Sub000Block047Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block047Part014CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block047Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block047Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block047Part014CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block047Part014SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block047Part014] using hcert

def TailChunk001Sub000Block047Part015SupportExplicit : Finset ℕ :=
  ([18447] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block047Part015 : ℚ :=
  (86102285881 : ℚ) / 1032592529306419200

def SurrogateDiagonalTailChunk001Sub000Block047Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18447
    = surrogateDiagTailX0RatChunk001Sub000Block047Part015

theorem surrogateDiagonalTailChunk001Sub000Block047Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block047Part015CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block047Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block047Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block047Part015CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block047Part015SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block047Part015] using hcert

def TailChunk001Sub000Block047Part016SupportExplicit : Finset ℕ :=
  ([18449] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block047Part016 : ℚ :=
  (1432427983 : ℚ) / 929530849221645120

def SurrogateDiagonalTailChunk001Sub000Block047Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18449
    = surrogateDiagTailX0RatChunk001Sub000Block047Part016

theorem surrogateDiagonalTailChunk001Sub000Block047Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block047Part016CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block047Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block047Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block047Part016CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block047Part016SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block047Part016] using hcert

def TailChunk001Sub000Block047Part017SupportExplicit : Finset ℕ :=
  ([18451] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block047Part017 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block047Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18451
    = surrogateDiagTailX0RatChunk001Sub000Block047Part017

theorem surrogateDiagonalTailChunk001Sub000Block047Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block047Part017CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block047Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block047Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block047Part017CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block047Part017SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block047Part017] using hcert

def TailChunk001Sub000Block047Part018SupportExplicit : Finset ℕ :=
  ([18453] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block047Part018 : ℚ :=
  (1891625027 : ℚ) / 45786483665640000

def SurrogateDiagonalTailChunk001Sub000Block047Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18453
    = surrogateDiagTailX0RatChunk001Sub000Block047Part018

theorem surrogateDiagonalTailChunk001Sub000Block047Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block047Part018CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block047Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block047Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block047Part018CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block047Part018SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block047Part018] using hcert

def TailChunk001Sub000Block047Part019SupportExplicit : Finset ℕ :=
  ([18454] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block047Part019 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block047Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18454
    = surrogateDiagTailX0RatChunk001Sub000Block047Part019

theorem surrogateDiagonalTailChunk001Sub000Block047Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block047Part019CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block047Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block047Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block047Part019CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block047Part019SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block047Part019] using hcert

def TailChunk001Sub000Block047Part020SupportExplicit : Finset ℕ :=
  ([18455] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block047Part020 : ℚ :=
  (6818055809 : ℚ) / 949428525290711040

def SurrogateDiagonalTailChunk001Sub000Block047Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18455
    = surrogateDiagTailX0RatChunk001Sub000Block047Part020

theorem surrogateDiagonalTailChunk001Sub000Block047Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block047Part020CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block047Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block047Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block047Part020CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block047Part020SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block047Part020] using hcert

def TailChunk001Sub000Block047Part021SupportExplicit : Finset ℕ :=
  ([18457] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block047Part021 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block047Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18457
    = surrogateDiagTailX0RatChunk001Sub000Block047Part021

theorem surrogateDiagonalTailChunk001Sub000Block047Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block047Part021CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block047Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block047Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block047Part021CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block047Part021SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block047Part021] using hcert

def TailChunk001Sub000Block047Part022SupportExplicit : Finset ℕ :=
  ([18458] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block047Part022 : ℚ :=
  (1064820103 : ℚ) / 49324526486310720

def SurrogateDiagonalTailChunk001Sub000Block047Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18458
    = surrogateDiagTailX0RatChunk001Sub000Block047Part022

theorem surrogateDiagonalTailChunk001Sub000Block047Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block047Part022CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block047Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block047Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block047Part022CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block047Part022SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block047Part022] using hcert

def TailChunk001Sub000Block047Part023SupportExplicit : Finset ℕ :=
  ([18461] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block047Part023 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block047Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18461
    = surrogateDiagTailX0RatChunk001Sub000Block047Part023

theorem surrogateDiagonalTailChunk001Sub000Block047Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block047Part023CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block047Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block047Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block047Part023CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block047Part023SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block047Part023] using hcert

def TailChunk001Sub000Block047Part024SupportExplicit : Finset ℕ :=
  ([18462] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block047Part024 : ℚ :=
  (15464829053 : ℚ) / 36699109746278400

def SurrogateDiagonalTailChunk001Sub000Block047Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18462
    = surrogateDiagTailX0RatChunk001Sub000Block047Part024

theorem surrogateDiagonalTailChunk001Sub000Block047Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block047Part024CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block047Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block047Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block047Part024CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block047Part024SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block047Part024] using hcert

def surrogateDiagonalTailChunk001Sub000Block047HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block047Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block047Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block047Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block047Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block047Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block047Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block047Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block047Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block047Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block047Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block047Head : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block047Part000
    + surrogateDiagTailX0RatChunk001Sub000Block047Part001
    + surrogateDiagTailX0RatChunk001Sub000Block047Part002
    + surrogateDiagTailX0RatChunk001Sub000Block047Part003
    + surrogateDiagTailX0RatChunk001Sub000Block047Part004
    + surrogateDiagTailX0RatChunk001Sub000Block047Part005
    + surrogateDiagTailX0RatChunk001Sub000Block047Part006
    + surrogateDiagTailX0RatChunk001Sub000Block047Part007
    + surrogateDiagTailX0RatChunk001Sub000Block047Part008
    + surrogateDiagTailX0RatChunk001Sub000Block047Part009

def surrogateDiagonalTailChunk001Sub000Block047MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block047Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block047Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block047Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block047Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block047Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block047Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block047Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block047Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block047Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block047Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block047Mid : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block047Part010
    + surrogateDiagTailX0RatChunk001Sub000Block047Part011
    + surrogateDiagTailX0RatChunk001Sub000Block047Part012
    + surrogateDiagTailX0RatChunk001Sub000Block047Part013
    + surrogateDiagTailX0RatChunk001Sub000Block047Part014
    + surrogateDiagTailX0RatChunk001Sub000Block047Part015
    + surrogateDiagTailX0RatChunk001Sub000Block047Part016
    + surrogateDiagTailX0RatChunk001Sub000Block047Part017
    + surrogateDiagTailX0RatChunk001Sub000Block047Part018
    + surrogateDiagTailX0RatChunk001Sub000Block047Part019

def surrogateDiagonalTailChunk001Sub000Block047TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block047Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block047Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block047Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block047Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block047Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block047Tail : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block047Part020
    + surrogateDiagTailX0RatChunk001Sub000Block047Part021
    + surrogateDiagTailX0RatChunk001Sub000Block047Part022
    + surrogateDiagTailX0RatChunk001Sub000Block047Part023
    + surrogateDiagTailX0RatChunk001Sub000Block047Part024

def surrogateDiagonalTailChunk001Sub000Block047Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk001Sub000Block047HeadSum X0
    + surrogateDiagonalTailChunk001Sub000Block047MidSum X0
    + surrogateDiagonalTailChunk001Sub000Block047TailSum X0

def surrogateDiagTailX0RatChunk001Sub000Block047 : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block047Part000
    + surrogateDiagTailX0RatChunk001Sub000Block047Part001
    + surrogateDiagTailX0RatChunk001Sub000Block047Part002
    + surrogateDiagTailX0RatChunk001Sub000Block047Part003
    + surrogateDiagTailX0RatChunk001Sub000Block047Part004
    + surrogateDiagTailX0RatChunk001Sub000Block047Part005
    + surrogateDiagTailX0RatChunk001Sub000Block047Part006
    + surrogateDiagTailX0RatChunk001Sub000Block047Part007
    + surrogateDiagTailX0RatChunk001Sub000Block047Part008
    + surrogateDiagTailX0RatChunk001Sub000Block047Part009
    + surrogateDiagTailX0RatChunk001Sub000Block047Part010
    + surrogateDiagTailX0RatChunk001Sub000Block047Part011
    + surrogateDiagTailX0RatChunk001Sub000Block047Part012
    + surrogateDiagTailX0RatChunk001Sub000Block047Part013
    + surrogateDiagTailX0RatChunk001Sub000Block047Part014
    + surrogateDiagTailX0RatChunk001Sub000Block047Part015
    + surrogateDiagTailX0RatChunk001Sub000Block047Part016
    + surrogateDiagTailX0RatChunk001Sub000Block047Part017
    + surrogateDiagTailX0RatChunk001Sub000Block047Part018
    + surrogateDiagTailX0RatChunk001Sub000Block047Part019
    + surrogateDiagTailX0RatChunk001Sub000Block047Part020
    + surrogateDiagTailX0RatChunk001Sub000Block047Part021
    + surrogateDiagTailX0RatChunk001Sub000Block047Part022
    + surrogateDiagTailX0RatChunk001Sub000Block047Part023
    + surrogateDiagTailX0RatChunk001Sub000Block047Part024

theorem surrogateDiagTailX0RatChunk001Sub000Block047_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk001Sub000Block047Head + surrogateDiagTailX0RatChunk001Sub000Block047Mid + surrogateDiagTailX0RatChunk001Sub000Block047Tail =
      surrogateDiagTailX0RatChunk001Sub000Block047 := by
  unfold surrogateDiagTailX0RatChunk001Sub000Block047Head surrogateDiagTailX0RatChunk001Sub000Block047Mid surrogateDiagTailX0RatChunk001Sub000Block047Tail surrogateDiagTailX0RatChunk001Sub000Block047
  ring

def SurrogateDiagonalTailChunk001Sub000Block047HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block047HeadSum X0 = surrogateDiagTailX0RatChunk001Sub000Block047Head

def SurrogateDiagonalTailChunk001Sub000Block047MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block047MidSum X0 = surrogateDiagTailX0RatChunk001Sub000Block047Mid

def SurrogateDiagonalTailChunk001Sub000Block047TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block047TailSum X0 = surrogateDiagTailX0RatChunk001Sub000Block047Tail

theorem surrogateDiagonalTailChunk001Sub000Block047_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk001Sub000Block047HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk001Sub000Block047MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk001Sub000Block047TailCertificateAt X0) :
    surrogateDiagonalTailChunk001Sub000Block047Sum X0 = surrogateDiagTailX0RatChunk001Sub000Block047 := by
  unfold SurrogateDiagonalTailChunk001Sub000Block047HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk001Sub000Block047MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk001Sub000Block047TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk001Sub000Block047Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk001Sub000Block047_eq_head_add_mid_add_tail

/-- Block 048 covers tail-support indices [11200,11225) and q from 18463 to 18506. -/

def TailChunk001Sub000Block048Part000SupportExplicit : Finset ℕ :=
  ([18463] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block048Part000 : ℚ :=
  (20745468125 : ℚ) / 32289717542496143616

def SurrogateDiagonalTailChunk001Sub000Block048Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18463
    = surrogateDiagTailX0RatChunk001Sub000Block048Part000

theorem surrogateDiagonalTailChunk001Sub000Block048Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block048Part000CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block048Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block048Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block048Part000CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block048Part000SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block048Part000] using hcert

def TailChunk001Sub000Block048Part001SupportExplicit : Finset ℕ :=
  ([18465] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block048Part001 : ℚ :=
  (42334369 : ℚ) / 476477228390400

def SurrogateDiagonalTailChunk001Sub000Block048Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18465
    = surrogateDiagTailX0RatChunk001Sub000Block048Part001

theorem surrogateDiagonalTailChunk001Sub000Block048Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block048Part001CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block048Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block048Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block048Part001CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block048Part001SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block048Part001] using hcert

def TailChunk001Sub000Block048Part002SupportExplicit : Finset ℕ :=
  ([18466] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block048Part002 : ℚ :=
  (18191949475 : ℚ) / 543276596040169536

def SurrogateDiagonalTailChunk001Sub000Block048Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18466
    = surrogateDiagTailX0RatChunk001Sub000Block048Part002

theorem surrogateDiagonalTailChunk001Sub000Block048Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block048Part002CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block048Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block048Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block048Part002CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block048Part002SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block048Part002] using hcert

def TailChunk001Sub000Block048Part003SupportExplicit : Finset ℕ :=
  ([18467] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block048Part003 : ℚ :=
  (19204891375 : ℚ) / 44689547659776933888

def SurrogateDiagonalTailChunk001Sub000Block048Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18467
    = surrogateDiagTailX0RatChunk001Sub000Block048Part003

theorem surrogateDiagonalTailChunk001Sub000Block048Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block048Part003CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block048Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block048Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block048Part003CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block048Part003SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block048Part003] using hcert

def TailChunk001Sub000Block048Part004SupportExplicit : Finset ℕ :=
  ([18469] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block048Part004 : ℚ :=
  (10041673429 : ℚ) / 2098873694512742400

def SurrogateDiagonalTailChunk001Sub000Block048Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18469
    = surrogateDiagTailX0RatChunk001Sub000Block048Part004

theorem surrogateDiagonalTailChunk001Sub000Block048Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block048Part004CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block048Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block048Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block048Part004CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block048Part004SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block048Part004] using hcert

def TailChunk001Sub000Block048Part005SupportExplicit : Finset ℕ :=
  ([18470] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block048Part005 : ℚ :=
  (79992658025 : ℚ) / 929188067385866496

def SurrogateDiagonalTailChunk001Sub000Block048Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18470
    = surrogateDiagTailX0RatChunk001Sub000Block048Part005

theorem surrogateDiagonalTailChunk001Sub000Block048Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block048Part005CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block048Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block048Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block048Part005CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block048Part005SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block048Part005] using hcert

def TailChunk001Sub000Block048Part006SupportExplicit : Finset ℕ :=
  ([18471] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block048Part006 : ℚ :=
  (93622069537 : ℚ) / 2046499151042611200

def SurrogateDiagonalTailChunk001Sub000Block048Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18471
    = surrogateDiagTailX0RatChunk001Sub000Block048Part006

theorem surrogateDiagonalTailChunk001Sub000Block048Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block048Part006CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block048Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block048Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block048Part006CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block048Part006SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block048Part006] using hcert

def TailChunk001Sub000Block048Part007SupportExplicit : Finset ℕ :=
  ([18474] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block048Part007 : ℚ :=
  (592324232525 : ℚ) / 1795524385851676224

def SurrogateDiagonalTailChunk001Sub000Block048Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18474
    = surrogateDiagTailX0RatChunk001Sub000Block048Part007

theorem surrogateDiagonalTailChunk001Sub000Block048Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block048Part007CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block048Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block048Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block048Part007CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block048Part007SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block048Part007] using hcert

def TailChunk001Sub000Block048Part008SupportExplicit : Finset ℕ :=
  ([18478] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block048Part008 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block048Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18478
    = surrogateDiagTailX0RatChunk001Sub000Block048Part008

theorem surrogateDiagonalTailChunk001Sub000Block048Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block048Part008CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block048Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block048Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block048Part008CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block048Part008SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block048Part008] using hcert

def TailChunk001Sub000Block048Part009SupportExplicit : Finset ℕ :=
  ([18479] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block048Part009 : ℚ :=
  (373265004025 : ℚ) / 227942911148189810688

def SurrogateDiagonalTailChunk001Sub000Block048Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18479
    = surrogateDiagTailX0RatChunk001Sub000Block048Part009

theorem surrogateDiagonalTailChunk001Sub000Block048Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block048Part009CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block048Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block048Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block048Part009CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block048Part009SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block048Part009] using hcert

def TailChunk001Sub000Block048Part010SupportExplicit : Finset ℕ :=
  ([18481] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block048Part010 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block048Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18481
    = surrogateDiagTailX0RatChunk001Sub000Block048Part010

theorem surrogateDiagonalTailChunk001Sub000Block048Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block048Part010CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block048Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block048Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block048Part010CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block048Part010SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block048Part010] using hcert

def TailChunk001Sub000Block048Part011SupportExplicit : Finset ℕ :=
  ([18482] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block048Part011 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block048Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18482
    = surrogateDiagTailX0RatChunk001Sub000Block048Part011

theorem surrogateDiagonalTailChunk001Sub000Block048Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block048Part011CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block048Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block048Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block048Part011CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block048Part011SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block048Part011] using hcert

def TailChunk001Sub000Block048Part012SupportExplicit : Finset ℕ :=
  ([18483] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block048Part012 : ℚ :=
  (1971053093 : ℚ) / 1037007360000000000

def SurrogateDiagonalTailChunk001Sub000Block048Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18483
    = surrogateDiagTailX0RatChunk001Sub000Block048Part012

theorem surrogateDiagonalTailChunk001Sub000Block048Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block048Part012CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block048Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block048Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block048Part012CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block048Part012SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block048Part012] using hcert

def TailChunk001Sub000Block048Part013SupportExplicit : Finset ℕ :=
  ([18485] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block048Part013 : ℚ :=
  (855026725375 : ℚ) / 119452343479113351168

def SurrogateDiagonalTailChunk001Sub000Block048Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18485
    = surrogateDiagTailX0RatChunk001Sub000Block048Part013

theorem surrogateDiagonalTailChunk001Sub000Block048Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block048Part013CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block048Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block048Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block048Part013CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block048Part013SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block048Part013] using hcert

def TailChunk001Sub000Block048Part014SupportExplicit : Finset ℕ :=
  ([18487] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block048Part014 : ℚ :=
  (547368167075 : ℚ) / 61689071098118513664

def SurrogateDiagonalTailChunk001Sub000Block048Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18487
    = surrogateDiagTailX0RatChunk001Sub000Block048Part014

theorem surrogateDiagonalTailChunk001Sub000Block048Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block048Part014CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block048Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block048Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block048Part014CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block048Part014SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block048Part014] using hcert

def TailChunk001Sub000Block048Part015SupportExplicit : Finset ℕ :=
  ([18489] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block048Part015 : ℚ :=
  (41675 : ℚ) / 3844638478452096

def SurrogateDiagonalTailChunk001Sub000Block048Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18489
    = surrogateDiagTailX0RatChunk001Sub000Block048Part015

theorem surrogateDiagonalTailChunk001Sub000Block048Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block048Part015CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block048Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block048Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block048Part015CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block048Part015SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block048Part015] using hcert

def TailChunk001Sub000Block048Part016SupportExplicit : Finset ℕ :=
  ([18493] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block048Part016 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block048Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18493
    = surrogateDiagTailX0RatChunk001Sub000Block048Part016

theorem surrogateDiagonalTailChunk001Sub000Block048Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block048Part016CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block048Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block048Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block048Part016CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block048Part016SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block048Part016] using hcert

def TailChunk001Sub000Block048Part017SupportExplicit : Finset ℕ :=
  ([18494] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block048Part017 : ℚ :=
  (17488522813 : ℚ) / 393538817721139200

def SurrogateDiagonalTailChunk001Sub000Block048Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18494
    = surrogateDiagTailX0RatChunk001Sub000Block048Part017

theorem surrogateDiagonalTailChunk001Sub000Block048Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block048Part017CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block048Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block048Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block048Part017CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block048Part017SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block048Part017] using hcert

def TailChunk001Sub000Block048Part018SupportExplicit : Finset ℕ :=
  ([18497] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block048Part018 : ℚ :=
  (20341439225 : ℚ) / 44689547659776933888

def SurrogateDiagonalTailChunk001Sub000Block048Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18497
    = surrogateDiagTailX0RatChunk001Sub000Block048Part018

theorem surrogateDiagonalTailChunk001Sub000Block048Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block048Part018CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block048Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block048Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block048Part018CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block048Part018SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block048Part018] using hcert

def TailChunk001Sub000Block048Part019SupportExplicit : Finset ℕ :=
  ([18498] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block048Part019 : ℚ :=
  (297147680225 : ℚ) / 1804876055594032704

def SurrogateDiagonalTailChunk001Sub000Block048Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18498
    = surrogateDiagTailX0RatChunk001Sub000Block048Part019

theorem surrogateDiagonalTailChunk001Sub000Block048Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block048Part019CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block048Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block048Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block048Part019CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block048Part019SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block048Part019] using hcert

def TailChunk001Sub000Block048Part020SupportExplicit : Finset ℕ :=
  ([18499] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block048Part020 : ℚ :=
  (95685602425 : ℚ) / 53001753422644081152

def SurrogateDiagonalTailChunk001Sub000Block048Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18499
    = surrogateDiagTailX0RatChunk001Sub000Block048Part020

theorem surrogateDiagonalTailChunk001Sub000Block048Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block048Part020CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block048Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block048Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block048Part020CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block048Part020SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block048Part020] using hcert

def TailChunk001Sub000Block048Part021SupportExplicit : Finset ℕ :=
  ([18501] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block048Part021 : ℚ :=
  (311759 : ℚ) / 16580377313280

def SurrogateDiagonalTailChunk001Sub000Block048Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18501
    = surrogateDiagTailX0RatChunk001Sub000Block048Part021

theorem surrogateDiagonalTailChunk001Sub000Block048Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block048Part021CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block048Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block048Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block048Part021CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block048Part021SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block048Part021] using hcert

def TailChunk001Sub000Block048Part022SupportExplicit : Finset ℕ :=
  ([18503] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block048Part022 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block048Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18503
    = surrogateDiagTailX0RatChunk001Sub000Block048Part022

theorem surrogateDiagonalTailChunk001Sub000Block048Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block048Part022CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block048Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block048Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block048Part022CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block048Part022SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block048Part022] using hcert

def TailChunk001Sub000Block048Part023SupportExplicit : Finset ℕ :=
  ([18505] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block048Part023 : ℚ :=
  (61756809 : ℚ) / 8646507622400000

def SurrogateDiagonalTailChunk001Sub000Block048Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18505
    = surrogateDiagTailX0RatChunk001Sub000Block048Part023

theorem surrogateDiagonalTailChunk001Sub000Block048Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block048Part023CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block048Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block048Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block048Part023CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block048Part023SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block048Part023] using hcert

def TailChunk001Sub000Block048Part024SupportExplicit : Finset ℕ :=
  ([18506] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block048Part024 : ℚ :=
  (4249400675 : ℚ) / 406779872239146528

def SurrogateDiagonalTailChunk001Sub000Block048Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18506
    = surrogateDiagTailX0RatChunk001Sub000Block048Part024

theorem surrogateDiagonalTailChunk001Sub000Block048Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block048Part024CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block048Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block048Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block048Part024CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block048Part024SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block048Part024] using hcert

def surrogateDiagonalTailChunk001Sub000Block048HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block048Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block048Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block048Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block048Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block048Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block048Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block048Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block048Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block048Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block048Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block048Head : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block048Part000
    + surrogateDiagTailX0RatChunk001Sub000Block048Part001
    + surrogateDiagTailX0RatChunk001Sub000Block048Part002
    + surrogateDiagTailX0RatChunk001Sub000Block048Part003
    + surrogateDiagTailX0RatChunk001Sub000Block048Part004
    + surrogateDiagTailX0RatChunk001Sub000Block048Part005
    + surrogateDiagTailX0RatChunk001Sub000Block048Part006
    + surrogateDiagTailX0RatChunk001Sub000Block048Part007
    + surrogateDiagTailX0RatChunk001Sub000Block048Part008
    + surrogateDiagTailX0RatChunk001Sub000Block048Part009

def surrogateDiagonalTailChunk001Sub000Block048MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block048Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block048Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block048Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block048Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block048Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block048Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block048Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block048Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block048Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block048Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block048Mid : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block048Part010
    + surrogateDiagTailX0RatChunk001Sub000Block048Part011
    + surrogateDiagTailX0RatChunk001Sub000Block048Part012
    + surrogateDiagTailX0RatChunk001Sub000Block048Part013
    + surrogateDiagTailX0RatChunk001Sub000Block048Part014
    + surrogateDiagTailX0RatChunk001Sub000Block048Part015
    + surrogateDiagTailX0RatChunk001Sub000Block048Part016
    + surrogateDiagTailX0RatChunk001Sub000Block048Part017
    + surrogateDiagTailX0RatChunk001Sub000Block048Part018
    + surrogateDiagTailX0RatChunk001Sub000Block048Part019

def surrogateDiagonalTailChunk001Sub000Block048TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block048Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block048Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block048Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block048Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block048Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block048Tail : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block048Part020
    + surrogateDiagTailX0RatChunk001Sub000Block048Part021
    + surrogateDiagTailX0RatChunk001Sub000Block048Part022
    + surrogateDiagTailX0RatChunk001Sub000Block048Part023
    + surrogateDiagTailX0RatChunk001Sub000Block048Part024

def surrogateDiagonalTailChunk001Sub000Block048Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk001Sub000Block048HeadSum X0
    + surrogateDiagonalTailChunk001Sub000Block048MidSum X0
    + surrogateDiagonalTailChunk001Sub000Block048TailSum X0

def surrogateDiagTailX0RatChunk001Sub000Block048 : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block048Part000
    + surrogateDiagTailX0RatChunk001Sub000Block048Part001
    + surrogateDiagTailX0RatChunk001Sub000Block048Part002
    + surrogateDiagTailX0RatChunk001Sub000Block048Part003
    + surrogateDiagTailX0RatChunk001Sub000Block048Part004
    + surrogateDiagTailX0RatChunk001Sub000Block048Part005
    + surrogateDiagTailX0RatChunk001Sub000Block048Part006
    + surrogateDiagTailX0RatChunk001Sub000Block048Part007
    + surrogateDiagTailX0RatChunk001Sub000Block048Part008
    + surrogateDiagTailX0RatChunk001Sub000Block048Part009
    + surrogateDiagTailX0RatChunk001Sub000Block048Part010
    + surrogateDiagTailX0RatChunk001Sub000Block048Part011
    + surrogateDiagTailX0RatChunk001Sub000Block048Part012
    + surrogateDiagTailX0RatChunk001Sub000Block048Part013
    + surrogateDiagTailX0RatChunk001Sub000Block048Part014
    + surrogateDiagTailX0RatChunk001Sub000Block048Part015
    + surrogateDiagTailX0RatChunk001Sub000Block048Part016
    + surrogateDiagTailX0RatChunk001Sub000Block048Part017
    + surrogateDiagTailX0RatChunk001Sub000Block048Part018
    + surrogateDiagTailX0RatChunk001Sub000Block048Part019
    + surrogateDiagTailX0RatChunk001Sub000Block048Part020
    + surrogateDiagTailX0RatChunk001Sub000Block048Part021
    + surrogateDiagTailX0RatChunk001Sub000Block048Part022
    + surrogateDiagTailX0RatChunk001Sub000Block048Part023
    + surrogateDiagTailX0RatChunk001Sub000Block048Part024

theorem surrogateDiagTailX0RatChunk001Sub000Block048_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk001Sub000Block048Head + surrogateDiagTailX0RatChunk001Sub000Block048Mid + surrogateDiagTailX0RatChunk001Sub000Block048Tail =
      surrogateDiagTailX0RatChunk001Sub000Block048 := by
  unfold surrogateDiagTailX0RatChunk001Sub000Block048Head surrogateDiagTailX0RatChunk001Sub000Block048Mid surrogateDiagTailX0RatChunk001Sub000Block048Tail surrogateDiagTailX0RatChunk001Sub000Block048
  ring

def SurrogateDiagonalTailChunk001Sub000Block048HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block048HeadSum X0 = surrogateDiagTailX0RatChunk001Sub000Block048Head

def SurrogateDiagonalTailChunk001Sub000Block048MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block048MidSum X0 = surrogateDiagTailX0RatChunk001Sub000Block048Mid

def SurrogateDiagonalTailChunk001Sub000Block048TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block048TailSum X0 = surrogateDiagTailX0RatChunk001Sub000Block048Tail

theorem surrogateDiagonalTailChunk001Sub000Block048_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk001Sub000Block048HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk001Sub000Block048MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk001Sub000Block048TailCertificateAt X0) :
    surrogateDiagonalTailChunk001Sub000Block048Sum X0 = surrogateDiagTailX0RatChunk001Sub000Block048 := by
  unfold SurrogateDiagonalTailChunk001Sub000Block048HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk001Sub000Block048MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk001Sub000Block048TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk001Sub000Block048Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk001Sub000Block048_eq_head_add_mid_add_tail

/-- Block 049 covers tail-support indices [11225,11250) and q from 18507 to 18546. -/

def TailChunk001Sub000Block049Part000SupportExplicit : Finset ℕ :=
  ([18507] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block049Part000 : ℚ :=
  (617156839 : ℚ) / 221365584968140800

def SurrogateDiagonalTailChunk001Sub000Block049Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18507
    = surrogateDiagTailX0RatChunk001Sub000Block049Part000

theorem surrogateDiagonalTailChunk001Sub000Block049Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block049Part000CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block049Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block049Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block049Part000CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block049Part000SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block049Part000] using hcert

def TailChunk001Sub000Block049Part001SupportExplicit : Finset ℕ :=
  ([18509] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block049Part001 : ℚ :=
  (93008304775 : ℚ) / 274595974442494489728

def SurrogateDiagonalTailChunk001Sub000Block049Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18509
    = surrogateDiagTailX0RatChunk001Sub000Block049Part001

theorem surrogateDiagonalTailChunk001Sub000Block049Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block049Part001CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block049Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block049Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block049Part001CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block049Part001SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block049Part001] using hcert

def TailChunk001Sub000Block049Part002SupportExplicit : Finset ℕ :=
  ([18510] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block049Part002 : ℚ :=
  (345178999475 : ℚ) / 737360144932798464

def SurrogateDiagonalTailChunk001Sub000Block049Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18510
    = surrogateDiagTailX0RatChunk001Sub000Block049Part002

theorem surrogateDiagonalTailChunk001Sub000Block049Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block049Part002CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block049Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block049Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block049Part002CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block049Part002SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block049Part002] using hcert

def TailChunk001Sub000Block049Part003SupportExplicit : Finset ℕ :=
  ([18511] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block049Part003 : ℚ :=
  (21658449775 : ℚ) / 69072331597177999872

def SurrogateDiagonalTailChunk001Sub000Block049Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18511
    = surrogateDiagTailX0RatChunk001Sub000Block049Part003

theorem surrogateDiagonalTailChunk001Sub000Block049Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block049Part003CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block049Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block049Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block049Part003CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block049Part003SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block049Part003] using hcert

def TailChunk001Sub000Block049Part004SupportExplicit : Finset ℕ :=
  ([18514] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block049Part004 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block049Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18514
    = surrogateDiagTailX0RatChunk001Sub000Block049Part004

theorem surrogateDiagonalTailChunk001Sub000Block049Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block049Part004CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block049Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block049Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block049Part004CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block049Part004SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block049Part004] using hcert

def TailChunk001Sub000Block049Part005SupportExplicit : Finset ℕ :=
  ([18517] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block049Part005 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block049Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18517
    = surrogateDiagTailX0RatChunk001Sub000Block049Part005

theorem surrogateDiagonalTailChunk001Sub000Block049Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block049Part005CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block049Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block049Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block049Part005CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block049Part005SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block049Part005] using hcert

def TailChunk001Sub000Block049Part006SupportExplicit : Finset ℕ :=
  ([18518] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block049Part006 : ℚ :=
  (74061884125 : ℚ) / 16522755299085600768

def SurrogateDiagonalTailChunk001Sub000Block049Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18518
    = surrogateDiagTailX0RatChunk001Sub000Block049Part006

theorem surrogateDiagonalTailChunk001Sub000Block049Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block049Part006CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block049Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block049Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block049Part006CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block049Part006SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block049Part006] using hcert

def TailChunk001Sub000Block049Part007SupportExplicit : Finset ℕ :=
  ([18519] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block049Part007 : ℚ :=
  (9524020382725 : ℚ) / 58056454647737960448

def SurrogateDiagonalTailChunk001Sub000Block049Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18519
    = surrogateDiagTailX0RatChunk001Sub000Block049Part007

theorem surrogateDiagonalTailChunk001Sub000Block049Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block049Part007CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block049Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block049Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block049Part007CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block049Part007SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block049Part007] using hcert

def TailChunk001Sub000Block049Part008SupportExplicit : Finset ℕ :=
  ([18521] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block049Part008 : ℚ :=
  (8575686025 : ℚ) / 117665942975058432

def SurrogateDiagonalTailChunk001Sub000Block049Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18521
    = surrogateDiagTailX0RatChunk001Sub000Block049Part008

theorem surrogateDiagonalTailChunk001Sub000Block049Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block049Part008CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block049Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block049Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block049Part008CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block049Part008SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block049Part008] using hcert

def TailChunk001Sub000Block049Part009SupportExplicit : Finset ℕ :=
  ([18523] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block049Part009 : ℚ :=
  (5360961390625 : ℚ) / 73572986768889183282

def SurrogateDiagonalTailChunk001Sub000Block049Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18523
    = surrogateDiagTailX0RatChunk001Sub000Block049Part009

theorem surrogateDiagonalTailChunk001Sub000Block049Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block049Part009CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block049Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block049Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block049Part009CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block049Part009SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block049Part009] using hcert

def TailChunk001Sub000Block049Part010SupportExplicit : Finset ℕ :=
  ([18526] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block049Part010 : ℚ :=
  (2591287265975 : ℚ) / 8379290186208175104

def SurrogateDiagonalTailChunk001Sub000Block049Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18526
    = surrogateDiagTailX0RatChunk001Sub000Block049Part010

theorem surrogateDiagonalTailChunk001Sub000Block049Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block049Part010CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block049Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block049Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block049Part010CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block049Part010SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block049Part010] using hcert

def TailChunk001Sub000Block049Part011SupportExplicit : Finset ℕ :=
  ([18527] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block049Part011 : ℚ :=
  (139210544893 : ℚ) / 1845163843072819200

def SurrogateDiagonalTailChunk001Sub000Block049Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18527
    = surrogateDiagTailX0RatChunk001Sub000Block049Part011

theorem surrogateDiagonalTailChunk001Sub000Block049Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block049Part011CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block049Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block049Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block049Part011CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block049Part011SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block049Part011] using hcert

def TailChunk001Sub000Block049Part012SupportExplicit : Finset ℕ :=
  ([18529] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block049Part012 : ℚ :=
  (16193463300025 : ℚ) / 158851463311087682688

def SurrogateDiagonalTailChunk001Sub000Block049Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18529
    = surrogateDiagTailX0RatChunk001Sub000Block049Part012

theorem surrogateDiagonalTailChunk001Sub000Block049Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block049Part012CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block049Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block049Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block049Part012CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block049Part012SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block049Part012] using hcert

def TailChunk001Sub000Block049Part013SupportExplicit : Finset ℕ :=
  ([18530] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block049Part013 : ℚ :=
  (3498320995375 : ℚ) / 5707445547741216768

def SurrogateDiagonalTailChunk001Sub000Block049Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18530
    = surrogateDiagTailX0RatChunk001Sub000Block049Part013

theorem surrogateDiagonalTailChunk001Sub000Block049Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block049Part013CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block049Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block049Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block049Part013CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block049Part013SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block049Part013] using hcert

def TailChunk001Sub000Block049Part014SupportExplicit : Finset ℕ :=
  ([18533] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block049Part014 : ℚ :=
  (820624659727 : ℚ) / 10640397050375299200

def SurrogateDiagonalTailChunk001Sub000Block049Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18533
    = surrogateDiagTailX0RatChunk001Sub000Block049Part014

theorem surrogateDiagonalTailChunk001Sub000Block049Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block049Part014CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block049Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block049Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block049Part014CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block049Part014SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block049Part014] using hcert

def TailChunk001Sub000Block049Part015SupportExplicit : Finset ℕ :=
  ([18534] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block049Part015 : ℚ :=
  (1490510823725 : ℚ) / 1818971994325254144

def SurrogateDiagonalTailChunk001Sub000Block049Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18534
    = surrogateDiagTailX0RatChunk001Sub000Block049Part015

theorem surrogateDiagonalTailChunk001Sub000Block049Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block049Part015CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block049Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block049Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block049Part015CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block049Part015SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block049Part015] using hcert

def TailChunk001Sub000Block049Part016SupportExplicit : Finset ℕ :=
  ([18535] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block049Part016 : ℚ :=
  (246238528889 : ℚ) / 1631751157422489600

def SurrogateDiagonalTailChunk001Sub000Block049Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18535
    = surrogateDiagTailX0RatChunk001Sub000Block049Part016

theorem surrogateDiagonalTailChunk001Sub000Block049Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block049Part016CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block049Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block049Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block049Part016CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block049Part016SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block049Part016] using hcert

def TailChunk001Sub000Block049Part017SupportExplicit : Finset ℕ :=
  ([18537] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block049Part017 : ℚ :=
  (1129955798075 : ℚ) / 6378215810863435776

def SurrogateDiagonalTailChunk001Sub000Block049Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18537
    = surrogateDiagTailX0RatChunk001Sub000Block049Part017

theorem surrogateDiagonalTailChunk001Sub000Block049Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block049Part017CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block049Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block049Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block049Part017CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block049Part017SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block049Part017] using hcert

def TailChunk001Sub000Block049Part018SupportExplicit : Finset ℕ :=
  ([18538] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block049Part018 : ℚ :=
  (17057136871 : ℚ) / 39353881772113920

def SurrogateDiagonalTailChunk001Sub000Block049Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18538
    = surrogateDiagTailX0RatChunk001Sub000Block049Part018

theorem surrogateDiagonalTailChunk001Sub000Block049Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block049Part018CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block049Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block049Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block049Part018CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block049Part018SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block049Part018] using hcert

def TailChunk001Sub000Block049Part019SupportExplicit : Finset ℕ :=
  ([18539] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block049Part019 : ℚ :=
  (5370226890625 : ℚ) / 73827536815235286642

def SurrogateDiagonalTailChunk001Sub000Block049Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18539
    = surrogateDiagTailX0RatChunk001Sub000Block049Part019

theorem surrogateDiagonalTailChunk001Sub000Block049Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block049Part019CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block049Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block049Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block049Part019CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block049Part019SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block049Part019] using hcert

def TailChunk001Sub000Block049Part020SupportExplicit : Finset ℕ :=
  ([18541] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block049Part020 : ℚ :=
  (8594217025 : ℚ) / 118175043121127712

def SurrogateDiagonalTailChunk001Sub000Block049Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18541
    = surrogateDiagTailX0RatChunk001Sub000Block049Part020

theorem surrogateDiagonalTailChunk001Sub000Block049Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block049Part020CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block049Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block049Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block049Part020CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block049Part020SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block049Part020] using hcert

def TailChunk001Sub000Block049Part021SupportExplicit : Finset ℕ :=
  ([18542] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block049Part021 : ℚ :=
  (5204347070875 : ℚ) / 16937098961948540928

def SurrogateDiagonalTailChunk001Sub000Block049Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18542
    = surrogateDiagTailX0RatChunk001Sub000Block049Part021

theorem surrogateDiagonalTailChunk001Sub000Block049Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block049Part021CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block049Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block049Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block049Part021CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block049Part021SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block049Part021] using hcert

def TailChunk001Sub000Block049Part022SupportExplicit : Finset ℕ :=
  ([18543] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block049Part022 : ℚ :=
  (7345219173925 : ℚ) / 31378066826881517568

def SurrogateDiagonalTailChunk001Sub000Block049Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18543
    = surrogateDiagTailX0RatChunk001Sub000Block049Part022

theorem surrogateDiagonalTailChunk001Sub000Block049Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block049Part022CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block049Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block049Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block049Part022CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block049Part022SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block049Part022] using hcert

def TailChunk001Sub000Block049Part023SupportExplicit : Finset ℕ :=
  ([18545] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block049Part023 : ℚ :=
  (14611218391975 : ℚ) / 121011244156034777088

def SurrogateDiagonalTailChunk001Sub000Block049Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18545
    = surrogateDiagTailX0RatChunk001Sub000Block049Part023

theorem surrogateDiagonalTailChunk001Sub000Block049Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block049Part023CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block049Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block049Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block049Part023CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block049Part023SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block049Part023] using hcert

def TailChunk001Sub000Block049Part024SupportExplicit : Finset ℕ :=
  ([18546] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block049Part024 : ℚ :=
  (10434127183 : ℚ) / 9836462899200000

def SurrogateDiagonalTailChunk001Sub000Block049Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18546
    = surrogateDiagTailX0RatChunk001Sub000Block049Part024

theorem surrogateDiagonalTailChunk001Sub000Block049Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block049Part024CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block049Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block049Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block049Part024CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block049Part024SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block049Part024] using hcert

def surrogateDiagonalTailChunk001Sub000Block049HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block049Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block049Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block049Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block049Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block049Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block049Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block049Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block049Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block049Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block049Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block049Head : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block049Part000
    + surrogateDiagTailX0RatChunk001Sub000Block049Part001
    + surrogateDiagTailX0RatChunk001Sub000Block049Part002
    + surrogateDiagTailX0RatChunk001Sub000Block049Part003
    + surrogateDiagTailX0RatChunk001Sub000Block049Part004
    + surrogateDiagTailX0RatChunk001Sub000Block049Part005
    + surrogateDiagTailX0RatChunk001Sub000Block049Part006
    + surrogateDiagTailX0RatChunk001Sub000Block049Part007
    + surrogateDiagTailX0RatChunk001Sub000Block049Part008
    + surrogateDiagTailX0RatChunk001Sub000Block049Part009

def surrogateDiagonalTailChunk001Sub000Block049MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block049Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block049Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block049Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block049Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block049Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block049Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block049Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block049Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block049Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block049Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block049Mid : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block049Part010
    + surrogateDiagTailX0RatChunk001Sub000Block049Part011
    + surrogateDiagTailX0RatChunk001Sub000Block049Part012
    + surrogateDiagTailX0RatChunk001Sub000Block049Part013
    + surrogateDiagTailX0RatChunk001Sub000Block049Part014
    + surrogateDiagTailX0RatChunk001Sub000Block049Part015
    + surrogateDiagTailX0RatChunk001Sub000Block049Part016
    + surrogateDiagTailX0RatChunk001Sub000Block049Part017
    + surrogateDiagTailX0RatChunk001Sub000Block049Part018
    + surrogateDiagTailX0RatChunk001Sub000Block049Part019

def surrogateDiagonalTailChunk001Sub000Block049TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block049Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block049Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block049Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block049Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block049Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block049Tail : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block049Part020
    + surrogateDiagTailX0RatChunk001Sub000Block049Part021
    + surrogateDiagTailX0RatChunk001Sub000Block049Part022
    + surrogateDiagTailX0RatChunk001Sub000Block049Part023
    + surrogateDiagTailX0RatChunk001Sub000Block049Part024

def surrogateDiagonalTailChunk001Sub000Block049Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk001Sub000Block049HeadSum X0
    + surrogateDiagonalTailChunk001Sub000Block049MidSum X0
    + surrogateDiagonalTailChunk001Sub000Block049TailSum X0

def surrogateDiagTailX0RatChunk001Sub000Block049 : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block049Part000
    + surrogateDiagTailX0RatChunk001Sub000Block049Part001
    + surrogateDiagTailX0RatChunk001Sub000Block049Part002
    + surrogateDiagTailX0RatChunk001Sub000Block049Part003
    + surrogateDiagTailX0RatChunk001Sub000Block049Part004
    + surrogateDiagTailX0RatChunk001Sub000Block049Part005
    + surrogateDiagTailX0RatChunk001Sub000Block049Part006
    + surrogateDiagTailX0RatChunk001Sub000Block049Part007
    + surrogateDiagTailX0RatChunk001Sub000Block049Part008
    + surrogateDiagTailX0RatChunk001Sub000Block049Part009
    + surrogateDiagTailX0RatChunk001Sub000Block049Part010
    + surrogateDiagTailX0RatChunk001Sub000Block049Part011
    + surrogateDiagTailX0RatChunk001Sub000Block049Part012
    + surrogateDiagTailX0RatChunk001Sub000Block049Part013
    + surrogateDiagTailX0RatChunk001Sub000Block049Part014
    + surrogateDiagTailX0RatChunk001Sub000Block049Part015
    + surrogateDiagTailX0RatChunk001Sub000Block049Part016
    + surrogateDiagTailX0RatChunk001Sub000Block049Part017
    + surrogateDiagTailX0RatChunk001Sub000Block049Part018
    + surrogateDiagTailX0RatChunk001Sub000Block049Part019
    + surrogateDiagTailX0RatChunk001Sub000Block049Part020
    + surrogateDiagTailX0RatChunk001Sub000Block049Part021
    + surrogateDiagTailX0RatChunk001Sub000Block049Part022
    + surrogateDiagTailX0RatChunk001Sub000Block049Part023
    + surrogateDiagTailX0RatChunk001Sub000Block049Part024

theorem surrogateDiagTailX0RatChunk001Sub000Block049_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk001Sub000Block049Head + surrogateDiagTailX0RatChunk001Sub000Block049Mid + surrogateDiagTailX0RatChunk001Sub000Block049Tail =
      surrogateDiagTailX0RatChunk001Sub000Block049 := by
  unfold surrogateDiagTailX0RatChunk001Sub000Block049Head surrogateDiagTailX0RatChunk001Sub000Block049Mid surrogateDiagTailX0RatChunk001Sub000Block049Tail surrogateDiagTailX0RatChunk001Sub000Block049
  ring

def SurrogateDiagonalTailChunk001Sub000Block049HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block049HeadSum X0 = surrogateDiagTailX0RatChunk001Sub000Block049Head

def SurrogateDiagonalTailChunk001Sub000Block049MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block049MidSum X0 = surrogateDiagTailX0RatChunk001Sub000Block049Mid

def SurrogateDiagonalTailChunk001Sub000Block049TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block049TailSum X0 = surrogateDiagTailX0RatChunk001Sub000Block049Tail

theorem surrogateDiagonalTailChunk001Sub000Block049_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk001Sub000Block049HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk001Sub000Block049MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk001Sub000Block049TailCertificateAt X0) :
    surrogateDiagonalTailChunk001Sub000Block049Sum X0 = surrogateDiagTailX0RatChunk001Sub000Block049 := by
  unfold SurrogateDiagonalTailChunk001Sub000Block049HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk001Sub000Block049MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk001Sub000Block049TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk001Sub000Block049Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk001Sub000Block049_eq_head_add_mid_add_tail

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

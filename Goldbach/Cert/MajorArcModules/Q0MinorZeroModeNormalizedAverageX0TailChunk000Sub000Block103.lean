import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0TailPilot25

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

open scoped BigOperators

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

/- Generated direct-term certificate blocks for tail chunk 000, subchunk 000, blocks [103,104). -/

/- Block 103 covers tail-support indices [2575,2600) and q from 4286 to 4322. -/

def TailChunk000Sub000Block103Part000SupportExplicit : Finset ℕ :=
  ([4286] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block103Part000 : ℚ :=
  (573941313775 : ℚ) / 52638647851685448

def SurrogateDiagonalTailChunk000Sub000Block103Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4286
    = surrogateDiagTailX0RatChunk000Sub000Block103Part000

theorem surrogateDiagonalTailChunk000Sub000Block103Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block103Part000CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block103Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block103Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block103Part000CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block103Part000SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block103Part000] using hcert

def TailChunk000Sub000Block103Part001SupportExplicit : Finset ℕ :=
  ([4287] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block103Part001 : ℚ :=
  (892920715525 : ℚ) / 166364121605326848

def SurrogateDiagonalTailChunk000Sub000Block103Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4287
    = surrogateDiagTailX0RatChunk000Sub000Block103Part001

theorem surrogateDiagonalTailChunk000Sub000Block103Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block103Part001CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block103Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block103Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block103Part001CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block103Part001SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block103Part001] using hcert

def TailChunk000Sub000Block103Part002SupportExplicit : Finset ℕ :=
  ([4289] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block103Part002 : ℚ :=
  (287430015625 : ℚ) / 211342078500667392

def SurrogateDiagonalTailChunk000Sub000Block103Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4289
    = surrogateDiagTailX0RatChunk000Sub000Block103Part002

theorem surrogateDiagonalTailChunk000Sub000Block103Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block103Part002CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block103Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block103Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block103Part002CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block103Part002SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block103Part002] using hcert

def TailChunk000Sub000Block103Part003SupportExplicit : Finset ℕ :=
  ([4290] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block103Part003 : ℚ :=
  (575196413 : ℚ) / 4247582146560

def SurrogateDiagonalTailChunk000Sub000Block103Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4290
    = surrogateDiagTailX0RatChunk000Sub000Block103Part003

theorem surrogateDiagonalTailChunk000Sub000Block103Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block103Part003CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block103Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block103Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block103Part003CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block103Part003SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block103Part003] using hcert

def TailChunk000Sub000Block103Part004SupportExplicit : Finset ℕ :=
  ([4291] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block103Part004 : ℚ :=
  (252163947625 : ℚ) / 113652124307845632

def SurrogateDiagonalTailChunk000Sub000Block103Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4291
    = surrogateDiagTailX0RatChunk000Sub000Block103Part004

theorem surrogateDiagonalTailChunk000Sub000Block103Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block103Part004CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block103Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block103Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block103Part004CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block103Part004SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block103Part004] using hcert

def TailChunk000Sub000Block103Part005SupportExplicit : Finset ℕ :=
  ([4294] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block103Part005 : ℚ :=
  (200167871725 : ℚ) / 10325925293064192

def SurrogateDiagonalTailChunk000Sub000Block103Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4294
    = surrogateDiagTailX0RatChunk000Sub000Block103Part005

theorem surrogateDiagonalTailChunk000Sub000Block103Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block103Part005CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block103Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block103Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block103Part005CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block103Part005SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block103Part005] using hcert

def TailChunk000Sub000Block103Part006SupportExplicit : Finset ℕ :=
  ([4295] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block103Part006 : ℚ :=
  (460819520375 : ℚ) / 173454663162553344

def SurrogateDiagonalTailChunk000Sub000Block103Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4295
    = surrogateDiagTailX0RatChunk000Sub000Block103Part006

theorem surrogateDiagonalTailChunk000Sub000Block103Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block103Part006CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block103Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block103Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block103Part006CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block103Part006SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block103Part006] using hcert

def TailChunk000Sub000Block103Part007SupportExplicit : Finset ℕ :=
  ([4297] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block103Part007 : ℚ :=
  (288503265625 : ℚ) / 212923677432402432

def SurrogateDiagonalTailChunk000Sub000Block103Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4297
    = surrogateDiagTailX0RatChunk000Sub000Block103Part007

theorem surrogateDiagonalTailChunk000Sub000Block103Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block103Part007CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block103Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block103Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block103Part007CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block103Part007SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block103Part007] using hcert

def TailChunk000Sub000Block103Part008SupportExplicit : Finset ℕ :=
  ([4298] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block103Part008 : ℚ :=
  (126314732125 : ℚ) / 7103257769240352

def SurrogateDiagonalTailChunk000Sub000Block103Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4298
    = surrogateDiagTailX0RatChunk000Sub000Block103Part008

theorem surrogateDiagonalTailChunk000Sub000Block103Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block103Part008CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block103Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block103Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block103Part008CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block103Part008SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block103Part008] using hcert

def TailChunk000Sub000Block103Part009SupportExplicit : Finset ℕ :=
  ([4299] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block103Part009 : ℚ :=
  (897926573425 : ℚ) / 168235992045355008

def SurrogateDiagonalTailChunk000Sub000Block103Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4299
    = surrogateDiagTailX0RatChunk000Sub000Block103Part009

theorem surrogateDiagonalTailChunk000Sub000Block103Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block103Part009CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block103Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block103Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block103Part009CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block103Part009SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block103Part009] using hcert

def TailChunk000Sub000Block103Part010SupportExplicit : Finset ℕ :=
  ([4301] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block103Part010 : ℚ :=
  (39163082929 : ℚ) / 15355271656243200

def SurrogateDiagonalTailChunk000Sub000Block103Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4301
    = surrogateDiagTailX0RatChunk000Sub000Block103Part010

theorem surrogateDiagonalTailChunk000Sub000Block103Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block103Part010CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block103Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block103Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block103Part010CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block103Part010SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block103Part010] using hcert

def TailChunk000Sub000Block103Part011SupportExplicit : Finset ℕ :=
  ([4303] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block103Part011 : ℚ :=
  (4797072919 : ℚ) / 2732908456396800

def SurrogateDiagonalTailChunk000Sub000Block103Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4303
    = surrogateDiagTailX0RatChunk000Sub000Block103Part011

theorem surrogateDiagonalTailChunk000Sub000Block103Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block103Part011CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block103Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block103Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block103Part011CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block103Part011SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block103Part011] using hcert

def TailChunk000Sub000Block103Part012SupportExplicit : Finset ℕ :=
  ([4305] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block103Part012 : ℚ :=
  (1218922309 : ℚ) / 75512571494400

def SurrogateDiagonalTailChunk000Sub000Block103Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4305
    = surrogateDiagTailX0RatChunk000Sub000Block103Part012

theorem surrogateDiagonalTailChunk000Sub000Block103Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block103Part012CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block103Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block103Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block103Part012CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block103Part012SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block103Part012] using hcert

def TailChunk000Sub000Block103Part013SupportExplicit : Finset ℕ :=
  ([4306] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block103Part013 : ℚ :=
  (579310239775 : ℚ) / 53628534209169408

def SurrogateDiagonalTailChunk000Sub000Block103Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4306
    = surrogateDiagTailX0RatChunk000Sub000Block103Part013

theorem surrogateDiagonalTailChunk000Sub000Block103Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block103Part013CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block103Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block103Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block103Part013CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block103Part013SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block103Part013] using hcert

def TailChunk000Sub000Block103Part014SupportExplicit : Finset ℕ :=
  ([4307] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block103Part014 : ℚ :=
  (282457089025 : ℚ) / 190111692190851072

def SurrogateDiagonalTailChunk000Sub000Block103Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4307
    = surrogateDiagTailX0RatChunk000Sub000Block103Part014

theorem surrogateDiagonalTailChunk000Sub000Block103Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block103Part014CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block103Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block103Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block103Part014CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block103Part014SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block103Part014] using hcert

def TailChunk000Sub000Block103Part015SupportExplicit : Finset ℕ :=
  ([4309] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block103Part015 : ℚ :=
  (561201317 : ℚ) / 367280801672040

def SurrogateDiagonalTailChunk000Sub000Block103Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4309
    = surrogateDiagTailX0RatChunk000Sub000Block103Part015

theorem surrogateDiagonalTailChunk000Sub000Block103Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block103Part015CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block103Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block103Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block103Part015CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block103Part015SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block103Part015] using hcert

def TailChunk000Sub000Block103Part016SupportExplicit : Finset ℕ :=
  ([4310] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block103Part016 : ℚ :=
  (253411911 : ℚ) / 11671841314816

def SurrogateDiagonalTailChunk000Sub000Block103Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4310
    = surrogateDiagTailX0RatChunk000Sub000Block103Part016

theorem surrogateDiagonalTailChunk000Sub000Block103Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block103Part016CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block103Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block103Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block103Part016CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block103Part016SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block103Part016] using hcert

def TailChunk000Sub000Block103Part017SupportExplicit : Finset ℕ :=
  ([4313] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block103Part017 : ℚ :=
  (712755156475 : ℚ) / 228259773070528896

def SurrogateDiagonalTailChunk000Sub000Block103Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4313
    = surrogateDiagTailX0RatChunk000Sub000Block103Part017

theorem surrogateDiagonalTailChunk000Sub000Block103Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block103Part017CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block103Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block103Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block103Part017CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block103Part017SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block103Part017] using hcert

def TailChunk000Sub000Block103Part018SupportExplicit : Finset ℕ :=
  ([4314] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block103Part018 : ℚ :=
  (516225506575 : ℚ) / 10632725902996608

def SurrogateDiagonalTailChunk000Sub000Block103Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4314
    = surrogateDiagTailX0RatChunk000Sub000Block103Part018

theorem surrogateDiagonalTailChunk000Sub000Block103Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block103Part018CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block103Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block103Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block103Part018CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block103Part018SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block103Part018] using hcert

def TailChunk000Sub000Block103Part019SupportExplicit : Finset ℕ :=
  ([4315] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block103Part019 : ℚ :=
  (836641880375 : ℚ) / 176711938820219904

def SurrogateDiagonalTailChunk000Sub000Block103Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4315
    = surrogateDiagTailX0RatChunk000Sub000Block103Part019

theorem surrogateDiagonalTailChunk000Sub000Block103Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block103Part019CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block103Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block103Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block103Part019CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block103Part019SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block103Part019] using hcert

def TailChunk000Sub000Block103Part020SupportExplicit : Finset ℕ :=
  ([4317] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block103Part020 : ℚ :=
  (77606625 : ℚ) / 17103915233344

def SurrogateDiagonalTailChunk000Sub000Block103Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4317
    = surrogateDiagTailX0RatChunk000Sub000Block103Part020

theorem surrogateDiagonalTailChunk000Sub000Block103Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block103Part020CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block103Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block103Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block103Part020CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block103Part020SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block103Part020] using hcert

def TailChunk000Sub000Block103Part021SupportExplicit : Finset ℕ :=
  ([4318] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block103Part021 : ℚ :=
  (549814074025 : ℚ) / 41303701172256768

def SurrogateDiagonalTailChunk000Sub000Block103Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4318
    = surrogateDiagTailX0RatChunk000Sub000Block103Part021

theorem surrogateDiagonalTailChunk000Sub000Block103Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block103Part021CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block103Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block103Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block103Part021CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block103Part021SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block103Part021] using hcert

def TailChunk000Sub000Block103Part022SupportExplicit : Finset ℕ :=
  ([4319] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block103Part022 : ℚ :=
  (255464842375 : ℚ) / 116652679178821632

def SurrogateDiagonalTailChunk000Sub000Block103Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4319
    = surrogateDiagTailX0RatChunk000Sub000Block103Part022

theorem surrogateDiagonalTailChunk000Sub000Block103Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block103Part022CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block103Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block103Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block103Part022CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block103Part022SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block103Part022] using hcert

def TailChunk000Sub000Block103Part023SupportExplicit : Finset ℕ :=
  ([4321] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block103Part023 : ℚ :=
  (187895080425 : ℚ) / 122900767624183808

def SurrogateDiagonalTailChunk000Sub000Block103Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4321
    = surrogateDiagTailX0RatChunk000Sub000Block103Part023

theorem surrogateDiagonalTailChunk000Sub000Block103Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block103Part023CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block103Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block103Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block103Part023CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block103Part023SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block103Part023] using hcert

def TailChunk000Sub000Block103Part024SupportExplicit : Finset ℕ :=
  ([4322] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block103Part024 : ℚ :=
  (23344935079 : ℚ) / 2177217692467200

def SurrogateDiagonalTailChunk000Sub000Block103Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4322
    = surrogateDiagTailX0RatChunk000Sub000Block103Part024

theorem surrogateDiagonalTailChunk000Sub000Block103Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block103Part024CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block103Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block103Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block103Part024CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block103Part024SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block103Part024] using hcert

def surrogateDiagonalTailChunk000Sub000Block103HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block103Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block103Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block103Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block103Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block103Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block103Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block103Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block103Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block103Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block103Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block103Head : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block103Part000
    + surrogateDiagTailX0RatChunk000Sub000Block103Part001
    + surrogateDiagTailX0RatChunk000Sub000Block103Part002
    + surrogateDiagTailX0RatChunk000Sub000Block103Part003
    + surrogateDiagTailX0RatChunk000Sub000Block103Part004
    + surrogateDiagTailX0RatChunk000Sub000Block103Part005
    + surrogateDiagTailX0RatChunk000Sub000Block103Part006
    + surrogateDiagTailX0RatChunk000Sub000Block103Part007
    + surrogateDiagTailX0RatChunk000Sub000Block103Part008
    + surrogateDiagTailX0RatChunk000Sub000Block103Part009

def surrogateDiagonalTailChunk000Sub000Block103MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block103Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block103Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block103Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block103Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block103Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block103Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block103Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block103Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block103Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block103Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block103Mid : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block103Part010
    + surrogateDiagTailX0RatChunk000Sub000Block103Part011
    + surrogateDiagTailX0RatChunk000Sub000Block103Part012
    + surrogateDiagTailX0RatChunk000Sub000Block103Part013
    + surrogateDiagTailX0RatChunk000Sub000Block103Part014
    + surrogateDiagTailX0RatChunk000Sub000Block103Part015
    + surrogateDiagTailX0RatChunk000Sub000Block103Part016
    + surrogateDiagTailX0RatChunk000Sub000Block103Part017
    + surrogateDiagTailX0RatChunk000Sub000Block103Part018
    + surrogateDiagTailX0RatChunk000Sub000Block103Part019

def surrogateDiagonalTailChunk000Sub000Block103TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block103Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block103Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block103Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block103Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block103Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block103Tail : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block103Part020
    + surrogateDiagTailX0RatChunk000Sub000Block103Part021
    + surrogateDiagTailX0RatChunk000Sub000Block103Part022
    + surrogateDiagTailX0RatChunk000Sub000Block103Part023
    + surrogateDiagTailX0RatChunk000Sub000Block103Part024

def surrogateDiagonalTailChunk000Sub000Block103Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub000Block103HeadSum X0
    + surrogateDiagonalTailChunk000Sub000Block103MidSum X0
    + surrogateDiagonalTailChunk000Sub000Block103TailSum X0

def surrogateDiagTailX0RatChunk000Sub000Block103 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block103Part000
    + surrogateDiagTailX0RatChunk000Sub000Block103Part001
    + surrogateDiagTailX0RatChunk000Sub000Block103Part002
    + surrogateDiagTailX0RatChunk000Sub000Block103Part003
    + surrogateDiagTailX0RatChunk000Sub000Block103Part004
    + surrogateDiagTailX0RatChunk000Sub000Block103Part005
    + surrogateDiagTailX0RatChunk000Sub000Block103Part006
    + surrogateDiagTailX0RatChunk000Sub000Block103Part007
    + surrogateDiagTailX0RatChunk000Sub000Block103Part008
    + surrogateDiagTailX0RatChunk000Sub000Block103Part009
    + surrogateDiagTailX0RatChunk000Sub000Block103Part010
    + surrogateDiagTailX0RatChunk000Sub000Block103Part011
    + surrogateDiagTailX0RatChunk000Sub000Block103Part012
    + surrogateDiagTailX0RatChunk000Sub000Block103Part013
    + surrogateDiagTailX0RatChunk000Sub000Block103Part014
    + surrogateDiagTailX0RatChunk000Sub000Block103Part015
    + surrogateDiagTailX0RatChunk000Sub000Block103Part016
    + surrogateDiagTailX0RatChunk000Sub000Block103Part017
    + surrogateDiagTailX0RatChunk000Sub000Block103Part018
    + surrogateDiagTailX0RatChunk000Sub000Block103Part019
    + surrogateDiagTailX0RatChunk000Sub000Block103Part020
    + surrogateDiagTailX0RatChunk000Sub000Block103Part021
    + surrogateDiagTailX0RatChunk000Sub000Block103Part022
    + surrogateDiagTailX0RatChunk000Sub000Block103Part023
    + surrogateDiagTailX0RatChunk000Sub000Block103Part024

theorem surrogateDiagTailX0RatChunk000Sub000Block103_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk000Sub000Block103Head + surrogateDiagTailX0RatChunk000Sub000Block103Mid + surrogateDiagTailX0RatChunk000Sub000Block103Tail =
      surrogateDiagTailX0RatChunk000Sub000Block103 := by
  unfold surrogateDiagTailX0RatChunk000Sub000Block103Head surrogateDiagTailX0RatChunk000Sub000Block103Mid surrogateDiagTailX0RatChunk000Sub000Block103Tail surrogateDiagTailX0RatChunk000Sub000Block103
  ring

def SurrogateDiagonalTailChunk000Sub000Block103HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block103HeadSum X0 = surrogateDiagTailX0RatChunk000Sub000Block103Head

def SurrogateDiagonalTailChunk000Sub000Block103MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block103MidSum X0 = surrogateDiagTailX0RatChunk000Sub000Block103Mid

def SurrogateDiagonalTailChunk000Sub000Block103TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block103TailSum X0 = surrogateDiagTailX0RatChunk000Sub000Block103Tail

theorem surrogateDiagonalTailChunk000Sub000Block103_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk000Sub000Block103HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk000Sub000Block103MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk000Sub000Block103TailCertificateAt X0) :
    surrogateDiagonalTailChunk000Sub000Block103Sum X0 = surrogateDiagTailX0RatChunk000Sub000Block103 := by
  unfold SurrogateDiagonalTailChunk000Sub000Block103HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk000Sub000Block103MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk000Sub000Block103TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk000Sub000Block103Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk000Sub000Block103_eq_head_add_mid_add_tail

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

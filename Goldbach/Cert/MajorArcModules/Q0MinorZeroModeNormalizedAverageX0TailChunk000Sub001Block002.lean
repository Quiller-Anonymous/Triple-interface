import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0TailPilot25

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

open scoped BigOperators

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

/- Generated direct-term certificate blocks for tail chunk 000, subchunk 001, blocks [2,3). -/

/-- Block 002 covers tail-support indices [5050,5075) and q from 8354 to 8393. -/

def TailChunk000Sub001Block002Part000SupportExplicit : Finset ℕ :=
  ([8354] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block002Part000 : ℚ :=
  (272614515625 : ℚ) / 190111692190851072

def SurrogateDiagonalTailChunk000Sub001Block002Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8354
    = surrogateDiagTailX0RatChunk000Sub001Block002Part000

theorem surrogateDiagonalTailChunk000Sub001Block002Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block002Part000CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block002Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block002Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block002Part000CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block002Part000SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block002Part000] using hcert

def TailChunk000Sub001Block002Part001SupportExplicit : Finset ℕ :=
  ([8355] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block002Part001 : ℚ :=
  (899804765825 : ℚ) / 489390999087611904

def SurrogateDiagonalTailChunk000Sub001Block002Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8355
    = surrogateDiagTailX0RatChunk000Sub001Block002Part001

theorem surrogateDiagonalTailChunk000Sub001Block002Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block002Part001CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block002Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block002Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block002Part001CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block002Part001SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block002Part001] using hcert

def TailChunk000Sub001Block002Part002SupportExplicit : Finset ℕ :=
  ([8357] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block002Part002 : ℚ :=
  (33779643857 : ℚ) / 88690577115709440

def SurrogateDiagonalTailChunk000Sub001Block002Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8357
    = surrogateDiagTailX0RatChunk000Sub001Block002Part002

theorem surrogateDiagonalTailChunk000Sub001Block002Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block002Part002CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block002Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block002Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block002Part002CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block002Part002SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block002Part002] using hcert

def TailChunk000Sub001Block002Part003SupportExplicit : Finset ℕ :=
  ([8358] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block002Part003 : ℚ :=
  (3657732325 : ℚ) / 402482881760256

def SurrogateDiagonalTailChunk000Sub001Block002Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8358
    = surrogateDiagTailX0RatChunk000Sub001Block002Part003

theorem surrogateDiagonalTailChunk000Sub001Block002Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block002Part003CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block002Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block002Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block002Part003CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block002Part003SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block002Part003] using hcert

def TailChunk000Sub001Block002Part004SupportExplicit : Finset ℕ :=
  ([8359] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block002Part004 : ℚ :=
  (1947095819675 : ℚ) / 4404148555844772864

def SurrogateDiagonalTailChunk000Sub001Block002Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8359
    = surrogateDiagTailX0RatChunk000Sub001Block002Part004

theorem surrogateDiagonalTailChunk000Sub001Block002Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block002Part004CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block002Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block002Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block002Part004CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block002Part004SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block002Part004] using hcert

def TailChunk000Sub001Block002Part005SupportExplicit : Finset ℕ :=
  ([8362] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block002Part005 : ℚ :=
  (1061917638025 : ℚ) / 660859218756108288

def SurrogateDiagonalTailChunk000Sub001Block002Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8362
    = surrogateDiagTailX0RatChunk000Sub001Block002Part005

theorem surrogateDiagonalTailChunk000Sub001Block002Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block002Part005CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block002Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block002Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block002Part005CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block002Part005SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block002Part005] using hcert

def TailChunk000Sub001Block002Part006SupportExplicit : Finset ℕ :=
  ([8363] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block002Part006 : ℚ :=
  (1092808890625 : ℚ) / 3056381205401488242

def SurrogateDiagonalTailChunk000Sub001Block002Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8363
    = surrogateDiagTailX0RatChunk000Sub001Block002Part006

theorem surrogateDiagonalTailChunk000Sub001Block002Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block002Part006CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block002Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block002Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block002Part006CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block002Part006SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block002Part006] using hcert

def TailChunk000Sub001Block002Part007SupportExplicit : Finset ℕ :=
  ([8365] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block002Part007 : ℚ :=
  (2521402699525 : ℚ) / 2661825945685229568

def SurrogateDiagonalTailChunk000Sub001Block002Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8365
    = surrogateDiagTailX0RatChunk000Sub001Block002Part007

theorem surrogateDiagonalTailChunk000Sub001Block002Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block002Part007CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block002Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block002Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block002Part007CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block002Part007SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block002Part007] using hcert

def TailChunk000Sub001Block002Part008SupportExplicit : Finset ℕ :=
  ([8366] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block002Part008 : ℚ :=
  (1065640291825 : ℚ) / 671411652430430208

def SurrogateDiagonalTailChunk000Sub001Block002Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8366
    = surrogateDiagTailX0RatChunk000Sub001Block002Part008

theorem surrogateDiagonalTailChunk000Sub001Block002Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block002Part008CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block002Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block002Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block002Part008CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block002Part008SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block002Part008] using hcert

def TailChunk000Sub001Block002Part009SupportExplicit : Finset ℕ :=
  ([8367] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block002Part009 : ℚ :=
  (1215029257475 : ℚ) / 1208614843176428544

def SurrogateDiagonalTailChunk000Sub001Block002Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8367
    = surrogateDiagTailX0RatChunk000Sub001Block002Part009

theorem surrogateDiagonalTailChunk000Sub001Block002Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block002Part009CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block002Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block002Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block002Part009CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block002Part009SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block002Part009] using hcert

def TailChunk000Sub001Block002Part010SupportExplicit : Finset ℕ :=
  ([8369] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block002Part010 : ℚ :=
  (1094377515625 : ℚ) / 3065162852915945472

def SurrogateDiagonalTailChunk000Sub001Block002Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8369
    = surrogateDiagTailX0RatChunk000Sub001Block002Part010

theorem surrogateDiagonalTailChunk000Sub001Block002Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block002Part010CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block002Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block002Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block002Part010CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block002Part010SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block002Part010] using hcert

def TailChunk000Sub001Block002Part011SupportExplicit : Finset ℕ :=
  ([8371] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block002Part011 : ℚ :=
  (5058932589 : ℚ) / 11122949478400000

def SurrogateDiagonalTailChunk000Sub001Block002Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8371
    = surrogateDiagTailX0RatChunk000Sub001Block002Part011

theorem surrogateDiagonalTailChunk000Sub001Block002Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block002Part011CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block002Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block002Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block002Part011CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block002Part011SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block002Part011] using hcert

def TailChunk000Sub001Block002Part012SupportExplicit : Finset ℕ :=
  ([8373] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block002Part012 : ℚ :=
  (77865988837 : ℚ) / 96966930004099200

def SurrogateDiagonalTailChunk000Sub001Block002Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8373
    = surrogateDiagTailX0RatChunk000Sub001Block002Part012

theorem surrogateDiagonalTailChunk000Sub001Block002Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block002Part012CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block002Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block002Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block002Part012CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block002Part012SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block002Part012] using hcert

def TailChunk000Sub001Block002Part013SupportExplicit : Finset ℕ :=
  ([8374] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block002Part013 : ℚ :=
  (534082677425 : ℚ) / 338367504582042624

def SurrogateDiagonalTailChunk000Sub001Block002Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8374
    = surrogateDiagTailX0RatChunk000Sub001Block002Part013

theorem surrogateDiagonalTailChunk000Sub001Block002Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block002Part013CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block002Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block002Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block002Part013CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block002Part013SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block002Part013] using hcert

def TailChunk000Sub001Block002Part014SupportExplicit : Finset ℕ :=
  ([8377] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block002Part014 : ℚ :=
  (1096470765625 : ℚ) / 3076901136679260672

def SurrogateDiagonalTailChunk000Sub001Block002Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8377
    = surrogateDiagTailX0RatChunk000Sub001Block002Part014

theorem surrogateDiagonalTailChunk000Sub001Block002Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block002Part014CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block002Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block002Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block002Part014CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block002Part014SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block002Part014] using hcert

def TailChunk000Sub001Block002Part015SupportExplicit : Finset ℕ :=
  ([8378] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block002Part015 : ℚ :=
  (2037192669 : ℚ) / 1294111479875200

def SurrogateDiagonalTailChunk000Sub001Block002Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8378
    = surrogateDiagTailX0RatChunk000Sub001Block002Part015

theorem surrogateDiagonalTailChunk000Sub001Block002Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block002Part015CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block002Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block002Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block002Part015CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block002Part015SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block002Part015] using hcert

def TailChunk000Sub001Block002Part016SupportExplicit : Finset ℕ :=
  ([8382] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block002Part016 : ℚ :=
  (7713679669 : ℚ) / 1008391141900800

def SurrogateDiagonalTailChunk000Sub001Block002Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8382
    = surrogateDiagTailX0RatChunk000Sub001Block002Part016

theorem surrogateDiagonalTailChunk000Sub001Block002Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block002Part016CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block002Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block002Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block002Part016CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block002Part016SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block002Part016] using hcert

def TailChunk000Sub001Block002Part017SupportExplicit : Finset ℕ :=
  ([8383] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block002Part017 : ℚ :=
  (28392910191 : ℚ) / 75368697392000000

def SurrogateDiagonalTailChunk000Sub001Block002Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8383
    = surrogateDiagTailX0RatChunk000Sub001Block002Part017

theorem surrogateDiagonalTailChunk000Sub001Block002Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block002Part017CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block002Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block002Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block002Part017CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block002Part017SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block002Part017] using hcert

def TailChunk000Sub001Block002Part018SupportExplicit : Finset ℕ :=
  ([8385] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block002Part018 : ℚ :=
  (796910850275 : ℚ) / 330429609378054144

def SurrogateDiagonalTailChunk000Sub001Block002Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8385
    = surrogateDiagTailX0RatChunk000Sub001Block002Part018

theorem surrogateDiagonalTailChunk000Sub001Block002Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block002Part018CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block002Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block002Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block002Part018CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block002Part018SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block002Part018] using hcert

def TailChunk000Sub001Block002Part019SupportExplicit : Finset ℕ :=
  ([8386] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block002Part019 : ℚ :=
  (985461893725 : ℚ) / 414416078086128768

def SurrogateDiagonalTailChunk000Sub001Block002Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8386
    = surrogateDiagTailX0RatChunk000Sub001Block002Part019

theorem surrogateDiagonalTailChunk000Sub001Block002Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block002Part019CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block002Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block002Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block002Part019CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block002Part019SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block002Part019] using hcert

def TailChunk000Sub001Block002Part020SupportExplicit : Finset ℕ :=
  ([8387] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block002Part020 : ℚ :=
  (1099090140625 : ℚ) / 3091621364632810002

def SurrogateDiagonalTailChunk000Sub001Block002Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8387
    = surrogateDiagTailX0RatChunk000Sub001Block002Part020

theorem surrogateDiagonalTailChunk000Sub001Block002Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block002Part020CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block002Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block002Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block002Part020CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block002Part020SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block002Part020] using hcert

def TailChunk000Sub001Block002Part021SupportExplicit : Finset ℕ :=
  ([8389] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block002Part021 : ℚ :=
  (1099614390625 : ℚ) / 3094571736714184992

def SurrogateDiagonalTailChunk000Sub001Block002Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8389
    = surrogateDiagTailX0RatChunk000Sub001Block002Part021

theorem surrogateDiagonalTailChunk000Sub001Block002Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block002Part021CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block002Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block002Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block002Part021CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block002Part021SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block002Part021] using hcert

def TailChunk000Sub001Block002Part022SupportExplicit : Finset ℕ :=
  ([8390] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block002Part022 : ℚ :=
  (307706881125 : ℚ) / 105225656504129536

def SurrogateDiagonalTailChunk000Sub001Block002Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8390
    = surrogateDiagTailX0RatChunk000Sub001Block002Part022

theorem surrogateDiagonalTailChunk000Sub001Block002Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block002Part022CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block002Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block002Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block002Part022CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block002Part022SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block002Part022] using hcert

def TailChunk000Sub001Block002Part023SupportExplicit : Finset ℕ :=
  ([8391] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block002Part023 : ℚ :=
  (1222010374175 : ℚ) / 1222546858948813824

def SurrogateDiagonalTailChunk000Sub001Block002Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8391
    = surrogateDiagTailX0RatChunk000Sub001Block002Part023

theorem surrogateDiagonalTailChunk000Sub001Block002Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block002Part023CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block002Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block002Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block002Part023CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block002Part023SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block002Part023] using hcert

def TailChunk000Sub001Block002Part024SupportExplicit : Finset ℕ :=
  ([8393] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block002Part024 : ℚ :=
  (60404058983 : ℚ) / 88177316544921600

def SurrogateDiagonalTailChunk000Sub001Block002Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8393
    = surrogateDiagTailX0RatChunk000Sub001Block002Part024

theorem surrogateDiagonalTailChunk000Sub001Block002Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block002Part024CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block002Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block002Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block002Part024CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block002Part024SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block002Part024] using hcert

def surrogateDiagonalTailChunk000Sub001Block002HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block002Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block002Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block002Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block002Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block002Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block002Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block002Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block002Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block002Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block002Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block002Head : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block002Part000
    + surrogateDiagTailX0RatChunk000Sub001Block002Part001
    + surrogateDiagTailX0RatChunk000Sub001Block002Part002
    + surrogateDiagTailX0RatChunk000Sub001Block002Part003
    + surrogateDiagTailX0RatChunk000Sub001Block002Part004
    + surrogateDiagTailX0RatChunk000Sub001Block002Part005
    + surrogateDiagTailX0RatChunk000Sub001Block002Part006
    + surrogateDiagTailX0RatChunk000Sub001Block002Part007
    + surrogateDiagTailX0RatChunk000Sub001Block002Part008
    + surrogateDiagTailX0RatChunk000Sub001Block002Part009

def surrogateDiagonalTailChunk000Sub001Block002MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block002Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block002Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block002Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block002Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block002Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block002Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block002Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block002Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block002Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block002Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block002Mid : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block002Part010
    + surrogateDiagTailX0RatChunk000Sub001Block002Part011
    + surrogateDiagTailX0RatChunk000Sub001Block002Part012
    + surrogateDiagTailX0RatChunk000Sub001Block002Part013
    + surrogateDiagTailX0RatChunk000Sub001Block002Part014
    + surrogateDiagTailX0RatChunk000Sub001Block002Part015
    + surrogateDiagTailX0RatChunk000Sub001Block002Part016
    + surrogateDiagTailX0RatChunk000Sub001Block002Part017
    + surrogateDiagTailX0RatChunk000Sub001Block002Part018
    + surrogateDiagTailX0RatChunk000Sub001Block002Part019

def surrogateDiagonalTailChunk000Sub001Block002TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block002Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block002Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block002Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block002Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block002Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block002Tail : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block002Part020
    + surrogateDiagTailX0RatChunk000Sub001Block002Part021
    + surrogateDiagTailX0RatChunk000Sub001Block002Part022
    + surrogateDiagTailX0RatChunk000Sub001Block002Part023
    + surrogateDiagTailX0RatChunk000Sub001Block002Part024

def surrogateDiagonalTailChunk000Sub001Block002Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub001Block002HeadSum X0
    + surrogateDiagonalTailChunk000Sub001Block002MidSum X0
    + surrogateDiagonalTailChunk000Sub001Block002TailSum X0

def surrogateDiagTailX0RatChunk000Sub001Block002 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block002Part000
    + surrogateDiagTailX0RatChunk000Sub001Block002Part001
    + surrogateDiagTailX0RatChunk000Sub001Block002Part002
    + surrogateDiagTailX0RatChunk000Sub001Block002Part003
    + surrogateDiagTailX0RatChunk000Sub001Block002Part004
    + surrogateDiagTailX0RatChunk000Sub001Block002Part005
    + surrogateDiagTailX0RatChunk000Sub001Block002Part006
    + surrogateDiagTailX0RatChunk000Sub001Block002Part007
    + surrogateDiagTailX0RatChunk000Sub001Block002Part008
    + surrogateDiagTailX0RatChunk000Sub001Block002Part009
    + surrogateDiagTailX0RatChunk000Sub001Block002Part010
    + surrogateDiagTailX0RatChunk000Sub001Block002Part011
    + surrogateDiagTailX0RatChunk000Sub001Block002Part012
    + surrogateDiagTailX0RatChunk000Sub001Block002Part013
    + surrogateDiagTailX0RatChunk000Sub001Block002Part014
    + surrogateDiagTailX0RatChunk000Sub001Block002Part015
    + surrogateDiagTailX0RatChunk000Sub001Block002Part016
    + surrogateDiagTailX0RatChunk000Sub001Block002Part017
    + surrogateDiagTailX0RatChunk000Sub001Block002Part018
    + surrogateDiagTailX0RatChunk000Sub001Block002Part019
    + surrogateDiagTailX0RatChunk000Sub001Block002Part020
    + surrogateDiagTailX0RatChunk000Sub001Block002Part021
    + surrogateDiagTailX0RatChunk000Sub001Block002Part022
    + surrogateDiagTailX0RatChunk000Sub001Block002Part023
    + surrogateDiagTailX0RatChunk000Sub001Block002Part024

theorem surrogateDiagTailX0RatChunk000Sub001Block002_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk000Sub001Block002Head + surrogateDiagTailX0RatChunk000Sub001Block002Mid + surrogateDiagTailX0RatChunk000Sub001Block002Tail =
      surrogateDiagTailX0RatChunk000Sub001Block002 := by
  unfold surrogateDiagTailX0RatChunk000Sub001Block002Head surrogateDiagTailX0RatChunk000Sub001Block002Mid surrogateDiagTailX0RatChunk000Sub001Block002Tail surrogateDiagTailX0RatChunk000Sub001Block002
  ring

def SurrogateDiagonalTailChunk000Sub001Block002HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block002HeadSum X0 = surrogateDiagTailX0RatChunk000Sub001Block002Head

def SurrogateDiagonalTailChunk000Sub001Block002MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block002MidSum X0 = surrogateDiagTailX0RatChunk000Sub001Block002Mid

def SurrogateDiagonalTailChunk000Sub001Block002TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block002TailSum X0 = surrogateDiagTailX0RatChunk000Sub001Block002Tail

theorem surrogateDiagonalTailChunk000Sub001Block002_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk000Sub001Block002HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk000Sub001Block002MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk000Sub001Block002TailCertificateAt X0) :
    surrogateDiagonalTailChunk000Sub001Block002Sum X0 = surrogateDiagTailX0RatChunk000Sub001Block002 := by
  unfold SurrogateDiagonalTailChunk000Sub001Block002HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk000Sub001Block002MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk000Sub001Block002TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk000Sub001Block002Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk000Sub001Block002_eq_head_add_mid_add_tail

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

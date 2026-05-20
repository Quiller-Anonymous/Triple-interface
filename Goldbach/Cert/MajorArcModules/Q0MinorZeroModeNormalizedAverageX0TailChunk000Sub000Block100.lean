import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0TailPilot25

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

open scoped BigOperators

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

/- Generated direct-term certificate blocks for tail chunk 000, subchunk 000, blocks [100,101). -/

/- Block 100 covers tail-support indices [2500,2525) and q from 4162 to 4201. -/

def TailChunk000Sub000Block100Part000SupportExplicit : Finset ℕ :=
  ([4162] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block100Part000 : ℚ :=
  (21648474439 : ℚ) / 1872148050739200

def SurrogateDiagonalTailChunk000Sub000Block100Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4162
    = surrogateDiagTailX0RatChunk000Sub000Block100Part000

theorem surrogateDiagonalTailChunk000Sub000Block100Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block100Part000CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block100Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block100Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block100Part000CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block100Part000SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block100Part000] using hcert

def TailChunk000Sub000Block100Part001SupportExplicit : Finset ℕ :=
  ([4163] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block100Part001 : ℚ :=
  (20836092419 : ℚ) / 12298088053785600

def SurrogateDiagonalTailChunk000Sub000Block100Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4163
    = surrogateDiagTailX0RatChunk000Sub000Block100Part001

theorem surrogateDiagonalTailChunk000Sub000Block100Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block100Part001CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block100Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block100Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block100Part001CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block100Part001SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block100Part001] using hcert

def TailChunk000Sub000Block100Part002SupportExplicit : Finset ℕ :=
  ([4166] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block100Part002 : ℚ :=
  (542252652775 : ℚ) / 46983975306518088

def SurrogateDiagonalTailChunk000Sub000Block100Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4166
    = surrogateDiagTailX0RatChunk000Sub000Block100Part002

theorem surrogateDiagonalTailChunk000Sub000Block100Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block100Part002CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block100Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block100Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block100Part002CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block100Part002SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block100Part002] using hcert

def TailChunk000Sub000Block100Part003SupportExplicit : Finset ℕ :=
  ([4169] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block100Part003 : ℚ :=
  (15101038571 : ℚ) / 4083984124698240

def SurrogateDiagonalTailChunk000Sub000Block100Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4169
    = surrogateDiagTailX0RatChunk000Sub000Block100Part003

theorem surrogateDiagonalTailChunk000Sub000Block100Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block100Part003CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block100Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block100Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block100Part003CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block100Part003SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block100Part003] using hcert

def TailChunk000Sub000Block100Part004SupportExplicit : Finset ℕ :=
  ([4170] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block100Part004 : ℚ :=
  (373888892725 : ℚ) / 3714523860860928

def SurrogateDiagonalTailChunk000Sub000Block100Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4170
    = surrogateDiagTailX0RatChunk000Sub000Block100Part004

theorem surrogateDiagonalTailChunk000Sub000Block100Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block100Part004CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block100Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block100Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block100Part004CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block100Part004SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block100Part004] using hcert

def TailChunk000Sub000Block100Part005SupportExplicit : Finset ℕ :=
  ([4171] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block100Part005 : ℚ :=
  (2074190158975 : ℚ) / 660859218756108288

def SurrogateDiagonalTailChunk000Sub000Block100Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4171
    = surrogateDiagTailX0RatChunk000Sub000Block100Part005

theorem surrogateDiagonalTailChunk000Sub000Block100Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block100Part005CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block100Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block100Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block100Part005CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block100Part005SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block100Part005] using hcert

def TailChunk000Sub000Block100Part006SupportExplicit : Finset ℕ :=
  ([4173] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block100Part006 : ℚ :=
  (22467903125 : ℚ) / 2181996498917376

def SurrogateDiagonalTailChunk000Sub000Block100Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4173
    = surrogateDiagTailX0RatChunk000Sub000Block100Part006

theorem surrogateDiagonalTailChunk000Sub000Block100Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block100Part006CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block100Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block100Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block100Part006CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block100Part006SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block100Part006] using hcert

def TailChunk000Sub000Block100Part007SupportExplicit : Finset ℕ :=
  ([4174] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block100Part007 : ℚ :=
  (544337235775 : ℚ) / 47346085195614408

def SurrogateDiagonalTailChunk000Sub000Block100Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4174
    = surrogateDiagTailX0RatChunk000Sub000Block100Part007

theorem surrogateDiagonalTailChunk000Sub000Block100Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block100Part007CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block100Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block100Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block100Part007CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block100Part007SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block100Part007] using hcert

def TailChunk000Sub000Block100Part008SupportExplicit : Finset ℕ :=
  ([4177] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block100Part008 : ℚ :=
  (272614515625 : ℚ) / 190111692190851072

def SurrogateDiagonalTailChunk000Sub000Block100Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4177
    = surrogateDiagTailX0RatChunk000Sub000Block100Part008

theorem surrogateDiagonalTailChunk000Sub000Block100Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block100Part008CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block100Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block100Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block100Part008CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block100Part008SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block100Part008] using hcert

def TailChunk000Sub000Block100Part009SupportExplicit : Finset ℕ :=
  ([4178] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block100Part009 : ℚ :=
  (545381026975 : ℚ) / 47527923047712768

def SurrogateDiagonalTailChunk000Sub000Block100Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4178
    = surrogateDiagTailX0RatChunk000Sub000Block100Part009

theorem surrogateDiagonalTailChunk000Sub000Block100Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block100Part009CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block100Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block100Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block100Part009CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block100Part009SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block100Part009] using hcert

def TailChunk000Sub000Block100Part010SupportExplicit : Finset ℕ :=
  ([4179] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block100Part010 : ℚ :=
  (3657732325 : ℚ) / 402482881760256

def SurrogateDiagonalTailChunk000Sub000Block100Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4179
    = surrogateDiagTailX0RatChunk000Sub000Block100Part010

theorem surrogateDiagonalTailChunk000Sub000Block100Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block100Part010CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block100Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block100Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block100Part010CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block100Part010SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block100Part010] using hcert

def TailChunk000Sub000Block100Part011SupportExplicit : Finset ℕ :=
  ([4181] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block100Part011 : ℚ :=
  (1061917638025 : ℚ) / 660859218756108288

def SurrogateDiagonalTailChunk000Sub000Block100Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4181
    = surrogateDiagTailX0RatChunk000Sub000Block100Part011

theorem surrogateDiagonalTailChunk000Sub000Block100Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block100Part011CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block100Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block100Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block100Part011CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block100Part011SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block100Part011] using hcert

def TailChunk000Sub000Block100Part012SupportExplicit : Finset ℕ :=
  ([4182] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block100Part012 : ℚ :=
  (243694953 : ℚ) / 4474819051520

def SurrogateDiagonalTailChunk000Sub000Block100Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4182
    = surrogateDiagTailX0RatChunk000Sub000Block100Part012

theorem surrogateDiagonalTailChunk000Sub000Block100Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block100Part012CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block100Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block100Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block100Part012CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block100Part012SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block100Part012] using hcert

def TailChunk000Sub000Block100Part013SupportExplicit : Finset ℕ :=
  ([4183] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block100Part013 : ℚ :=
  (1065640291825 : ℚ) / 671411652430430208

def SurrogateDiagonalTailChunk000Sub000Block100Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4183
    = surrogateDiagTailX0RatChunk000Sub000Block100Part013

theorem surrogateDiagonalTailChunk000Sub000Block100Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block100Part013CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block100Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block100Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block100Part013CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block100Part013SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block100Part013] using hcert

def TailChunk000Sub000Block100Part014SupportExplicit : Finset ℕ :=
  ([4186] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block100Part014 : ℚ :=
  (146061876475 : ℚ) / 3935388177211392

def SurrogateDiagonalTailChunk000Sub000Block100Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4186
    = surrogateDiagTailX0RatChunk000Sub000Block100Part014

theorem surrogateDiagonalTailChunk000Sub000Block100Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block100Part014CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block100Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block100Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block100Part014CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block100Part014SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block100Part014] using hcert

def TailChunk000Sub000Block100Part015SupportExplicit : Finset ℕ :=
  ([4187] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block100Part015 : ℚ :=
  (534082677425 : ℚ) / 338367504582042624

def SurrogateDiagonalTailChunk000Sub000Block100Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4187
    = surrogateDiagTailX0RatChunk000Sub000Block100Part015

theorem surrogateDiagonalTailChunk000Sub000Block100Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block100Part015CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block100Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block100Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block100Part015CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block100Part015SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block100Part015] using hcert

def TailChunk000Sub000Block100Part016SupportExplicit : Finset ℕ :=
  ([4189] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block100Part016 : ℚ :=
  (2037192669 : ℚ) / 1294111479875200

def SurrogateDiagonalTailChunk000Sub000Block100Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4189
    = surrogateDiagTailX0RatChunk000Sub000Block100Part016

theorem surrogateDiagonalTailChunk000Sub000Block100Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block100Part016CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block100Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block100Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block100Part016CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block100Part016SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block100Part016] using hcert

def TailChunk000Sub000Block100Part017SupportExplicit : Finset ℕ :=
  ([4190] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block100Part017 : ℚ :=
  (623806802725 : ℚ) / 19542132397590528

def SurrogateDiagonalTailChunk000Sub000Block100Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4190
    = surrogateDiagTailX0RatChunk000Sub000Block100Part017

theorem surrogateDiagonalTailChunk000Sub000Block100Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block100Part017CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block100Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block100Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block100Part017CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block100Part017SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block100Part017] using hcert

def TailChunk000Sub000Block100Part018SupportExplicit : Finset ℕ :=
  ([4191] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block100Part018 : ℚ :=
  (7713679669 : ℚ) / 1008391141900800

def SurrogateDiagonalTailChunk000Sub000Block100Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4191
    = surrogateDiagTailX0RatChunk000Sub000Block100Part018

theorem surrogateDiagonalTailChunk000Sub000Block100Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block100Part018CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block100Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block100Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block100Part018CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block100Part018SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block100Part018] using hcert

def TailChunk000Sub000Block100Part019SupportExplicit : Finset ℕ :=
  ([4193] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block100Part019 : ℚ :=
  (985461893725 : ℚ) / 414416078086128768

def SurrogateDiagonalTailChunk000Sub000Block100Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4193
    = surrogateDiagTailX0RatChunk000Sub000Block100Part019

theorem surrogateDiagonalTailChunk000Sub000Block100Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block100Part019CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block100Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block100Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block100Part019CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block100Part019SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block100Part019] using hcert

def TailChunk000Sub000Block100Part020SupportExplicit : Finset ℕ :=
  ([4195] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block100Part020 : ℚ :=
  (307706881125 : ℚ) / 105225656504129536

def SurrogateDiagonalTailChunk000Sub000Block100Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4195
    = surrogateDiagTailX0RatChunk000Sub000Block100Part020

theorem surrogateDiagonalTailChunk000Sub000Block100Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block100Part020CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block100Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block100Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block100Part020CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block100Part020SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block100Part020] using hcert

def TailChunk000Sub000Block100Part021SupportExplicit : Finset ℕ :=
  ([4197] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block100Part021 : ℚ :=
  (24450875 : ℚ) / 5092926660288

def SurrogateDiagonalTailChunk000Sub000Block100Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4197
    = surrogateDiagTailX0RatChunk000Sub000Block100Part021

theorem surrogateDiagonalTailChunk000Sub000Block100Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block100Part021CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block100Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block100Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block100Part021CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block100Part021SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block100Part021] using hcert

def TailChunk000Sub000Block100Part022SupportExplicit : Finset ℕ :=
  ([4198] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block100Part022 : ℚ :=
  (550614979975 : ℚ) / 48444981490926408

def SurrogateDiagonalTailChunk000Sub000Block100Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4198
    = surrogateDiagTailX0RatChunk000Sub000Block100Part022

theorem surrogateDiagonalTailChunk000Sub000Block100Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block100Part022CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block100Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block100Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block100Part022CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block100Part022SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block100Part022] using hcert

def TailChunk000Sub000Block100Part023SupportExplicit : Finset ℕ :=
  ([4199] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block100Part023 : ℚ :=
  (157096911325 : ℚ) / 59452557788971008

def SurrogateDiagonalTailChunk000Sub000Block100Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4199
    = surrogateDiagTailX0RatChunk000Sub000Block100Part023

theorem surrogateDiagonalTailChunk000Sub000Block100Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block100Part023CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block100Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block100Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block100Part023CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block100Part023SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block100Part023] using hcert

def TailChunk000Sub000Block100Part024SupportExplicit : Finset ℕ :=
  ([4201] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block100Part024 : ℚ :=
  (17648401 : ℚ) / 12449273356800

def SurrogateDiagonalTailChunk000Sub000Block100Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4201
    = surrogateDiagTailX0RatChunk000Sub000Block100Part024

theorem surrogateDiagonalTailChunk000Sub000Block100Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block100Part024CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block100Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block100Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block100Part024CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block100Part024SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block100Part024] using hcert

def surrogateDiagonalTailChunk000Sub000Block100HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block100Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block100Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block100Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block100Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block100Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block100Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block100Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block100Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block100Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block100Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block100Head : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block100Part000
    + surrogateDiagTailX0RatChunk000Sub000Block100Part001
    + surrogateDiagTailX0RatChunk000Sub000Block100Part002
    + surrogateDiagTailX0RatChunk000Sub000Block100Part003
    + surrogateDiagTailX0RatChunk000Sub000Block100Part004
    + surrogateDiagTailX0RatChunk000Sub000Block100Part005
    + surrogateDiagTailX0RatChunk000Sub000Block100Part006
    + surrogateDiagTailX0RatChunk000Sub000Block100Part007
    + surrogateDiagTailX0RatChunk000Sub000Block100Part008
    + surrogateDiagTailX0RatChunk000Sub000Block100Part009

def surrogateDiagonalTailChunk000Sub000Block100MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block100Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block100Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block100Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block100Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block100Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block100Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block100Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block100Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block100Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block100Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block100Mid : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block100Part010
    + surrogateDiagTailX0RatChunk000Sub000Block100Part011
    + surrogateDiagTailX0RatChunk000Sub000Block100Part012
    + surrogateDiagTailX0RatChunk000Sub000Block100Part013
    + surrogateDiagTailX0RatChunk000Sub000Block100Part014
    + surrogateDiagTailX0RatChunk000Sub000Block100Part015
    + surrogateDiagTailX0RatChunk000Sub000Block100Part016
    + surrogateDiagTailX0RatChunk000Sub000Block100Part017
    + surrogateDiagTailX0RatChunk000Sub000Block100Part018
    + surrogateDiagTailX0RatChunk000Sub000Block100Part019

def surrogateDiagonalTailChunk000Sub000Block100TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block100Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block100Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block100Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block100Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block100Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block100Tail : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block100Part020
    + surrogateDiagTailX0RatChunk000Sub000Block100Part021
    + surrogateDiagTailX0RatChunk000Sub000Block100Part022
    + surrogateDiagTailX0RatChunk000Sub000Block100Part023
    + surrogateDiagTailX0RatChunk000Sub000Block100Part024

def surrogateDiagonalTailChunk000Sub000Block100Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub000Block100HeadSum X0
    + surrogateDiagonalTailChunk000Sub000Block100MidSum X0
    + surrogateDiagonalTailChunk000Sub000Block100TailSum X0

def surrogateDiagTailX0RatChunk000Sub000Block100 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block100Part000
    + surrogateDiagTailX0RatChunk000Sub000Block100Part001
    + surrogateDiagTailX0RatChunk000Sub000Block100Part002
    + surrogateDiagTailX0RatChunk000Sub000Block100Part003
    + surrogateDiagTailX0RatChunk000Sub000Block100Part004
    + surrogateDiagTailX0RatChunk000Sub000Block100Part005
    + surrogateDiagTailX0RatChunk000Sub000Block100Part006
    + surrogateDiagTailX0RatChunk000Sub000Block100Part007
    + surrogateDiagTailX0RatChunk000Sub000Block100Part008
    + surrogateDiagTailX0RatChunk000Sub000Block100Part009
    + surrogateDiagTailX0RatChunk000Sub000Block100Part010
    + surrogateDiagTailX0RatChunk000Sub000Block100Part011
    + surrogateDiagTailX0RatChunk000Sub000Block100Part012
    + surrogateDiagTailX0RatChunk000Sub000Block100Part013
    + surrogateDiagTailX0RatChunk000Sub000Block100Part014
    + surrogateDiagTailX0RatChunk000Sub000Block100Part015
    + surrogateDiagTailX0RatChunk000Sub000Block100Part016
    + surrogateDiagTailX0RatChunk000Sub000Block100Part017
    + surrogateDiagTailX0RatChunk000Sub000Block100Part018
    + surrogateDiagTailX0RatChunk000Sub000Block100Part019
    + surrogateDiagTailX0RatChunk000Sub000Block100Part020
    + surrogateDiagTailX0RatChunk000Sub000Block100Part021
    + surrogateDiagTailX0RatChunk000Sub000Block100Part022
    + surrogateDiagTailX0RatChunk000Sub000Block100Part023
    + surrogateDiagTailX0RatChunk000Sub000Block100Part024

theorem surrogateDiagTailX0RatChunk000Sub000Block100_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk000Sub000Block100Head + surrogateDiagTailX0RatChunk000Sub000Block100Mid + surrogateDiagTailX0RatChunk000Sub000Block100Tail =
      surrogateDiagTailX0RatChunk000Sub000Block100 := by
  unfold surrogateDiagTailX0RatChunk000Sub000Block100Head surrogateDiagTailX0RatChunk000Sub000Block100Mid surrogateDiagTailX0RatChunk000Sub000Block100Tail surrogateDiagTailX0RatChunk000Sub000Block100
  ring

def SurrogateDiagonalTailChunk000Sub000Block100HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block100HeadSum X0 = surrogateDiagTailX0RatChunk000Sub000Block100Head

def SurrogateDiagonalTailChunk000Sub000Block100MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block100MidSum X0 = surrogateDiagTailX0RatChunk000Sub000Block100Mid

def SurrogateDiagonalTailChunk000Sub000Block100TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block100TailSum X0 = surrogateDiagTailX0RatChunk000Sub000Block100Tail

theorem surrogateDiagonalTailChunk000Sub000Block100_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk000Sub000Block100HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk000Sub000Block100MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk000Sub000Block100TailCertificateAt X0) :
    surrogateDiagonalTailChunk000Sub000Block100Sum X0 = surrogateDiagTailX0RatChunk000Sub000Block100 := by
  unfold SurrogateDiagonalTailChunk000Sub000Block100HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk000Sub000Block100MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk000Sub000Block100TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk000Sub000Block100Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk000Sub000Block100_eq_head_add_mid_add_tail

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

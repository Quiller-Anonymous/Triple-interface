import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0TailPilot25

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

open scoped BigOperators

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

/- Generated direct-term certificate blocks for tail chunk 000, subchunk 000, blocks [55,56). -/

/- Block 055 covers tail-support indices [1375,1400) and q from 2314 to 2353. -/

def TailChunk000Sub000Block055Part000SupportExplicit : Finset ℕ :=
  ([2314] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block055Part000 : ℚ :=
  (308209297525 : ℚ) / 3109442510389248

def SurrogateDiagonalTailChunk000Sub000Block055Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2314
    = surrogateDiagTailX0RatChunk000Sub000Block055Part000

theorem surrogateDiagonalTailChunk000Sub000Block055Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block055Part000CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block055Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block055Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block055Part000CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block055Part000SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block055Part000] using hcert

def TailChunk000Sub000Block055Part001SupportExplicit : Finset ℕ :=
  ([2315] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block055Part001 : ℚ :=
  (62367372625 : ℚ) / 2430264149558784

def SurrogateDiagonalTailChunk000Sub000Block055Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2315
    = surrogateDiagTailX0RatChunk000Sub000Block055Part001

theorem surrogateDiagonalTailChunk000Sub000Block055Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block055Part001CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block055Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block055Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block055Part001CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block055Part001SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block055Part001] using hcert

def TailChunk000Sub000Block055Part002SupportExplicit : Finset ℕ :=
  ([2317] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block055Part002 : ℚ :=
  (23220604411 : ℚ) / 1537261006723200

def SurrogateDiagonalTailChunk000Sub000Block055Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2317
    = surrogateDiagTailX0RatChunk000Sub000Block055Part002

theorem surrogateDiagonalTailChunk000Sub000Block055Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block055Part002CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block055Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block055Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block055Part002CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block055Part002SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block055Part002] using hcert

def TailChunk000Sub000Block055Part003SupportExplicit : Finset ℕ :=
  ([2318] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block055Part003 : ℚ :=
  (6294945983 : ℚ) / 68038052889600

def SurrogateDiagonalTailChunk000Sub000Block055Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2318
    = surrogateDiagTailX0RatChunk000Sub000Block055Part003

theorem surrogateDiagonalTailChunk000Sub000Block055Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block055Part003CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block055Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block055Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block055Part003CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block055Part003SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block055Part003] using hcert

def TailChunk000Sub000Block055Part004SupportExplicit : Finset ℕ :=
  ([2319] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block055Part004 : ℚ :=
  (242475407825 : ℚ) / 7105359352833024

def SurrogateDiagonalTailChunk000Sub000Block055Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2319
    = surrogateDiagTailX0RatChunk000Sub000Block055Part004

theorem surrogateDiagonalTailChunk000Sub000Block055Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block055Part004CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block055Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block055Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block055Part004CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block055Part004SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block055Part004] using hcert

def TailChunk000Sub000Block055Part005SupportExplicit : Finset ℕ :=
  ([2321] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block055Part005 : ℚ :=
  (195276899 : ℚ) / 15438087000000

def SurrogateDiagonalTailChunk000Sub000Block055Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2321
    = surrogateDiagTailX0RatChunk000Sub000Block055Part005

theorem surrogateDiagonalTailChunk000Sub000Block055Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block055Part005CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block055Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block055Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block055Part005CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block055Part005SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block055Part005] using hcert

def TailChunk000Sub000Block055Part006SupportExplicit : Finset ℕ :=
  ([2323] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block055Part006 : ℚ :=
  (116713849 : ℚ) / 10650129600000

def SurrogateDiagonalTailChunk000Sub000Block055Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2323
    = surrogateDiagTailX0RatChunk000Sub000Block055Part006

theorem surrogateDiagonalTailChunk000Sub000Block055Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block055Part006CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block055Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block055Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block055Part006CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block055Part006SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block055Part006] using hcert

def TailChunk000Sub000Block055Part007SupportExplicit : Finset ℕ :=
  ([2326] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block055Part007 : ℚ :=
  (211169835125 : ℚ) / 2279404364134884

def SurrogateDiagonalTailChunk000Sub000Block055Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2326
    = surrogateDiagTailX0RatChunk000Sub000Block055Part007

theorem surrogateDiagonalTailChunk000Sub000Block055Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block055Part007CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block055Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block055Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block055Part007CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block055Part007SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block055Part007] using hcert

def TailChunk000Sub000Block055Part008SupportExplicit : Finset ℕ :=
  ([2327] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block055Part008 : ℚ :=
  (302944220675 : ℚ) / 17350444186638336

def SurrogateDiagonalTailChunk000Sub000Block055Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2327
    = surrogateDiagTailX0RatChunk000Sub000Block055Part008

theorem surrogateDiagonalTailChunk000Sub000Block055Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block055Part008CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block055Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block055Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block055Part008CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block055Part008SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block055Part008] using hcert

def TailChunk000Sub000Block055Part009SupportExplicit : Finset ℕ :=
  ([2329] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block055Part009 : ℚ :=
  (390576825 : ℚ) / 34351228125184

def SurrogateDiagonalTailChunk000Sub000Block055Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2329
    = surrogateDiagTailX0RatChunk000Sub000Block055Part009

theorem surrogateDiagonalTailChunk000Sub000Block055Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block055Part009CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block055Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block055Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block055Part009CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block055Part009SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block055Part009] using hcert

def TailChunk000Sub000Block055Part010SupportExplicit : Finset ℕ :=
  ([2330] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block055Part010 : ℚ :=
  (277146532525 : ℚ) / 1854465523580928

def SurrogateDiagonalTailChunk000Sub000Block055Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2330
    = surrogateDiagTailX0RatChunk000Sub000Block055Part010

theorem surrogateDiagonalTailChunk000Sub000Block055Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block055Part010CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block055Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block055Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block055Part010CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block055Part010SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block055Part010] using hcert

def TailChunk000Sub000Block055Part011SupportExplicit : Finset ℕ :=
  ([2333] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block055Part011 : ℚ :=
  (680225052775 : ℚ) / 73950487825577088

def SurrogateDiagonalTailChunk000Sub000Block055Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2333
    = surrogateDiagTailX0RatChunk000Sub000Block055Part011

theorem surrogateDiagonalTailChunk000Sub000Block055Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block055Part011CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block055Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block055Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block055Part011CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block055Part011SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block055Part011] using hcert

def TailChunk000Sub000Block055Part012SupportExplicit : Finset ℕ :=
  ([2334] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block055Part012 : ℚ :=
  (58973460175 : ℚ) / 226680286351872

def SurrogateDiagonalTailChunk000Sub000Block055Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2334
    = surrogateDiagTailX0RatChunk000Sub000Block055Part012

theorem surrogateDiagonalTailChunk000Sub000Block055Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block055Part012CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block055Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block055Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block055Part012CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block055Part012SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block055Part012] using hcert

def TailChunk000Sub000Block055Part013SupportExplicit : Finset ℕ :=
  ([2335] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block055Part013 : ℚ :=
  (185939818875 : ℚ) / 10062114065422336

def SurrogateDiagonalTailChunk000Sub000Block055Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2335
    = surrogateDiagTailX0RatChunk000Sub000Block055Part013

theorem surrogateDiagonalTailChunk000Sub000Block055Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block055Part013CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block055Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block055Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block055Part013CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block055Part013SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block055Part013] using hcert

def TailChunk000Sub000Block055Part014SupportExplicit : Finset ℕ :=
  ([2337] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block055Part014 : ℚ :=
  (11040067043 : ℚ) / 215033846169600

def SurrogateDiagonalTailChunk000Sub000Block055Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2337
    = surrogateDiagTailX0RatChunk000Sub000Block055Part014

theorem surrogateDiagonalTailChunk000Sub000Block055Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block055Part014CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block055Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block055Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block055Part014CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block055Part014SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block055Part014] using hcert

def TailChunk000Sub000Block055Part015SupportExplicit : Finset ℕ :=
  ([2338] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block055Part015 : ℚ :=
  (292982373625 : ℚ) / 2460731408512128

def SurrogateDiagonalTailChunk000Sub000Block055Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2338
    = surrogateDiagTailX0RatChunk000Sub000Block055Part015

theorem surrogateDiagonalTailChunk000Sub000Block055Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block055Part015CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block055Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block055Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block055Part015CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block055Part015SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block055Part015] using hcert

def TailChunk000Sub000Block055Part016SupportExplicit : Finset ℕ :=
  ([2339] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block055Part016 : ℚ :=
  (683728351975 : ℚ) / 74714498580573768

def SurrogateDiagonalTailChunk000Sub000Block055Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2339
    = surrogateDiagTailX0RatChunk000Sub000Block055Part016

theorem surrogateDiagonalTailChunk000Sub000Block055Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block055Part016CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block055Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block055Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block055Part016CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block055Part016SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block055Part016] using hcert

def TailChunk000Sub000Block055Part017SupportExplicit : Finset ℕ :=
  ([2341] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block055Part017 : ℚ :=
  (27395924719 : ℚ) / 2998819179907200

def SurrogateDiagonalTailChunk000Sub000Block055Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2341
    = surrogateDiagTailX0RatChunk000Sub000Block055Part017

theorem surrogateDiagonalTailChunk000Sub000Block055Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block055Part017CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block055Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block055Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block055Part017CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block055Part017SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block055Part017] using hcert

def TailChunk000Sub000Block055Part018SupportExplicit : Finset ℕ :=
  ([2342] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block055Part018 : ℚ :=
  (1712680009 : ℚ) / 18742619874420

def SurrogateDiagonalTailChunk000Sub000Block055Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2342
    = surrogateDiagTailX0RatChunk000Sub000Block055Part018

theorem surrogateDiagonalTailChunk000Sub000Block055Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block055Part018CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block055Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block055Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block055Part018CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block055Part018SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block055Part018] using hcert

def TailChunk000Sub000Block055Part019SupportExplicit : Finset ℕ :=
  ([2343] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block055Part019 : ℚ :=
  (393004971 : ℚ) / 9148496000000

def SurrogateDiagonalTailChunk000Sub000Block055Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2343
    = surrogateDiagTailX0RatChunk000Sub000Block055Part019

theorem surrogateDiagonalTailChunk000Sub000Block055Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block055Part019CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block055Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block055Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block055Part019CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block055Part019SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block055Part019] using hcert

def TailChunk000Sub000Block055Part020SupportExplicit : Finset ℕ :=
  ([2345] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block055Part020 : ℚ :=
  (78386309525 : ℚ) / 2623592118140928

def SurrogateDiagonalTailChunk000Sub000Block055Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2345
    = surrogateDiagTailX0RatChunk000Sub000Block055Part020

theorem surrogateDiagonalTailChunk000Sub000Block055Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block055Part020CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block055Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block055Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block055Part020CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block055Part020SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block055Part020] using hcert

def TailChunk000Sub000Block055Part021SupportExplicit : Finset ℕ :=
  ([2346] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block055Part021 : ℚ :=
  (215554284775 : ℚ) / 614210866249728

def SurrogateDiagonalTailChunk000Sub000Block055Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2346
    = surrogateDiagTailX0RatChunk000Sub000Block055Part021

theorem surrogateDiagonalTailChunk000Sub000Block055Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block055Part021CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block055Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block055Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block055Part021CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block055Part021SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block055Part021] using hcert

def TailChunk000Sub000Block055Part022SupportExplicit : Finset ℕ :=
  ([2347] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block055Part022 : ℚ :=
  (688413414775 : ℚ) / 75742369966544328

def SurrogateDiagonalTailChunk000Sub000Block055Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2347
    = surrogateDiagTailX0RatChunk000Sub000Block055Part022

theorem surrogateDiagonalTailChunk000Sub000Block055Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block055Part022CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block055Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block055Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block055Part022CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block055Part022SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block055Part022] using hcert

def TailChunk000Sub000Block055Part023SupportExplicit : Finset ℕ :=
  ([2351] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block055Part023 : ℚ :=
  (27630477799 : ℚ) / 3050410585125000

def SurrogateDiagonalTailChunk000Sub000Block055Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2351
    = surrogateDiagTailX0RatChunk000Sub000Block055Part023

theorem surrogateDiagonalTailChunk000Sub000Block055Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block055Part023CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block055Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block055Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block055Part023CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block055Part023SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block055Part023] using hcert

def TailChunk000Sub000Block055Part024SupportExplicit : Finset ℕ :=
  ([2353] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block055Part024 : ℚ :=
  (2843156077 : ℚ) / 241913076940800

def SurrogateDiagonalTailChunk000Sub000Block055Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2353
    = surrogateDiagTailX0RatChunk000Sub000Block055Part024

theorem surrogateDiagonalTailChunk000Sub000Block055Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block055Part024CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block055Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block055Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block055Part024CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block055Part024SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block055Part024] using hcert

def surrogateDiagonalTailChunk000Sub000Block055HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block055Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block055Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block055Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block055Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block055Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block055Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block055Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block055Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block055Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block055Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block055Head : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block055Part000
    + surrogateDiagTailX0RatChunk000Sub000Block055Part001
    + surrogateDiagTailX0RatChunk000Sub000Block055Part002
    + surrogateDiagTailX0RatChunk000Sub000Block055Part003
    + surrogateDiagTailX0RatChunk000Sub000Block055Part004
    + surrogateDiagTailX0RatChunk000Sub000Block055Part005
    + surrogateDiagTailX0RatChunk000Sub000Block055Part006
    + surrogateDiagTailX0RatChunk000Sub000Block055Part007
    + surrogateDiagTailX0RatChunk000Sub000Block055Part008
    + surrogateDiagTailX0RatChunk000Sub000Block055Part009

def surrogateDiagonalTailChunk000Sub000Block055MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block055Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block055Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block055Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block055Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block055Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block055Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block055Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block055Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block055Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block055Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block055Mid : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block055Part010
    + surrogateDiagTailX0RatChunk000Sub000Block055Part011
    + surrogateDiagTailX0RatChunk000Sub000Block055Part012
    + surrogateDiagTailX0RatChunk000Sub000Block055Part013
    + surrogateDiagTailX0RatChunk000Sub000Block055Part014
    + surrogateDiagTailX0RatChunk000Sub000Block055Part015
    + surrogateDiagTailX0RatChunk000Sub000Block055Part016
    + surrogateDiagTailX0RatChunk000Sub000Block055Part017
    + surrogateDiagTailX0RatChunk000Sub000Block055Part018
    + surrogateDiagTailX0RatChunk000Sub000Block055Part019

def surrogateDiagonalTailChunk000Sub000Block055TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block055Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block055Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block055Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block055Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block055Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block055Tail : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block055Part020
    + surrogateDiagTailX0RatChunk000Sub000Block055Part021
    + surrogateDiagTailX0RatChunk000Sub000Block055Part022
    + surrogateDiagTailX0RatChunk000Sub000Block055Part023
    + surrogateDiagTailX0RatChunk000Sub000Block055Part024

def surrogateDiagonalTailChunk000Sub000Block055Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub000Block055HeadSum X0
    + surrogateDiagonalTailChunk000Sub000Block055MidSum X0
    + surrogateDiagonalTailChunk000Sub000Block055TailSum X0

def surrogateDiagTailX0RatChunk000Sub000Block055 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block055Part000
    + surrogateDiagTailX0RatChunk000Sub000Block055Part001
    + surrogateDiagTailX0RatChunk000Sub000Block055Part002
    + surrogateDiagTailX0RatChunk000Sub000Block055Part003
    + surrogateDiagTailX0RatChunk000Sub000Block055Part004
    + surrogateDiagTailX0RatChunk000Sub000Block055Part005
    + surrogateDiagTailX0RatChunk000Sub000Block055Part006
    + surrogateDiagTailX0RatChunk000Sub000Block055Part007
    + surrogateDiagTailX0RatChunk000Sub000Block055Part008
    + surrogateDiagTailX0RatChunk000Sub000Block055Part009
    + surrogateDiagTailX0RatChunk000Sub000Block055Part010
    + surrogateDiagTailX0RatChunk000Sub000Block055Part011
    + surrogateDiagTailX0RatChunk000Sub000Block055Part012
    + surrogateDiagTailX0RatChunk000Sub000Block055Part013
    + surrogateDiagTailX0RatChunk000Sub000Block055Part014
    + surrogateDiagTailX0RatChunk000Sub000Block055Part015
    + surrogateDiagTailX0RatChunk000Sub000Block055Part016
    + surrogateDiagTailX0RatChunk000Sub000Block055Part017
    + surrogateDiagTailX0RatChunk000Sub000Block055Part018
    + surrogateDiagTailX0RatChunk000Sub000Block055Part019
    + surrogateDiagTailX0RatChunk000Sub000Block055Part020
    + surrogateDiagTailX0RatChunk000Sub000Block055Part021
    + surrogateDiagTailX0RatChunk000Sub000Block055Part022
    + surrogateDiagTailX0RatChunk000Sub000Block055Part023
    + surrogateDiagTailX0RatChunk000Sub000Block055Part024

theorem surrogateDiagTailX0RatChunk000Sub000Block055_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk000Sub000Block055Head + surrogateDiagTailX0RatChunk000Sub000Block055Mid + surrogateDiagTailX0RatChunk000Sub000Block055Tail =
      surrogateDiagTailX0RatChunk000Sub000Block055 := by
  unfold surrogateDiagTailX0RatChunk000Sub000Block055Head surrogateDiagTailX0RatChunk000Sub000Block055Mid surrogateDiagTailX0RatChunk000Sub000Block055Tail surrogateDiagTailX0RatChunk000Sub000Block055
  ring

def SurrogateDiagonalTailChunk000Sub000Block055HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block055HeadSum X0 = surrogateDiagTailX0RatChunk000Sub000Block055Head

def SurrogateDiagonalTailChunk000Sub000Block055MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block055MidSum X0 = surrogateDiagTailX0RatChunk000Sub000Block055Mid

def SurrogateDiagonalTailChunk000Sub000Block055TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block055TailSum X0 = surrogateDiagTailX0RatChunk000Sub000Block055Tail

theorem surrogateDiagonalTailChunk000Sub000Block055_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk000Sub000Block055HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk000Sub000Block055MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk000Sub000Block055TailCertificateAt X0) :
    surrogateDiagonalTailChunk000Sub000Block055Sum X0 = surrogateDiagTailX0RatChunk000Sub000Block055 := by
  unfold SurrogateDiagonalTailChunk000Sub000Block055HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk000Sub000Block055MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk000Sub000Block055TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk000Sub000Block055Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk000Sub000Block055_eq_head_add_mid_add_tail

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

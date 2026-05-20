import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0TailPilot25

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

open scoped BigOperators

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

/- Generated direct-term certificate blocks for tail chunk 000, subchunk 000, blocks [175,176). -/

/-- Block 175 covers tail-support indices [4375,4400) and q from 7249 to 7289. -/

def TailChunk000Sub000Block175Part000SupportExplicit : Finset ℕ :=
  ([7249] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block175Part000 : ℚ :=
  (115963959679 : ℚ) / 187495316861059200

def SurrogateDiagonalTailChunk000Sub000Block175Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7249
    = surrogateDiagTailX0RatChunk000Sub000Block175Part000

theorem surrogateDiagonalTailChunk000Sub000Block175Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block175Part000CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block175Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block175Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block175Part000CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block175Part000SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block175Part000] using hcert

def TailChunk000Sub000Block175Part001SupportExplicit : Finset ℕ :=
  ([7251] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block175Part001 : ℚ :=
  (912498364925 : ℚ) / 681560739833708544

def SurrogateDiagonalTailChunk000Sub000Block175Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7251
    = surrogateDiagTailX0RatChunk000Sub000Block175Part001

theorem surrogateDiagonalTailChunk000Sub000Block175Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block175Part001CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block175Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block175Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block175Part001CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block175Part001SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block175Part001] using hcert

def TailChunk000Sub000Block175Part002SupportExplicit : Finset ℕ :=
  ([7253] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block175Part002 : ℚ :=
  (821968890625 : ℚ) / 1729012166400382752

def SurrogateDiagonalTailChunk000Sub000Block175Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7253
    = surrogateDiagTailX0RatChunk000Sub000Block175Part002

theorem surrogateDiagonalTailChunk000Sub000Block175Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block175Part002CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block175Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block175Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block175Part002CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block175Part002SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block175Part002] using hcert

def TailChunk000Sub000Block175Part003SupportExplicit : Finset ℕ :=
  ([7255] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block175Part003 : ℚ :=
  (6246104959 : ℚ) / 7074224562000000

def SurrogateDiagonalTailChunk000Sub000Block175Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7255
    = surrogateDiagTailX0RatChunk000Sub000Block175Part003

theorem surrogateDiagonalTailChunk000Sub000Block175Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block175Part003CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block175Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block175Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block175Part003CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block175Part003SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block175Part003] using hcert

def TailChunk000Sub000Block175Part004SupportExplicit : Finset ℕ :=
  ([7257] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block175Part004 : ℚ :=
  (34833772223 : ℚ) / 23180819044761600

def SurrogateDiagonalTailChunk000Sub000Block175Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7257
    = surrogateDiagTailX0RatChunk000Sub000Block175Part004

theorem surrogateDiagonalTailChunk000Sub000Block175Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block175Part004CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block175Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block175Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block175Part004CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block175Part004SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block175Part004] using hcert

def TailChunk000Sub000Block175Part005SupportExplicit : Finset ℕ :=
  ([7258] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block175Part005 : ℚ :=
  (60880733431 : ℚ) / 13683313411459200

def SurrogateDiagonalTailChunk000Sub000Block175Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7258
    = surrogateDiagTailX0RatChunk000Sub000Block175Part005

theorem surrogateDiagonalTailChunk000Sub000Block175Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block175Part005CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block175Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block175Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block175Part005CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block175Part005SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block175Part005] using hcert

def TailChunk000Sub000Block175Part006SupportExplicit : Finset ℕ :=
  ([7259] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block175Part006 : ℚ :=
  (5950686949 : ℚ) / 6881083077427200

def SurrogateDiagonalTailChunk000Sub000Block175Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7259
    = surrogateDiagTailX0RatChunk000Sub000Block175Part006

theorem surrogateDiagonalTailChunk000Sub000Block175Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block175Part006CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block175Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block175Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block175Part006CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block175Part006SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block175Part006] using hcert

def TailChunk000Sub000Block175Part007SupportExplicit : Finset ℕ :=
  ([7261] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block175Part007 : ℚ :=
  (3184208889025 : ℚ) / 6254547093831548928

def SurrogateDiagonalTailChunk000Sub000Block175Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7261
    = surrogateDiagTailX0RatChunk000Sub000Block175Part007

theorem surrogateDiagonalTailChunk000Sub000Block175Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block175Part007CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block175Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block175Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block175Part007CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block175Part007SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block175Part007] using hcert

def TailChunk000Sub000Block175Part008SupportExplicit : Finset ℕ :=
  ([7262] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block175Part008 : ℚ :=
  (65907620839 : ℚ) / 17366541974872200

def SurrogateDiagonalTailChunk000Sub000Block175Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7262
    = surrogateDiagTailX0RatChunk000Sub000Block175Part008

theorem surrogateDiagonalTailChunk000Sub000Block175Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block175Part008CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block175Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block175Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block175Part008CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block175Part008SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block175Part008] using hcert

def TailChunk000Sub000Block175Part009SupportExplicit : Finset ℕ :=
  ([7265] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block175Part009 : ℚ :=
  (2373461223325 : ℚ) / 2845334237163061248

def SurrogateDiagonalTailChunk000Sub000Block175Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7265
    = surrogateDiagTailX0RatChunk000Sub000Block175Part009

theorem surrogateDiagonalTailChunk000Sub000Block175Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block175Part009CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block175Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block175Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block175Part009CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block175Part009SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block175Part009] using hcert

def TailChunk000Sub000Block175Part010SupportExplicit : Finset ℕ :=
  ([7266] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block175Part010 : ℚ :=
  (30549207125 : ℚ) / 1680745149333504

def SurrogateDiagonalTailChunk000Sub000Block175Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7266
    = surrogateDiagTailX0RatChunk000Sub000Block175Part010

theorem surrogateDiagonalTailChunk000Sub000Block175Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block175Part010CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block175Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block175Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block175Part010CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block175Part010SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block175Part010] using hcert

def TailChunk000Sub000Block175Part011SupportExplicit : Finset ℕ :=
  ([7269] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block175Part011 : ℚ :=
  (458517357775 : ℚ) / 344178236833550112

def SurrogateDiagonalTailChunk000Sub000Block175Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7269
    = surrogateDiagTailX0RatChunk000Sub000Block175Part011

theorem surrogateDiagonalTailChunk000Sub000Block175Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block175Part011CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block175Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block175Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block175Part011CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block175Part011SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block175Part011] using hcert

def TailChunk000Sub000Block175Part012SupportExplicit : Finset ℕ :=
  ([7270] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block175Part012 : ℚ :=
  (242032582925 : ℚ) / 59277796607563776

def SurrogateDiagonalTailChunk000Sub000Block175Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7270
    = surrogateDiagTailX0RatChunk000Sub000Block175Part012

theorem surrogateDiagonalTailChunk000Sub000Block175Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block175Part012CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block175Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block175Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block175Part012CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block175Part012SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block175Part012] using hcert

def TailChunk000Sub000Block175Part013SupportExplicit : Finset ℕ :=
  ([7271] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block175Part013 : ℚ :=
  (350237809 : ℚ) / 575106998400000

def SurrogateDiagonalTailChunk000Sub000Block175Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7271
    = surrogateDiagTailX0RatChunk000Sub000Block175Part013

theorem surrogateDiagonalTailChunk000Sub000Block175Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block175Part013CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block175Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block175Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block175Part013CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block175Part013SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block175Part013] using hcert

def TailChunk000Sub000Block175Part014SupportExplicit : Finset ℕ :=
  ([7273] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block175Part014 : ℚ :=
  (2695966901875 : ℚ) / 3762021510812032128

def SurrogateDiagonalTailChunk000Sub000Block175Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7273
    = surrogateDiagTailX0RatChunk000Sub000Block175Part014

theorem surrogateDiagonalTailChunk000Sub000Block175Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block175Part014CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block175Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block175Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block175Part014CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block175Part014SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block175Part014] using hcert

def TailChunk000Sub000Block175Part015SupportExplicit : Finset ℕ :=
  ([7274] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block175Part015 : ℚ :=
  (206683890625 : ℚ) / 109260294243070752

def SurrogateDiagonalTailChunk000Sub000Block175Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7274
    = surrogateDiagTailX0RatChunk000Sub000Block175Part015

theorem surrogateDiagonalTailChunk000Sub000Block175Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block175Part015CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block175Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block175Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block175Part015CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block175Part015SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block175Part015] using hcert

def TailChunk000Sub000Block175Part016SupportExplicit : Finset ℕ :=
  ([7277] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block175Part016 : ℚ :=
  (3070552635925 : ℚ) / 5589466157070914688

def SurrogateDiagonalTailChunk000Sub000Block175Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7277
    = surrogateDiagTailX0RatChunk000Sub000Block175Part016

theorem surrogateDiagonalTailChunk000Sub000Block175Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block175Part016CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block175Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block175Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block175Part016CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block175Part016SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block175Part016] using hcert

def TailChunk000Sub000Block175Part017SupportExplicit : Finset ℕ :=
  ([7278] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block175Part017 : ℚ :=
  (643397952925 : ℚ) / 86329121377241088

def SurrogateDiagonalTailChunk000Sub000Block175Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7278
    = surrogateDiagTailX0RatChunk000Sub000Block175Part017

theorem surrogateDiagonalTailChunk000Sub000Block175Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block175Part017CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block175Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block175Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block175Part017CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block175Part017SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block175Part017] using hcert

def TailChunk000Sub000Block175Part018SupportExplicit : Finset ℕ :=
  ([7279] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block175Part018 : ℚ :=
  (41893878891 : ℚ) / 80049340000000000

def SurrogateDiagonalTailChunk000Sub000Block175Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7279
    = surrogateDiagTailX0RatChunk000Sub000Block175Part018

theorem surrogateDiagonalTailChunk000Sub000Block175Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block175Part018CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block175Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block175Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block175Part018CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block175Part018SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block175Part018] using hcert

def TailChunk000Sub000Block175Part019SupportExplicit : Finset ℕ :=
  ([7282] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block175Part019 : ℚ :=
  (15583340237 : ℚ) / 5930790921000000

def SurrogateDiagonalTailChunk000Sub000Block175Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7282
    = surrogateDiagTailX0RatChunk000Sub000Block175Part019

theorem surrogateDiagonalTailChunk000Sub000Block175Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block175Part019CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block175Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block175Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block175Part019CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block175Part019SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block175Part019] using hcert

def TailChunk000Sub000Block175Part020SupportExplicit : Finset ℕ :=
  ([7283] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block175Part020 : ℚ :=
  (828782640625 : ℚ) / 1757800428269306322

def SurrogateDiagonalTailChunk000Sub000Block175Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7283
    = surrogateDiagTailX0RatChunk000Sub000Block175Part020

theorem surrogateDiagonalTailChunk000Sub000Block175Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block175Part020CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block175Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block175Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block175Part020CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block175Part020SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block175Part020] using hcert

def TailChunk000Sub000Block175Part021SupportExplicit : Finset ℕ :=
  ([7285] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block175Part021 : ℚ :=
  (7443882451 : ℚ) / 7738591376793600

def SurrogateDiagonalTailChunk000Sub000Block175Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7285
    = surrogateDiagTailX0RatChunk000Sub000Block175Part021

theorem surrogateDiagonalTailChunk000Sub000Block175Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block175Part021CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block175Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block175Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block175Part021CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block175Part021SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block175Part021] using hcert

def TailChunk000Sub000Block175Part022SupportExplicit : Finset ℕ :=
  ([7286] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block175Part022 : ℚ :=
  (207366390625 : ℚ) / 109983271392637362

def SurrogateDiagonalTailChunk000Sub000Block175Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7286
    = surrogateDiagTailX0RatChunk000Sub000Block175Part022

theorem surrogateDiagonalTailChunk000Sub000Block175Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block175Part022CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block175Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block175Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block175Part022CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block175Part022SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block175Part022] using hcert

def TailChunk000Sub000Block175Part023SupportExplicit : Finset ℕ :=
  ([7287] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block175Part023 : ℚ :=
  (768915540725 : ℚ) / 371557680080200704

def SurrogateDiagonalTailChunk000Sub000Block175Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7287
    = surrogateDiagTailX0RatChunk000Sub000Block175Part023

theorem surrogateDiagonalTailChunk000Sub000Block175Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block175Part023CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block175Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block175Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block175Part023CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block175Part023SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block175Part023] using hcert

def TailChunk000Sub000Block175Part024SupportExplicit : Finset ℕ :=
  ([7289] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block175Part024 : ℚ :=
  (117816389225 : ℚ) / 229560616931917824

def SurrogateDiagonalTailChunk000Sub000Block175Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7289
    = surrogateDiagTailX0RatChunk000Sub000Block175Part024

theorem surrogateDiagonalTailChunk000Sub000Block175Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block175Part024CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block175Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block175Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block175Part024CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block175Part024SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block175Part024] using hcert

def surrogateDiagonalTailChunk000Sub000Block175HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block175Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block175Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block175Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block175Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block175Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block175Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block175Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block175Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block175Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block175Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block175Head : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block175Part000
    + surrogateDiagTailX0RatChunk000Sub000Block175Part001
    + surrogateDiagTailX0RatChunk000Sub000Block175Part002
    + surrogateDiagTailX0RatChunk000Sub000Block175Part003
    + surrogateDiagTailX0RatChunk000Sub000Block175Part004
    + surrogateDiagTailX0RatChunk000Sub000Block175Part005
    + surrogateDiagTailX0RatChunk000Sub000Block175Part006
    + surrogateDiagTailX0RatChunk000Sub000Block175Part007
    + surrogateDiagTailX0RatChunk000Sub000Block175Part008
    + surrogateDiagTailX0RatChunk000Sub000Block175Part009

def surrogateDiagonalTailChunk000Sub000Block175MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block175Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block175Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block175Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block175Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block175Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block175Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block175Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block175Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block175Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block175Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block175Mid : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block175Part010
    + surrogateDiagTailX0RatChunk000Sub000Block175Part011
    + surrogateDiagTailX0RatChunk000Sub000Block175Part012
    + surrogateDiagTailX0RatChunk000Sub000Block175Part013
    + surrogateDiagTailX0RatChunk000Sub000Block175Part014
    + surrogateDiagTailX0RatChunk000Sub000Block175Part015
    + surrogateDiagTailX0RatChunk000Sub000Block175Part016
    + surrogateDiagTailX0RatChunk000Sub000Block175Part017
    + surrogateDiagTailX0RatChunk000Sub000Block175Part018
    + surrogateDiagTailX0RatChunk000Sub000Block175Part019

def surrogateDiagonalTailChunk000Sub000Block175TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block175Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block175Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block175Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block175Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block175Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block175Tail : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block175Part020
    + surrogateDiagTailX0RatChunk000Sub000Block175Part021
    + surrogateDiagTailX0RatChunk000Sub000Block175Part022
    + surrogateDiagTailX0RatChunk000Sub000Block175Part023
    + surrogateDiagTailX0RatChunk000Sub000Block175Part024

def surrogateDiagonalTailChunk000Sub000Block175Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub000Block175HeadSum X0
    + surrogateDiagonalTailChunk000Sub000Block175MidSum X0
    + surrogateDiagonalTailChunk000Sub000Block175TailSum X0

def surrogateDiagTailX0RatChunk000Sub000Block175 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block175Part000
    + surrogateDiagTailX0RatChunk000Sub000Block175Part001
    + surrogateDiagTailX0RatChunk000Sub000Block175Part002
    + surrogateDiagTailX0RatChunk000Sub000Block175Part003
    + surrogateDiagTailX0RatChunk000Sub000Block175Part004
    + surrogateDiagTailX0RatChunk000Sub000Block175Part005
    + surrogateDiagTailX0RatChunk000Sub000Block175Part006
    + surrogateDiagTailX0RatChunk000Sub000Block175Part007
    + surrogateDiagTailX0RatChunk000Sub000Block175Part008
    + surrogateDiagTailX0RatChunk000Sub000Block175Part009
    + surrogateDiagTailX0RatChunk000Sub000Block175Part010
    + surrogateDiagTailX0RatChunk000Sub000Block175Part011
    + surrogateDiagTailX0RatChunk000Sub000Block175Part012
    + surrogateDiagTailX0RatChunk000Sub000Block175Part013
    + surrogateDiagTailX0RatChunk000Sub000Block175Part014
    + surrogateDiagTailX0RatChunk000Sub000Block175Part015
    + surrogateDiagTailX0RatChunk000Sub000Block175Part016
    + surrogateDiagTailX0RatChunk000Sub000Block175Part017
    + surrogateDiagTailX0RatChunk000Sub000Block175Part018
    + surrogateDiagTailX0RatChunk000Sub000Block175Part019
    + surrogateDiagTailX0RatChunk000Sub000Block175Part020
    + surrogateDiagTailX0RatChunk000Sub000Block175Part021
    + surrogateDiagTailX0RatChunk000Sub000Block175Part022
    + surrogateDiagTailX0RatChunk000Sub000Block175Part023
    + surrogateDiagTailX0RatChunk000Sub000Block175Part024

theorem surrogateDiagTailX0RatChunk000Sub000Block175_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk000Sub000Block175Head + surrogateDiagTailX0RatChunk000Sub000Block175Mid + surrogateDiagTailX0RatChunk000Sub000Block175Tail =
      surrogateDiagTailX0RatChunk000Sub000Block175 := by
  unfold surrogateDiagTailX0RatChunk000Sub000Block175Head surrogateDiagTailX0RatChunk000Sub000Block175Mid surrogateDiagTailX0RatChunk000Sub000Block175Tail surrogateDiagTailX0RatChunk000Sub000Block175
  ring

def SurrogateDiagonalTailChunk000Sub000Block175HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block175HeadSum X0 = surrogateDiagTailX0RatChunk000Sub000Block175Head

def SurrogateDiagonalTailChunk000Sub000Block175MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block175MidSum X0 = surrogateDiagTailX0RatChunk000Sub000Block175Mid

def SurrogateDiagonalTailChunk000Sub000Block175TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block175TailSum X0 = surrogateDiagTailX0RatChunk000Sub000Block175Tail

theorem surrogateDiagonalTailChunk000Sub000Block175_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk000Sub000Block175HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk000Sub000Block175MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk000Sub000Block175TailCertificateAt X0) :
    surrogateDiagonalTailChunk000Sub000Block175Sum X0 = surrogateDiagTailX0RatChunk000Sub000Block175 := by
  unfold SurrogateDiagonalTailChunk000Sub000Block175HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk000Sub000Block175MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk000Sub000Block175TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk000Sub000Block175Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk000Sub000Block175_eq_head_add_mid_add_tail

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

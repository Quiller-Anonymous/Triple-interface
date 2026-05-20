import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0TailPilot25

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

open scoped BigOperators

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

/- Generated direct-term certificate blocks for tail chunk 000, subchunk 000, blocks [49,50). -/

/- Block 049 covers tail-support indices [1225,1250) and q from 2069 to 2109. -/

def TailChunk000Sub000Block049Part000SupportExplicit : Finset ℕ :=
  ([2069] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block049Part000 : ℚ :=
  (267440543475 : ℚ) / 15244308949952896

def SurrogateDiagonalTailChunk000Sub000Block049Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2069
    = surrogateDiagTailX0RatChunk000Sub000Block049Part000

theorem surrogateDiagonalTailChunk000Sub000Block049Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block049Part000CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block049Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block049Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block049Part000CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block049Part000SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block049Part000] using hcert

def TailChunk000Sub000Block049Part001SupportExplicit : Finset ℕ :=
  ([2071] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block049Part001 : ℚ :=
  (510139216525 : ℚ) / 35711813200693248

def SurrogateDiagonalTailChunk000Sub000Block049Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2071
    = surrogateDiagTailX0RatChunk000Sub000Block049Part001

theorem surrogateDiagonalTailChunk000Sub000Block049Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block049Part001CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block049Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block049Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block049Part001CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block049Part001SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block049Part001] using hcert

def TailChunk000Sub000Block049Part002SupportExplicit : Finset ℕ :=
  ([2073] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block049Part002 : ℚ :=
  (168490037 : ℚ) / 3942896421600

def SurrogateDiagonalTailChunk000Sub000Block049Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2073
    = surrogateDiagTailX0RatChunk000Sub000Block049Part002

theorem surrogateDiagonalTailChunk000Sub000Block049Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block049Part002CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block049Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block049Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block049Part002CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block049Part002SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block049Part002] using hcert

def TailChunk000Sub000Block049Part003SupportExplicit : Finset ℕ :=
  ([2074] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block049Part003 : ℚ :=
  (5058416717 : ℚ) / 42475821465600

def SurrogateDiagonalTailChunk000Sub000Block049Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2074
    = surrogateDiagTailX0RatChunk000Sub000Block049Part003

theorem surrogateDiagonalTailChunk000Sub000Block049Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block049Part003CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block049Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block049Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block049Part003CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block049Part003SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block049Part003] using hcert

def TailChunk000Sub000Block049Part004SupportExplicit : Finset ℕ :=
  ([2077] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block049Part004 : ℚ :=
  (7639967893 : ℚ) / 384315251680800

def SurrogateDiagonalTailChunk000Sub000Block049Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2077
    = surrogateDiagTailX0RatChunk000Sub000Block049Part004

theorem surrogateDiagonalTailChunk000Sub000Block049Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block049Part004CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block049Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block049Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block049Part004CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block049Part004SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block049Part004] using hcert

def TailChunk000Sub000Block049Part005SupportExplicit : Finset ℕ :=
  ([2078] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block049Part005 : ℚ :=
  (168540216125 : ℚ) / 1451397187813284

def SurrogateDiagonalTailChunk000Sub000Block049Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2078
    = surrogateDiagTailX0RatChunk000Sub000Block049Part005

theorem surrogateDiagonalTailChunk000Sub000Block049Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block049Part005CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block049Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block049Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block049Part005CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block049Part005SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block049Part005] using hcert

def TailChunk000Sub000Block049Part006SupportExplicit : Finset ℕ :=
  ([2081] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block049Part006 : ℚ :=
  (21648474439 : ℚ) / 1872148050739200

def SurrogateDiagonalTailChunk000Sub000Block049Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2081
    = surrogateDiagTailX0RatChunk000Sub000Block049Part006

theorem surrogateDiagonalTailChunk000Sub000Block049Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block049Part006CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block049Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block049Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block049Part006CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block049Part006SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block049Part006] using hcert

def TailChunk000Sub000Block049Part007SupportExplicit : Finset ℕ :=
  ([2082] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block049Part007 : ℚ :=
  (22509075 : ℚ) / 57327682624

def SurrogateDiagonalTailChunk000Sub000Block049Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2082
    = surrogateDiagTailX0RatChunk000Sub000Block049Part007

theorem surrogateDiagonalTailChunk000Sub000Block049Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block049Part007CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block049Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block049Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block049Part007CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block049Part007SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block049Part007] using hcert

def TailChunk000Sub000Block049Part008SupportExplicit : Finset ℕ :=
  ([2083] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block049Part008 : ℚ :=
  (542252652775 : ℚ) / 46983975306518088

def SurrogateDiagonalTailChunk000Sub000Block049Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2083
    = surrogateDiagTailX0RatChunk000Sub000Block049Part008

theorem surrogateDiagonalTailChunk000Sub000Block049Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block049Part008CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block049Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block049Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block049Part008CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block049Part008SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block049Part008] using hcert

def TailChunk000Sub000Block049Part009SupportExplicit : Finset ℕ :=
  ([2085] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block049Part009 : ℚ :=
  (373888892725 : ℚ) / 3714523860860928

def SurrogateDiagonalTailChunk000Sub000Block049Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2085
    = surrogateDiagTailX0RatChunk000Sub000Block049Part009

theorem surrogateDiagonalTailChunk000Sub000Block049Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block049Part009CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block049Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block049Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block049Part009CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block049Part009SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block049Part009] using hcert

def TailChunk000Sub000Block049Part010SupportExplicit : Finset ℕ :=
  ([2086] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block049Part010 : ℚ :=
  (288039682675 : ℚ) / 1554815000659968

def SurrogateDiagonalTailChunk000Sub000Block049Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2086
    = surrogateDiagTailX0RatChunk000Sub000Block049Part010

theorem surrogateDiagonalTailChunk000Sub000Block049Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block049Part010CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block049Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block049Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block049Part010CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block049Part010SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block049Part010] using hcert

def TailChunk000Sub000Block049Part011SupportExplicit : Finset ℕ :=
  ([2087] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block049Part011 : ℚ :=
  (544337235775 : ℚ) / 47346085195614408

def SurrogateDiagonalTailChunk000Sub000Block049Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2087
    = surrogateDiagTailX0RatChunk000Sub000Block049Part011

theorem surrogateDiagonalTailChunk000Sub000Block049Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block049Part011CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block049Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block049Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block049Part011CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block049Part011SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block049Part011] using hcert

def TailChunk000Sub000Block049Part012SupportExplicit : Finset ℕ :=
  ([2089] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block049Part012 : ℚ :=
  (545381026975 : ℚ) / 47527923047712768

def SurrogateDiagonalTailChunk000Sub000Block049Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2089
    = surrogateDiagTailX0RatChunk000Sub000Block049Part012

theorem surrogateDiagonalTailChunk000Sub000Block049Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block049Part012CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block049Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block049Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block049Part012CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block049Part012SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block049Part012] using hcert

def TailChunk000Sub000Block049Part013SupportExplicit : Finset ℕ :=
  ([2090] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block049Part013 : ℚ :=
  (1543139159 : ℚ) / 4479871795200

def SurrogateDiagonalTailChunk000Sub000Block049Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2090
    = surrogateDiagTailX0RatChunk000Sub000Block049Part013

theorem surrogateDiagonalTailChunk000Sub000Block049Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block049Part013CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block049Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block049Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block049Part013CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block049Part013SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block049Part013] using hcert

def TailChunk000Sub000Block049Part014SupportExplicit : Finset ℕ :=
  ([2091] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block049Part014 : ℚ :=
  (243694953 : ℚ) / 4474819051520

def SurrogateDiagonalTailChunk000Sub000Block049Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2091
    = surrogateDiagTailX0RatChunk000Sub000Block049Part014

theorem surrogateDiagonalTailChunk000Sub000Block049Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block049Part014CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block049Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block049Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block049Part014CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block049Part014SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block049Part014] using hcert

def TailChunk000Sub000Block049Part015SupportExplicit : Finset ℕ :=
  ([2093] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block049Part015 : ℚ :=
  (146061876475 : ℚ) / 3935388177211392

def SurrogateDiagonalTailChunk000Sub000Block049Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2093
    = surrogateDiagTailX0RatChunk000Sub000Block049Part015

theorem surrogateDiagonalTailChunk000Sub000Block049Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block049Part015CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block049Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block049Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block049Part015CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block049Part015SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block049Part015] using hcert

def TailChunk000Sub000Block049Part016SupportExplicit : Finset ℕ :=
  ([2094] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block049Part016 : ℚ :=
  (110083407425 : ℚ) / 293382241035264

def SurrogateDiagonalTailChunk000Sub000Block049Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2094
    = surrogateDiagTailX0RatChunk000Sub000Block049Part016

theorem surrogateDiagonalTailChunk000Sub000Block049Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block049Part016CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block049Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block049Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block049Part016CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block049Part016SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block049Part016] using hcert

def TailChunk000Sub000Block049Part017SupportExplicit : Finset ℕ :=
  ([2095] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block049Part017 : ℚ :=
  (623806802725 : ℚ) / 19542132397590528

def SurrogateDiagonalTailChunk000Sub000Block049Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2095
    = surrogateDiagTailX0RatChunk000Sub000Block049Part017

theorem surrogateDiagonalTailChunk000Sub000Block049Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block049Part017CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block049Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block049Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block049Part017CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block049Part017SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block049Part017] using hcert

def TailChunk000Sub000Block049Part018SupportExplicit : Finset ℕ :=
  ([2098] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block049Part018 : ℚ :=
  (171800106125 : ℚ) / 1508141163439104

def SurrogateDiagonalTailChunk000Sub000Block049Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2098
    = surrogateDiagTailX0RatChunk000Sub000Block049Part018

theorem surrogateDiagonalTailChunk000Sub000Block049Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block049Part018CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block049Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block049Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block049Part018CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block049Part018SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block049Part018] using hcert

def TailChunk000Sub000Block049Part019SupportExplicit : Finset ℕ :=
  ([2099] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block049Part019 : ℚ :=
  (550614979975 : ℚ) / 48444981490926408

def SurrogateDiagonalTailChunk000Sub000Block049Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2099
    = surrogateDiagTailX0RatChunk000Sub000Block049Part019

theorem surrogateDiagonalTailChunk000Sub000Block049Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block049Part019CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block049Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block049Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block049Part019CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block049Part019SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block049Part019] using hcert

def TailChunk000Sub000Block049Part020SupportExplicit : Finset ℕ :=
  ([2101] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block049Part020 : ℚ :=
  (29280024067 : ℚ) / 1303470642000000

def SurrogateDiagonalTailChunk000Sub000Block049Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2101
    = surrogateDiagTailX0RatChunk000Sub000Block049Part020

theorem surrogateDiagonalTailChunk000Sub000Block049Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block049Part020CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block049Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block049Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block049Part020CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block049Part020SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block049Part020] using hcert

def TailChunk000Sub000Block049Part021SupportExplicit : Finset ℕ :=
  ([2102] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block049Part021 : ℚ :=
  (1379646649 : ℚ) / 12157493512500

def SurrogateDiagonalTailChunk000Sub000Block049Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2102
    = surrogateDiagTailX0RatChunk000Sub000Block049Part021

theorem surrogateDiagonalTailChunk000Sub000Block049Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block049Part021CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block049Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block049Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block049Part021CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block049Part021SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block049Part021] using hcert

def TailChunk000Sub000Block049Part022SupportExplicit : Finset ℕ :=
  ([2103] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block049Part022 : ℚ :=
  (19627907191 : ℚ) / 384236832000000

def SurrogateDiagonalTailChunk000Sub000Block049Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2103
    = surrogateDiagTailX0RatChunk000Sub000Block049Part022

theorem surrogateDiagonalTailChunk000Sub000Block049Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block049Part022CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block049Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block049Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block049Part022CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block049Part022SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block049Part022] using hcert

def TailChunk000Sub000Block049Part023SupportExplicit : Finset ℕ :=
  ([2105] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block049Part023 : ℚ :=
  (2063921281 : ℚ) / 88528166092800

def SurrogateDiagonalTailChunk000Sub000Block049Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2105
    = surrogateDiagTailX0RatChunk000Sub000Block049Part023

theorem surrogateDiagonalTailChunk000Sub000Block049Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block049Part023CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block049Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block049Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block049Part023CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block049Part023SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block049Part023] using hcert

def TailChunk000Sub000Block049Part024SupportExplicit : Finset ℕ :=
  ([2109] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block049Part024 : ℚ :=
  (373041703675 : ℚ) / 7054185323593728

def SurrogateDiagonalTailChunk000Sub000Block049Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2109
    = surrogateDiagTailX0RatChunk000Sub000Block049Part024

theorem surrogateDiagonalTailChunk000Sub000Block049Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block049Part024CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block049Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block049Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block049Part024CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block049Part024SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block049Part024] using hcert

def surrogateDiagonalTailChunk000Sub000Block049HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block049Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block049Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block049Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block049Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block049Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block049Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block049Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block049Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block049Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block049Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block049Head : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block049Part000
    + surrogateDiagTailX0RatChunk000Sub000Block049Part001
    + surrogateDiagTailX0RatChunk000Sub000Block049Part002
    + surrogateDiagTailX0RatChunk000Sub000Block049Part003
    + surrogateDiagTailX0RatChunk000Sub000Block049Part004
    + surrogateDiagTailX0RatChunk000Sub000Block049Part005
    + surrogateDiagTailX0RatChunk000Sub000Block049Part006
    + surrogateDiagTailX0RatChunk000Sub000Block049Part007
    + surrogateDiagTailX0RatChunk000Sub000Block049Part008
    + surrogateDiagTailX0RatChunk000Sub000Block049Part009

def surrogateDiagonalTailChunk000Sub000Block049MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block049Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block049Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block049Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block049Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block049Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block049Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block049Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block049Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block049Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block049Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block049Mid : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block049Part010
    + surrogateDiagTailX0RatChunk000Sub000Block049Part011
    + surrogateDiagTailX0RatChunk000Sub000Block049Part012
    + surrogateDiagTailX0RatChunk000Sub000Block049Part013
    + surrogateDiagTailX0RatChunk000Sub000Block049Part014
    + surrogateDiagTailX0RatChunk000Sub000Block049Part015
    + surrogateDiagTailX0RatChunk000Sub000Block049Part016
    + surrogateDiagTailX0RatChunk000Sub000Block049Part017
    + surrogateDiagTailX0RatChunk000Sub000Block049Part018
    + surrogateDiagTailX0RatChunk000Sub000Block049Part019

def surrogateDiagonalTailChunk000Sub000Block049TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block049Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block049Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block049Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block049Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block049Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block049Tail : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block049Part020
    + surrogateDiagTailX0RatChunk000Sub000Block049Part021
    + surrogateDiagTailX0RatChunk000Sub000Block049Part022
    + surrogateDiagTailX0RatChunk000Sub000Block049Part023
    + surrogateDiagTailX0RatChunk000Sub000Block049Part024

def surrogateDiagonalTailChunk000Sub000Block049Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub000Block049HeadSum X0
    + surrogateDiagonalTailChunk000Sub000Block049MidSum X0
    + surrogateDiagonalTailChunk000Sub000Block049TailSum X0

def surrogateDiagTailX0RatChunk000Sub000Block049 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block049Part000
    + surrogateDiagTailX0RatChunk000Sub000Block049Part001
    + surrogateDiagTailX0RatChunk000Sub000Block049Part002
    + surrogateDiagTailX0RatChunk000Sub000Block049Part003
    + surrogateDiagTailX0RatChunk000Sub000Block049Part004
    + surrogateDiagTailX0RatChunk000Sub000Block049Part005
    + surrogateDiagTailX0RatChunk000Sub000Block049Part006
    + surrogateDiagTailX0RatChunk000Sub000Block049Part007
    + surrogateDiagTailX0RatChunk000Sub000Block049Part008
    + surrogateDiagTailX0RatChunk000Sub000Block049Part009
    + surrogateDiagTailX0RatChunk000Sub000Block049Part010
    + surrogateDiagTailX0RatChunk000Sub000Block049Part011
    + surrogateDiagTailX0RatChunk000Sub000Block049Part012
    + surrogateDiagTailX0RatChunk000Sub000Block049Part013
    + surrogateDiagTailX0RatChunk000Sub000Block049Part014
    + surrogateDiagTailX0RatChunk000Sub000Block049Part015
    + surrogateDiagTailX0RatChunk000Sub000Block049Part016
    + surrogateDiagTailX0RatChunk000Sub000Block049Part017
    + surrogateDiagTailX0RatChunk000Sub000Block049Part018
    + surrogateDiagTailX0RatChunk000Sub000Block049Part019
    + surrogateDiagTailX0RatChunk000Sub000Block049Part020
    + surrogateDiagTailX0RatChunk000Sub000Block049Part021
    + surrogateDiagTailX0RatChunk000Sub000Block049Part022
    + surrogateDiagTailX0RatChunk000Sub000Block049Part023
    + surrogateDiagTailX0RatChunk000Sub000Block049Part024

theorem surrogateDiagTailX0RatChunk000Sub000Block049_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk000Sub000Block049Head + surrogateDiagTailX0RatChunk000Sub000Block049Mid + surrogateDiagTailX0RatChunk000Sub000Block049Tail =
      surrogateDiagTailX0RatChunk000Sub000Block049 := by
  unfold surrogateDiagTailX0RatChunk000Sub000Block049Head surrogateDiagTailX0RatChunk000Sub000Block049Mid surrogateDiagTailX0RatChunk000Sub000Block049Tail surrogateDiagTailX0RatChunk000Sub000Block049
  ring

def SurrogateDiagonalTailChunk000Sub000Block049HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block049HeadSum X0 = surrogateDiagTailX0RatChunk000Sub000Block049Head

def SurrogateDiagonalTailChunk000Sub000Block049MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block049MidSum X0 = surrogateDiagTailX0RatChunk000Sub000Block049Mid

def SurrogateDiagonalTailChunk000Sub000Block049TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block049TailSum X0 = surrogateDiagTailX0RatChunk000Sub000Block049Tail

theorem surrogateDiagonalTailChunk000Sub000Block049_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk000Sub000Block049HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk000Sub000Block049MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk000Sub000Block049TailCertificateAt X0) :
    surrogateDiagonalTailChunk000Sub000Block049Sum X0 = surrogateDiagTailX0RatChunk000Sub000Block049 := by
  unfold SurrogateDiagonalTailChunk000Sub000Block049HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk000Sub000Block049MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk000Sub000Block049TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk000Sub000Block049Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk000Sub000Block049_eq_head_add_mid_add_tail

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

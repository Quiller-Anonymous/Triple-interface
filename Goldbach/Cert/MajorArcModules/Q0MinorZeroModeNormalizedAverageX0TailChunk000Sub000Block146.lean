import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0TailPilot25

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

open scoped BigOperators

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

/- Generated direct-term certificate blocks for tail chunk 000, subchunk 000, blocks [146,147). -/

/- Block 146 covers tail-support indices [3650,3675) and q from 6058 to 6095. -/

def TailChunk000Sub000Block146Part000SupportExplicit : Finset ℕ :=
  ([6058] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block146Part000 : ℚ :=
  (558859770625 : ℚ) / 150211707410055168

def SurrogateDiagonalTailChunk000Sub000Block146Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6058
    = surrogateDiagTailX0RatChunk000Sub000Block146Part000

theorem surrogateDiagonalTailChunk000Sub000Block146Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block146Part000CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block146Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block146Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block146Part000CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block146Part000SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block146Part000] using hcert

def TailChunk000Sub000Block146Part001SupportExplicit : Finset ℕ :=
  ([6059] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block146Part001 : ℚ :=
  (741937627825 : ℚ) / 1012723760310091776

def SurrogateDiagonalTailChunk000Sub000Block146Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6059
    = surrogateDiagTailX0RatChunk000Sub000Block146Part001

theorem surrogateDiagonalTailChunk000Sub000Block146Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block146Part001CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block146Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block146Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block146Part001CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block146Part001SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block146Part001] using hcert

def TailChunk000Sub000Block146Part002SupportExplicit : Finset ℕ :=
  ([6061] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block146Part002 : ℚ :=
  (73993231861 : ℚ) / 64537033081651200

def SurrogateDiagonalTailChunk000Sub000Block146Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6061
    = surrogateDiagTailX0RatChunk000Sub000Block146Part002

theorem surrogateDiagonalTailChunk000Sub000Block146Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block146Part002CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block146Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block146Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block146Part002CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block146Part002SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block146Part002] using hcert

def TailChunk000Sub000Block146Part003SupportExplicit : Finset ℕ :=
  ([6062] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block146Part003 : ℚ :=
  (479249768225 : ℚ) / 56433482588749824

def SurrogateDiagonalTailChunk000Sub000Block146Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6062
    = surrogateDiagTailX0RatChunk000Sub000Block146Part003

theorem surrogateDiagonalTailChunk000Sub000Block146Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block146Part003CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block146Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block146Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block146Part003CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block146Part003SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block146Part003] using hcert

def TailChunk000Sub000Block146Part004SupportExplicit : Finset ℕ :=
  ([6063] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block146Part004 : ℚ :=
  (1219723823875 : ℚ) / 557410736870443008

def SurrogateDiagonalTailChunk000Sub000Block146Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6063
    = surrogateDiagTailX0RatChunk000Sub000Block146Part004

theorem surrogateDiagonalTailChunk000Sub000Block146Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block146Part004CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block146Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block146Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block146Part004CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block146Part004SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block146Part004] using hcert

def TailChunk000Sub000Block146Part005SupportExplicit : Finset ℕ :=
  ([6065] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block146Part005 : ℚ :=
  (290991944275 : ℚ) / 230210990339309568

def SurrogateDiagonalTailChunk000Sub000Block146Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6065
    = surrogateDiagTailX0RatChunk000Sub000Block146Part005

theorem surrogateDiagonalTailChunk000Sub000Block146Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block146Part005CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block146Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block146Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block146Part005CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block146Part005SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block146Part005] using hcert

def TailChunk000Sub000Block146Part006SupportExplicit : Finset ℕ :=
  ([6067] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block146Part006 : ℚ :=
  (575132640625 : ℚ) / 846401630776069842

def SurrogateDiagonalTailChunk000Sub000Block146Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6067
    = surrogateDiagTailX0RatChunk000Sub000Block146Part006

theorem surrogateDiagonalTailChunk000Sub000Block146Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block146Part006CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block146Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block146Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block146Part006CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block146Part006SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block146Part006] using hcert

def TailChunk000Sub000Block146Part007SupportExplicit : Finset ℕ :=
  ([6070] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block146Part007 : ℚ :=
  (873590510575 : ℚ) / 86329121377241088

def SurrogateDiagonalTailChunk000Sub000Block146Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6070
    = surrogateDiagTailX0RatChunk000Sub000Block146Part007

theorem surrogateDiagonalTailChunk000Sub000Block146Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block146Part007CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block146Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block146Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block146Part007CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block146Part007SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block146Part007] using hcert

def TailChunk000Sub000Block146Part008SupportExplicit : Finset ℕ :=
  ([6071] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block146Part008 : ℚ :=
  (698092779275 : ℚ) / 815031239299209216

def SurrogateDiagonalTailChunk000Sub000Block146Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6071
    = surrogateDiagTailX0RatChunk000Sub000Block146Part008

theorem surrogateDiagonalTailChunk000Sub000Block146Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block146Part008CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block146Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block146Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block146Part008CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block146Part008SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block146Part008] using hcert

def TailChunk000Sub000Block146Part009SupportExplicit : Finset ℕ :=
  ([6073] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block146Part009 : ℚ :=
  (576270765625 : ℚ) / 849755372607263232

def SurrogateDiagonalTailChunk000Sub000Block146Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6073
    = surrogateDiagTailX0RatChunk000Sub000Block146Part009

theorem surrogateDiagonalTailChunk000Sub000Block146Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block146Part009CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block146Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block146Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block146Part009CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block146Part009SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block146Part009] using hcert

def TailChunk000Sub000Block146Part010SupportExplicit : Finset ℕ :=
  ([6074] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block146Part010 : ℚ :=
  (1152690540775 : ℚ) / 212438843151815808

def SurrogateDiagonalTailChunk000Sub000Block146Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6074
    = surrogateDiagTailX0RatChunk000Sub000Block146Part010

theorem surrogateDiagonalTailChunk000Sub000Block146Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block146Part010CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block146Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block146Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block146Part010CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block146Part010SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block146Part010] using hcert

def TailChunk000Sub000Block146Part011SupportExplicit : Finset ℕ :=
  ([6077] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block146Part011 : ℚ :=
  (62122211225 : ℚ) / 85081868588563488

def SurrogateDiagonalTailChunk000Sub000Block146Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6077
    = surrogateDiagTailX0RatChunk000Sub000Block146Part011

theorem surrogateDiagonalTailChunk000Sub000Block146Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block146Part011CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block146Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block146Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block146Part011CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block146Part011SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block146Part011] using hcert

def TailChunk000Sub000Block146Part012SupportExplicit : Finset ℕ :=
  ([6078] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block146Part012 : ℚ :=
  (704851555075 : ℚ) / 41963228276901888

def SurrogateDiagonalTailChunk000Sub000Block146Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6078
    = surrogateDiagTailX0RatChunk000Sub000Block146Part012

theorem surrogateDiagonalTailChunk000Sub000Block146Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block146Part012CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block146Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block146Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block146Part012CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block146Part012SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block146Part012] using hcert

def TailChunk000Sub000Block146Part013SupportExplicit : Finset ℕ :=
  ([6079] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block146Part013 : ℚ :=
  (577410015625 : ℚ) / 853119071110692882

def SurrogateDiagonalTailChunk000Sub000Block146Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6079
    = surrogateDiagTailX0RatChunk000Sub000Block146Part013

theorem surrogateDiagonalTailChunk000Sub000Block146Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block146Part013CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block146Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block146Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block146Part013CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block146Part013SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block146Part013] using hcert

def TailChunk000Sub000Block146Part014SupportExplicit : Finset ℕ :=
  ([6081] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block146Part014 : ℚ :=
  (153987825 : ℚ) / 67393460259904

def SurrogateDiagonalTailChunk000Sub000Block146Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6081
    = surrogateDiagTailX0RatChunk000Sub000Block146Part014

theorem surrogateDiagonalTailChunk000Sub000Block146Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block146Part014CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block146Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block146Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block146Part014CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block146Part014SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block146Part014] using hcert

def TailChunk000Sub000Block146Part015SupportExplicit : Finset ℕ :=
  ([6082] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block146Part015 : ℚ :=
  (46229157319 : ℚ) / 8542425199411200

def SurrogateDiagonalTailChunk000Sub000Block146Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6082
    = surrogateDiagTailX0RatChunk000Sub000Block146Part015

theorem surrogateDiagonalTailChunk000Sub000Block146Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block146Part015CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block146Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block146Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block146Part015CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block146Part015SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block146Part015] using hcert

def TailChunk000Sub000Block146Part016SupportExplicit : Finset ℕ :=
  ([6083] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block146Part016 : ℚ :=
  (2132487509 : ℚ) / 1499409589953600

def SurrogateDiagonalTailChunk000Sub000Block146Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6083
    = surrogateDiagTailX0RatChunk000Sub000Block146Part016

theorem surrogateDiagonalTailChunk000Sub000Block146Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block146Part016CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block146Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block146Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block146Part016CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block146Part016SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block146Part016] using hcert

def TailChunk000Sub000Block146Part017SupportExplicit : Finset ℕ :=
  ([6085] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block146Part017 : ℚ :=
  (61782038025 : ℚ) / 233265157445255168

def SurrogateDiagonalTailChunk000Sub000Block146Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6085
    = surrogateDiagTailX0RatChunk000Sub000Block146Part017

theorem surrogateDiagonalTailChunk000Sub000Block146Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block146Part017CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block146Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block146Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block146Part017CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block146Part017SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block146Part017] using hcert

def TailChunk000Sub000Block146Part018SupportExplicit : Finset ℕ :=
  ([6086] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block146Part018 : ℚ :=
  (70682001725 : ℚ) / 20563489406386176

def SurrogateDiagonalTailChunk000Sub000Block146Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6086
    = surrogateDiagTailX0RatChunk000Sub000Block146Part018

theorem surrogateDiagonalTailChunk000Sub000Block146Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block146Part018CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block146Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block146Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block146Part018CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block146Part018SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block146Part018] using hcert

def TailChunk000Sub000Block146Part019SupportExplicit : Finset ℕ :=
  ([6087] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block146Part019 : ℚ :=
  (257310051275 : ℚ) / 338367504582042624

def SurrogateDiagonalTailChunk000Sub000Block146Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6087
    = surrogateDiagTailX0RatChunk000Sub000Block146Part019

theorem surrogateDiagonalTailChunk000Sub000Block146Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block146Part019CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block146Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block146Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block146Part019CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block146Part019SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block146Part019] using hcert

def TailChunk000Sub000Block146Part020SupportExplicit : Finset ℕ :=
  ([6089] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block146Part020 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub000Block146Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6089
    = surrogateDiagTailX0RatChunk000Sub000Block146Part020

theorem surrogateDiagonalTailChunk000Sub000Block146Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block146Part020CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block146Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block146Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block146Part020CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block146Part020SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block146Part020] using hcert

def TailChunk000Sub000Block146Part021SupportExplicit : Finset ℕ :=
  ([6090] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block146Part021 : ℚ :=
  (6829390625 : ℚ) / 151088070131712

def SurrogateDiagonalTailChunk000Sub000Block146Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6090
    = surrogateDiagTailX0RatChunk000Sub000Block146Part021

theorem surrogateDiagonalTailChunk000Sub000Block146Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block146Part021CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block146Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block146Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block146Part021CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block146Part021SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block146Part021] using hcert

def TailChunk000Sub000Block146Part022SupportExplicit : Finset ℕ :=
  ([6091] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block146Part022 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub000Block146Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6091
    = surrogateDiagTailX0RatChunk000Sub000Block146Part022

theorem surrogateDiagonalTailChunk000Sub000Block146Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block146Part022CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block146Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block146Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block146Part022CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block146Part022SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block146Part022] using hcert

def TailChunk000Sub000Block146Part023SupportExplicit : Finset ℕ :=
  ([6094] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block146Part023 : ℚ :=
  (121787479 : ℚ) / 31543171372800

def SurrogateDiagonalTailChunk000Sub000Block146Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6094
    = surrogateDiagTailX0RatChunk000Sub000Block146Part023

theorem surrogateDiagonalTailChunk000Sub000Block146Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block146Part023CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block146Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block146Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block146Part023CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block146Part023SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block146Part023] using hcert

def TailChunk000Sub000Block146Part024SupportExplicit : Finset ℕ :=
  ([6095] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block146Part024 : ℚ :=
  (139362476925 : ℚ) / 365468261478301696

def SurrogateDiagonalTailChunk000Sub000Block146Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6095
    = surrogateDiagTailX0RatChunk000Sub000Block146Part024

theorem surrogateDiagonalTailChunk000Sub000Block146Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block146Part024CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block146Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block146Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block146Part024CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block146Part024SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block146Part024] using hcert

def surrogateDiagonalTailChunk000Sub000Block146HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block146Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block146Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block146Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block146Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block146Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block146Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block146Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block146Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block146Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block146Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block146Head : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block146Part000
    + surrogateDiagTailX0RatChunk000Sub000Block146Part001
    + surrogateDiagTailX0RatChunk000Sub000Block146Part002
    + surrogateDiagTailX0RatChunk000Sub000Block146Part003
    + surrogateDiagTailX0RatChunk000Sub000Block146Part004
    + surrogateDiagTailX0RatChunk000Sub000Block146Part005
    + surrogateDiagTailX0RatChunk000Sub000Block146Part006
    + surrogateDiagTailX0RatChunk000Sub000Block146Part007
    + surrogateDiagTailX0RatChunk000Sub000Block146Part008
    + surrogateDiagTailX0RatChunk000Sub000Block146Part009

def surrogateDiagonalTailChunk000Sub000Block146MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block146Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block146Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block146Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block146Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block146Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block146Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block146Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block146Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block146Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block146Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block146Mid : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block146Part010
    + surrogateDiagTailX0RatChunk000Sub000Block146Part011
    + surrogateDiagTailX0RatChunk000Sub000Block146Part012
    + surrogateDiagTailX0RatChunk000Sub000Block146Part013
    + surrogateDiagTailX0RatChunk000Sub000Block146Part014
    + surrogateDiagTailX0RatChunk000Sub000Block146Part015
    + surrogateDiagTailX0RatChunk000Sub000Block146Part016
    + surrogateDiagTailX0RatChunk000Sub000Block146Part017
    + surrogateDiagTailX0RatChunk000Sub000Block146Part018
    + surrogateDiagTailX0RatChunk000Sub000Block146Part019

def surrogateDiagonalTailChunk000Sub000Block146TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block146Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block146Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block146Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block146Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block146Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block146Tail : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block146Part020
    + surrogateDiagTailX0RatChunk000Sub000Block146Part021
    + surrogateDiagTailX0RatChunk000Sub000Block146Part022
    + surrogateDiagTailX0RatChunk000Sub000Block146Part023
    + surrogateDiagTailX0RatChunk000Sub000Block146Part024

def surrogateDiagonalTailChunk000Sub000Block146Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub000Block146HeadSum X0
    + surrogateDiagonalTailChunk000Sub000Block146MidSum X0
    + surrogateDiagonalTailChunk000Sub000Block146TailSum X0

def surrogateDiagTailX0RatChunk000Sub000Block146 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block146Part000
    + surrogateDiagTailX0RatChunk000Sub000Block146Part001
    + surrogateDiagTailX0RatChunk000Sub000Block146Part002
    + surrogateDiagTailX0RatChunk000Sub000Block146Part003
    + surrogateDiagTailX0RatChunk000Sub000Block146Part004
    + surrogateDiagTailX0RatChunk000Sub000Block146Part005
    + surrogateDiagTailX0RatChunk000Sub000Block146Part006
    + surrogateDiagTailX0RatChunk000Sub000Block146Part007
    + surrogateDiagTailX0RatChunk000Sub000Block146Part008
    + surrogateDiagTailX0RatChunk000Sub000Block146Part009
    + surrogateDiagTailX0RatChunk000Sub000Block146Part010
    + surrogateDiagTailX0RatChunk000Sub000Block146Part011
    + surrogateDiagTailX0RatChunk000Sub000Block146Part012
    + surrogateDiagTailX0RatChunk000Sub000Block146Part013
    + surrogateDiagTailX0RatChunk000Sub000Block146Part014
    + surrogateDiagTailX0RatChunk000Sub000Block146Part015
    + surrogateDiagTailX0RatChunk000Sub000Block146Part016
    + surrogateDiagTailX0RatChunk000Sub000Block146Part017
    + surrogateDiagTailX0RatChunk000Sub000Block146Part018
    + surrogateDiagTailX0RatChunk000Sub000Block146Part019
    + surrogateDiagTailX0RatChunk000Sub000Block146Part020
    + surrogateDiagTailX0RatChunk000Sub000Block146Part021
    + surrogateDiagTailX0RatChunk000Sub000Block146Part022
    + surrogateDiagTailX0RatChunk000Sub000Block146Part023
    + surrogateDiagTailX0RatChunk000Sub000Block146Part024

theorem surrogateDiagTailX0RatChunk000Sub000Block146_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk000Sub000Block146Head + surrogateDiagTailX0RatChunk000Sub000Block146Mid + surrogateDiagTailX0RatChunk000Sub000Block146Tail =
      surrogateDiagTailX0RatChunk000Sub000Block146 := by
  unfold surrogateDiagTailX0RatChunk000Sub000Block146Head surrogateDiagTailX0RatChunk000Sub000Block146Mid surrogateDiagTailX0RatChunk000Sub000Block146Tail surrogateDiagTailX0RatChunk000Sub000Block146
  ring

def SurrogateDiagonalTailChunk000Sub000Block146HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block146HeadSum X0 = surrogateDiagTailX0RatChunk000Sub000Block146Head

def SurrogateDiagonalTailChunk000Sub000Block146MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block146MidSum X0 = surrogateDiagTailX0RatChunk000Sub000Block146Mid

def SurrogateDiagonalTailChunk000Sub000Block146TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block146TailSum X0 = surrogateDiagTailX0RatChunk000Sub000Block146Tail

theorem surrogateDiagonalTailChunk000Sub000Block146_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk000Sub000Block146HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk000Sub000Block146MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk000Sub000Block146TailCertificateAt X0) :
    surrogateDiagonalTailChunk000Sub000Block146Sum X0 = surrogateDiagTailX0RatChunk000Sub000Block146 := by
  unfold SurrogateDiagonalTailChunk000Sub000Block146HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk000Sub000Block146MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk000Sub000Block146TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk000Sub000Block146Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk000Sub000Block146_eq_head_add_mid_add_tail

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

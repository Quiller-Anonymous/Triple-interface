import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0TailPilot25

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

open scoped BigOperators

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

/- Generated direct-term certificate blocks for tail chunk 001, subchunk 000, blocks [160,170). -/

/-- Block 160 covers tail-support indices [14000,14025) and q from 23081 to 23118. -/

def TailChunk001Sub000Block160Part000SupportExplicit : Finset ℕ :=
  ([23081] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block160Part000 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block160Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23081
    = surrogateDiagTailX0RatChunk001Sub000Block160Part000

theorem surrogateDiagonalTailChunk001Sub000Block160Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block160Part000CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block160Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block160Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block160Part000CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block160Part000SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block160Part000] using hcert

def TailChunk001Sub000Block160Part001SupportExplicit : Finset ℕ :=
  ([23082] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block160Part001 : ℚ :=
  (924609723725 : ℚ) / 4376772423942018624

def SurrogateDiagonalTailChunk001Sub000Block160Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23082
    = surrogateDiagTailX0RatChunk001Sub000Block160Part001

theorem surrogateDiagonalTailChunk001Sub000Block160Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block160Part001CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block160Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block160Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block160Part001CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block160Part001SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block160Part001] using hcert

def TailChunk001Sub000Block160Part002SupportExplicit : Finset ℕ :=
  ([23083] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block160Part002 : ℚ :=
  (6808273399 : ℚ) / 25543010258551603200

def SurrogateDiagonalTailChunk001Sub000Block160Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23083
    = surrogateDiagTailX0RatChunk001Sub000Block160Part002

theorem surrogateDiagonalTailChunk001Sub000Block160Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block160Part002CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block160Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block160Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block160Part002CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block160Part002SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block160Part002] using hcert

def TailChunk001Sub000Block160Part003SupportExplicit : Finset ℕ :=
  ([23086] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block160Part003 : ℚ :=
  (35638378375 : ℚ) / 1002130356805042176

def SurrogateDiagonalTailChunk001Sub000Block160Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23086
    = surrogateDiagTailX0RatChunk001Sub000Block160Part003

theorem surrogateDiagonalTailChunk001Sub000Block160Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block160Part003CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block160Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block160Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block160Part003CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block160Part003SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block160Part003] using hcert

def TailChunk001Sub000Block160Part004SupportExplicit : Finset ℕ :=
  ([23087] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block160Part004 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block160Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23087
    = surrogateDiagTailX0RatChunk001Sub000Block160Part004

theorem surrogateDiagonalTailChunk001Sub000Block160Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block160Part004CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block160Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block160Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block160Part004CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block160Part004SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block160Part004] using hcert

def TailChunk001Sub000Block160Part005SupportExplicit : Finset ℕ :=
  ([23089] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block160Part005 : ℚ :=
  (691522757 : ℚ) / 605562268636580100

def SurrogateDiagonalTailChunk001Sub000Block160Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23089
    = surrogateDiagTailX0RatChunk001Sub000Block160Part005

theorem surrogateDiagonalTailChunk001Sub000Block160Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block160Part005CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block160Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block160Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block160Part005CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block160Part005SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block160Part005] using hcert

def TailChunk001Sub000Block160Part006SupportExplicit : Finset ℕ :=
  ([23090] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block160Part006 : ℚ :=
  (666975260725 : ℚ) / 18163939309126975488

def SurrogateDiagonalTailChunk001Sub000Block160Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23090
    = surrogateDiagTailX0RatChunk001Sub000Block160Part006

theorem surrogateDiagonalTailChunk001Sub000Block160Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block160Part006CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block160Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block160Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block160Part006CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block160Part006SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block160Part006] using hcert

def TailChunk001Sub000Block160Part007SupportExplicit : Finset ℕ :=
  ([23091] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block160Part007 : ℚ :=
  (402934294325 : ℚ) / 13886138830706214912

def SurrogateDiagonalTailChunk001Sub000Block160Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23091
    = surrogateDiagTailX0RatChunk001Sub000Block160Part007

theorem surrogateDiagonalTailChunk001Sub000Block160Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block160Part007CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block160Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block160Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block160Part007CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block160Part007SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block160Part007] using hcert

def TailChunk001Sub000Block160Part008SupportExplicit : Finset ℕ :=
  ([23093] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block160Part008 : ℚ :=
  (680601716075 : ℚ) / 191692212488496350784

def SurrogateDiagonalTailChunk001Sub000Block160Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23093
    = surrogateDiagTailX0RatChunk001Sub000Block160Part008

theorem surrogateDiagonalTailChunk001Sub000Block160Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block160Part008CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block160Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block160Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block160Part008CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block160Part008SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block160Part008] using hcert

def TailChunk001Sub000Block160Part009SupportExplicit : Finset ℕ :=
  ([23095] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block160Part009 : ℚ :=
  (959070809 : ℚ) / 165846933403729920

def SurrogateDiagonalTailChunk001Sub000Block160Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23095
    = surrogateDiagTailX0RatChunk001Sub000Block160Part009

theorem surrogateDiagonalTailChunk001Sub000Block160Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block160Part009CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block160Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block160Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block160Part009CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block160Part009SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block160Part009] using hcert

def TailChunk001Sub000Block160Part010SupportExplicit : Finset ℕ :=
  ([23097] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block160Part010 : ℚ :=
  (1852162622525 : ℚ) / 70247111787307174464

def SurrogateDiagonalTailChunk001Sub000Block160Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23097
    = surrogateDiagTailX0RatChunk001Sub000Block160Part010

theorem surrogateDiagonalTailChunk001Sub000Block160Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block160Part010CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block160Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block160Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block160Part010CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block160Part010SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block160Part010] using hcert

def TailChunk001Sub000Block160Part011SupportExplicit : Finset ℕ :=
  ([23098] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block160Part011 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block160Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23098
    = surrogateDiagTailX0RatChunk001Sub000Block160Part011

theorem surrogateDiagonalTailChunk001Sub000Block160Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block160Part011CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block160Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block160Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block160Part011CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block160Part011SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block160Part011] using hcert

def TailChunk001Sub000Block160Part012SupportExplicit : Finset ℕ :=
  ([23099] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block160Part012 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block160Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23099
    = surrogateDiagTailX0RatChunk001Sub000Block160Part012

theorem surrogateDiagonalTailChunk001Sub000Block160Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block160Part012CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block160Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block160Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block160Part012CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block160Part012SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block160Part012] using hcert

def TailChunk001Sub000Block160Part013SupportExplicit : Finset ℕ :=
  ([23101] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block160Part013 : ℚ :=
  (8039521175 : ℚ) / 6970950022418399232

def SurrogateDiagonalTailChunk001Sub000Block160Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23101
    = surrogateDiagTailX0RatChunk001Sub000Block160Part013

theorem surrogateDiagonalTailChunk001Sub000Block160Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block160Part013CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block160Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block160Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block160Part013CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block160Part013SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block160Part013] using hcert

def TailChunk001Sub000Block160Part014SupportExplicit : Finset ℕ :=
  ([23102] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block160Part014 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block160Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23102
    = surrogateDiagTailX0RatChunk001Sub000Block160Part014

theorem surrogateDiagonalTailChunk001Sub000Block160Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block160Part014CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block160Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block160Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block160Part014CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block160Part014SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block160Part014] using hcert

def TailChunk001Sub000Block160Part015SupportExplicit : Finset ℕ :=
  ([23105] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block160Part015 : ℚ :=
  (10682204879 : ℚ) / 2333053583576432640

def SurrogateDiagonalTailChunk001Sub000Block160Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23105
    = surrogateDiagTailX0RatChunk001Sub000Block160Part015

theorem surrogateDiagonalTailChunk001Sub000Block160Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block160Part015CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block160Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block160Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block160Part015CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block160Part015SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block160Part015] using hcert

def TailChunk001Sub000Block160Part016SupportExplicit : Finset ℕ :=
  ([23106] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block160Part016 : ℚ :=
  (37061333549 : ℚ) / 175800358041000000

def SurrogateDiagonalTailChunk001Sub000Block160Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23106
    = surrogateDiagTailX0RatChunk001Sub000Block160Part016

theorem surrogateDiagonalTailChunk001Sub000Block160Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block160Part016CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block160Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block160Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block160Part016CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block160Part016SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block160Part016] using hcert

def TailChunk001Sub000Block160Part017SupportExplicit : Finset ℕ :=
  ([23107] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block160Part017 : ℚ :=
  (27299996593 : ℚ) / 15372610067232000000

def SurrogateDiagonalTailChunk001Sub000Block160Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23107
    = surrogateDiagTailX0RatChunk001Sub000Block160Part017

theorem surrogateDiagonalTailChunk001Sub000Block160Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block160Part017CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block160Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block160Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block160Part017CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block160Part017SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block160Part017] using hcert

def TailChunk001Sub000Block160Part018SupportExplicit : Finset ℕ :=
  ([23109] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block160Part018 : ℚ :=
  (1854087622475 : ℚ) / 70393231575277145664

def SurrogateDiagonalTailChunk001Sub000Block160Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23109
    = surrogateDiagTailX0RatChunk001Sub000Block160Part018

theorem surrogateDiagonalTailChunk001Sub000Block160Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block160Part018CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block160Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block160Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block160Part018CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block160Part018SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block160Part018] using hcert

def TailChunk001Sub000Block160Part019SupportExplicit : Finset ℕ :=
  ([23110] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block160Part019 : ℚ :=
  (8908393723 : ℚ) / 243026414955878400

def SurrogateDiagonalTailChunk001Sub000Block160Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23110
    = surrogateDiagTailX0RatChunk001Sub000Block160Part019

theorem surrogateDiagonalTailChunk001Sub000Block160Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block160Part019CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block160Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block160Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block160Part019CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block160Part019SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block160Part019] using hcert

def TailChunk001Sub000Block160Part020SupportExplicit : Finset ℕ :=
  ([23113] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block160Part020 : ℚ :=
  (246100412575 : ℚ) / 617037068708302061568

def SurrogateDiagonalTailChunk001Sub000Block160Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23113
    = surrogateDiagTailX0RatChunk001Sub000Block160Part020

theorem surrogateDiagonalTailChunk001Sub000Block160Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block160Part020CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block160Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block160Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block160Part020CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block160Part020SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block160Part020] using hcert

def TailChunk001Sub000Block160Part021SupportExplicit : Finset ℕ :=
  ([23114] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block160Part021 : ℚ :=
  (77222909725 : ℚ) / 1881899884660948992

def SurrogateDiagonalTailChunk001Sub000Block160Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23114
    = surrogateDiagTailX0RatChunk001Sub000Block160Part021

theorem surrogateDiagonalTailChunk001Sub000Block160Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block160Part021CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block160Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block160Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block160Part021CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block160Part021SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block160Part021] using hcert

def TailChunk001Sub000Block160Part022SupportExplicit : Finset ℕ :=
  ([23115] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block160Part022 : ℚ :=
  (744628649725 : ℚ) / 11381336948652244992

def SurrogateDiagonalTailChunk001Sub000Block160Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23115
    = surrogateDiagTailX0RatChunk001Sub000Block160Part022

theorem surrogateDiagonalTailChunk001Sub000Block160Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block160Part022CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block160Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block160Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block160Part022CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block160Part022SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block160Part022] using hcert

def TailChunk001Sub000Block160Part023SupportExplicit : Finset ℕ :=
  ([23117] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block160Part023 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block160Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23117
    = surrogateDiagTailX0RatChunk001Sub000Block160Part023

theorem surrogateDiagonalTailChunk001Sub000Block160Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block160Part023CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block160Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block160Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block160Part023CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block160Part023SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block160Part023] using hcert

def TailChunk001Sub000Block160Part024SupportExplicit : Finset ℕ :=
  ([23118] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block160Part024 : ℚ :=
  (927495896075 : ℚ) / 4404148555844772864

def SurrogateDiagonalTailChunk001Sub000Block160Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23118
    = surrogateDiagTailX0RatChunk001Sub000Block160Part024

theorem surrogateDiagonalTailChunk001Sub000Block160Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block160Part024CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block160Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block160Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block160Part024CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block160Part024SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block160Part024] using hcert

def surrogateDiagonalTailChunk001Sub000Block160HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block160Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block160Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block160Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block160Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block160Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block160Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block160Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block160Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block160Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block160Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block160Head : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block160Part000
    + surrogateDiagTailX0RatChunk001Sub000Block160Part001
    + surrogateDiagTailX0RatChunk001Sub000Block160Part002
    + surrogateDiagTailX0RatChunk001Sub000Block160Part003
    + surrogateDiagTailX0RatChunk001Sub000Block160Part004
    + surrogateDiagTailX0RatChunk001Sub000Block160Part005
    + surrogateDiagTailX0RatChunk001Sub000Block160Part006
    + surrogateDiagTailX0RatChunk001Sub000Block160Part007
    + surrogateDiagTailX0RatChunk001Sub000Block160Part008
    + surrogateDiagTailX0RatChunk001Sub000Block160Part009

def surrogateDiagonalTailChunk001Sub000Block160MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block160Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block160Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block160Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block160Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block160Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block160Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block160Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block160Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block160Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block160Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block160Mid : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block160Part010
    + surrogateDiagTailX0RatChunk001Sub000Block160Part011
    + surrogateDiagTailX0RatChunk001Sub000Block160Part012
    + surrogateDiagTailX0RatChunk001Sub000Block160Part013
    + surrogateDiagTailX0RatChunk001Sub000Block160Part014
    + surrogateDiagTailX0RatChunk001Sub000Block160Part015
    + surrogateDiagTailX0RatChunk001Sub000Block160Part016
    + surrogateDiagTailX0RatChunk001Sub000Block160Part017
    + surrogateDiagTailX0RatChunk001Sub000Block160Part018
    + surrogateDiagTailX0RatChunk001Sub000Block160Part019

def surrogateDiagonalTailChunk001Sub000Block160TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block160Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block160Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block160Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block160Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block160Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block160Tail : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block160Part020
    + surrogateDiagTailX0RatChunk001Sub000Block160Part021
    + surrogateDiagTailX0RatChunk001Sub000Block160Part022
    + surrogateDiagTailX0RatChunk001Sub000Block160Part023
    + surrogateDiagTailX0RatChunk001Sub000Block160Part024

def surrogateDiagonalTailChunk001Sub000Block160Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk001Sub000Block160HeadSum X0
    + surrogateDiagonalTailChunk001Sub000Block160MidSum X0
    + surrogateDiagonalTailChunk001Sub000Block160TailSum X0

def surrogateDiagTailX0RatChunk001Sub000Block160 : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block160Part000
    + surrogateDiagTailX0RatChunk001Sub000Block160Part001
    + surrogateDiagTailX0RatChunk001Sub000Block160Part002
    + surrogateDiagTailX0RatChunk001Sub000Block160Part003
    + surrogateDiagTailX0RatChunk001Sub000Block160Part004
    + surrogateDiagTailX0RatChunk001Sub000Block160Part005
    + surrogateDiagTailX0RatChunk001Sub000Block160Part006
    + surrogateDiagTailX0RatChunk001Sub000Block160Part007
    + surrogateDiagTailX0RatChunk001Sub000Block160Part008
    + surrogateDiagTailX0RatChunk001Sub000Block160Part009
    + surrogateDiagTailX0RatChunk001Sub000Block160Part010
    + surrogateDiagTailX0RatChunk001Sub000Block160Part011
    + surrogateDiagTailX0RatChunk001Sub000Block160Part012
    + surrogateDiagTailX0RatChunk001Sub000Block160Part013
    + surrogateDiagTailX0RatChunk001Sub000Block160Part014
    + surrogateDiagTailX0RatChunk001Sub000Block160Part015
    + surrogateDiagTailX0RatChunk001Sub000Block160Part016
    + surrogateDiagTailX0RatChunk001Sub000Block160Part017
    + surrogateDiagTailX0RatChunk001Sub000Block160Part018
    + surrogateDiagTailX0RatChunk001Sub000Block160Part019
    + surrogateDiagTailX0RatChunk001Sub000Block160Part020
    + surrogateDiagTailX0RatChunk001Sub000Block160Part021
    + surrogateDiagTailX0RatChunk001Sub000Block160Part022
    + surrogateDiagTailX0RatChunk001Sub000Block160Part023
    + surrogateDiagTailX0RatChunk001Sub000Block160Part024

theorem surrogateDiagTailX0RatChunk001Sub000Block160_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk001Sub000Block160Head + surrogateDiagTailX0RatChunk001Sub000Block160Mid + surrogateDiagTailX0RatChunk001Sub000Block160Tail =
      surrogateDiagTailX0RatChunk001Sub000Block160 := by
  unfold surrogateDiagTailX0RatChunk001Sub000Block160Head surrogateDiagTailX0RatChunk001Sub000Block160Mid surrogateDiagTailX0RatChunk001Sub000Block160Tail surrogateDiagTailX0RatChunk001Sub000Block160
  ring

def SurrogateDiagonalTailChunk001Sub000Block160HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block160HeadSum X0 = surrogateDiagTailX0RatChunk001Sub000Block160Head

def SurrogateDiagonalTailChunk001Sub000Block160MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block160MidSum X0 = surrogateDiagTailX0RatChunk001Sub000Block160Mid

def SurrogateDiagonalTailChunk001Sub000Block160TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block160TailSum X0 = surrogateDiagTailX0RatChunk001Sub000Block160Tail

theorem surrogateDiagonalTailChunk001Sub000Block160_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk001Sub000Block160HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk001Sub000Block160MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk001Sub000Block160TailCertificateAt X0) :
    surrogateDiagonalTailChunk001Sub000Block160Sum X0 = surrogateDiagTailX0RatChunk001Sub000Block160 := by
  unfold SurrogateDiagonalTailChunk001Sub000Block160HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk001Sub000Block160MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk001Sub000Block160TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk001Sub000Block160Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk001Sub000Block160_eq_head_add_mid_add_tail

/-- Block 161 covers tail-support indices [14025,14050) and q from 23119 to 23161. -/

def TailChunk001Sub000Block161Part000SupportExplicit : Finset ℕ :=
  ([23119] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block161Part000 : ℚ :=
  (5382931207 : ℚ) / 26464217128044595200

def SurrogateDiagonalTailChunk001Sub000Block161Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23119
    = surrogateDiagTailX0RatChunk001Sub000Block161Part000

theorem surrogateDiagonalTailChunk001Sub000Block161Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block161Part000CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block161Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block161Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block161Part000CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block161Part000SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block161Part000] using hcert

def TailChunk001Sub000Block161Part001SupportExplicit : Finset ℕ :=
  ([23122] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block161Part001 : ℚ :=
  (463176841 : ℚ) / 40524978375000000

def SurrogateDiagonalTailChunk001Sub000Block161Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23122
    = surrogateDiagTailX0RatChunk001Sub000Block161Part001

theorem surrogateDiagonalTailChunk001Sub000Block161Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block161Part001CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block161Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block161Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block161Part001CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block161Part001SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block161Part001] using hcert

def TailChunk001Sub000Block161Part002SupportExplicit : Finset ℕ :=
  ([23123] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block161Part002 : ℚ :=
  (19740260575 : ℚ) / 30206303249966825472

def SurrogateDiagonalTailChunk001Sub000Block161Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23123
    = surrogateDiagTailX0RatChunk001Sub000Block161Part002

theorem surrogateDiagonalTailChunk001Sub000Block161Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block161Part002CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block161Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block161Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block161Part002CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block161Part002SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block161Part002] using hcert

def TailChunk001Sub000Block161Part003SupportExplicit : Finset ℕ :=
  ([23126] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block161Part003 : ℚ :=
  (540118211 : ℚ) / 172385653340620800

def SurrogateDiagonalTailChunk001Sub000Block161Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23126
    = surrogateDiagTailX0RatChunk001Sub000Block161Part003

theorem surrogateDiagonalTailChunk001Sub000Block161Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block161Part003CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block161Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block161Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block161Part003CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block161Part003SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block161Part003] using hcert

def TailChunk001Sub000Block161Part004SupportExplicit : Finset ℕ :=
  ([23127] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block161Part004 : ℚ :=
  (71803662125 : ℚ) / 2122840747567742976

def SurrogateDiagonalTailChunk001Sub000Block161Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23127
    = surrogateDiagTailX0RatChunk001Sub000Block161Part004

theorem surrogateDiagonalTailChunk001Sub000Block161Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block161Part004CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block161Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block161Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block161Part004CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block161Part004SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block161Part004] using hcert

def TailChunk001Sub000Block161Part005SupportExplicit : Finset ℕ :=
  ([23129] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block161Part005 : ℚ :=
  (1027332001 : ℚ) / 6757191808128000000

def SurrogateDiagonalTailChunk001Sub000Block161Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23129
    = surrogateDiagTailX0RatChunk001Sub000Block161Part005

theorem surrogateDiagonalTailChunk001Sub000Block161Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block161Part005CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block161Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block161Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block161Part005CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block161Part005SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block161Part005] using hcert

def TailChunk001Sub000Block161Part006SupportExplicit : Finset ℕ :=
  ([23131] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block161Part006 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block161Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23131
    = surrogateDiagTailX0RatChunk001Sub000Block161Part006

theorem surrogateDiagonalTailChunk001Sub000Block161Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block161Part006CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block161Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block161Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block161Part006CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block161Part006SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block161Part006] using hcert

def TailChunk001Sub000Block161Part007SupportExplicit : Finset ℕ :=
  ([23133] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block161Part007 : ℚ :=
  (2822235827 : ℚ) / 76847366400000000

def SurrogateDiagonalTailChunk001Sub000Block161Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23133
    = surrogateDiagTailX0RatChunk001Sub000Block161Part007

theorem surrogateDiagonalTailChunk001Sub000Block161Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block161Part007CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block161Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block161Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block161Part007CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block161Part007SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block161Part007] using hcert

def TailChunk001Sub000Block161Part008SupportExplicit : Finset ℕ :=
  ([23134] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block161Part008 : ℚ :=
  (49091818925 : ℚ) / 20069345101996237824

def SurrogateDiagonalTailChunk001Sub000Block161Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23134
    = surrogateDiagTailX0RatChunk001Sub000Block161Part008

theorem surrogateDiagonalTailChunk001Sub000Block161Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block161Part008CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block161Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block161Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block161Part008CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block161Part008SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block161Part008] using hcert

def TailChunk001Sub000Block161Part009SupportExplicit : Finset ℕ :=
  ([23135] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block161Part009 : ℚ :=
  (3119003159 : ℚ) / 314831054176911360

def SurrogateDiagonalTailChunk001Sub000Block161Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23135
    = surrogateDiagTailX0RatChunk001Sub000Block161Part009

theorem surrogateDiagonalTailChunk001Sub000Block161Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block161Part009CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block161Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block161Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block161Part009CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block161Part009SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block161Part009] using hcert

def TailChunk001Sub000Block161Part010SupportExplicit : Finset ℕ :=
  ([23137] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block161Part010 : ℚ :=
  (18684854443 : ℚ) / 22424481720120115200

def SurrogateDiagonalTailChunk001Sub000Block161Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23137
    = surrogateDiagTailX0RatChunk001Sub000Block161Part010

theorem surrogateDiagonalTailChunk001Sub000Block161Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block161Part010CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block161Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block161Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block161Part010CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block161Part010SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block161Part010] using hcert

def TailChunk001Sub000Block161Part011SupportExplicit : Finset ℕ :=
  ([23138] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block161Part011 : ℚ :=
  (148389619375 : ℚ) / 37199101552254162048

def SurrogateDiagonalTailChunk001Sub000Block161Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23138
    = surrogateDiagTailX0RatChunk001Sub000Block161Part011

theorem surrogateDiagonalTailChunk001Sub000Block161Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block161Part011CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block161Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block161Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block161Part011CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block161Part011SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block161Part011] using hcert

def TailChunk001Sub000Block161Part012SupportExplicit : Finset ℕ :=
  ([23141] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block161Part012 : ℚ :=
  (60951430625 : ℚ) / 335023429041898389504

def SurrogateDiagonalTailChunk001Sub000Block161Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23141
    = surrogateDiagTailX0RatChunk001Sub000Block161Part012

theorem surrogateDiagonalTailChunk001Sub000Block161Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block161Part012CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block161Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block161Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block161Part012CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block161Part012SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block161Part012] using hcert

def TailChunk001Sub000Block161Part013SupportExplicit : Finset ℕ :=
  ([23142] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block161Part013 : ℚ :=
  (1002754636225 : ℚ) / 3345599794952798208

def SurrogateDiagonalTailChunk001Sub000Block161Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23142
    = surrogateDiagTailX0RatChunk001Sub000Block161Part013

theorem surrogateDiagonalTailChunk001Sub000Block161Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block161Part013CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block161Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block161Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block161Part013CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block161Part013SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block161Part013] using hcert

def TailChunk001Sub000Block161Part014SupportExplicit : Finset ℕ :=
  ([23143] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block161Part014 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block161Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23143
    = surrogateDiagTailX0RatChunk001Sub000Block161Part014

theorem surrogateDiagonalTailChunk001Sub000Block161Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block161Part014CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block161Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block161Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block161Part014CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block161Part014SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block161Part014] using hcert

def TailChunk001Sub000Block161Part015SupportExplicit : Finset ℕ :=
  ([23145] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block161Part015 : ℚ :=
  (780799159375 : ℚ) / 14476524523581284352

def SurrogateDiagonalTailChunk001Sub000Block161Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23145
    = surrogateDiagTailX0RatChunk001Sub000Block161Part015

theorem surrogateDiagonalTailChunk001Sub000Block161Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block161Part015CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block161Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block161Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block161Part015CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block161Part015SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block161Part015] using hcert

def TailChunk001Sub000Block161Part016SupportExplicit : Finset ℕ :=
  ([23146] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block161Part016 : ℚ :=
  (13769669 : ℚ) / 7876255097632320

def SurrogateDiagonalTailChunk001Sub000Block161Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23146
    = surrogateDiagTailX0RatChunk001Sub000Block161Part016

theorem surrogateDiagonalTailChunk001Sub000Block161Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block161Part016CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block161Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block161Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block161Part016CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block161Part016SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block161Part016] using hcert

def TailChunk001Sub000Block161Part017SupportExplicit : Finset ℕ :=
  ([23147] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block161Part017 : ℚ :=
  (57286067825 : ℚ) / 336439268292057375744

def SurrogateDiagonalTailChunk001Sub000Block161Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23147
    = surrogateDiagTailX0RatChunk001Sub000Block161Part017

theorem surrogateDiagonalTailChunk001Sub000Block161Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block161Part017CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block161Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block161Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block161Part017CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block161Part017SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block161Part017] using hcert

def TailChunk001Sub000Block161Part018SupportExplicit : Finset ℕ :=
  ([23149] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block161Part018 : ℚ :=
  (684977165125 : ℚ) / 387117903718810977408

def SurrogateDiagonalTailChunk001Sub000Block161Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23149
    = surrogateDiagTailX0RatChunk001Sub000Block161Part018

theorem surrogateDiagonalTailChunk001Sub000Block161Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block161Part018CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block161Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block161Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block161Part018CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block161Part018SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block161Part018] using hcert

def TailChunk001Sub000Block161Part019SupportExplicit : Finset ℕ :=
  ([23151] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block161Part019 : ℚ :=
  (465208249325 : ℚ) / 17726611651719342336

def SurrogateDiagonalTailChunk001Sub000Block161Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23151
    = surrogateDiagTailX0RatChunk001Sub000Block161Part019

theorem surrogateDiagonalTailChunk001Sub000Block161Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block161Part019CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block161Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block161Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block161Part019CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block161Part019SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block161Part019] using hcert

def TailChunk001Sub000Block161Part020SupportExplicit : Finset ℕ :=
  ([23154] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block161Part020 : ℚ :=
  (480647805425 : ℚ) / 3420034862357151744

def SurrogateDiagonalTailChunk001Sub000Block161Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23154
    = surrogateDiagTailX0RatChunk001Sub000Block161Part020

theorem surrogateDiagonalTailChunk001Sub000Block161Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block161Part020CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block161Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block161Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block161Part020CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block161Part020SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block161Part020] using hcert

def TailChunk001Sub000Block161Part021SupportExplicit : Finset ℕ :=
  ([23155] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block161Part021 : ℚ :=
  (2126514869 : ℚ) / 159350698967040000

def SurrogateDiagonalTailChunk001Sub000Block161Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23155
    = surrogateDiagTailX0RatChunk001Sub000Block161Part021

theorem surrogateDiagonalTailChunk001Sub000Block161Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block161Part021CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block161Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block161Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block161Part021CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block161Part021SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block161Part021] using hcert

def TailChunk001Sub000Block161Part022SupportExplicit : Finset ℕ :=
  ([23158] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block161Part022 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block161Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23158
    = surrogateDiagTailX0RatChunk001Sub000Block161Part022

theorem surrogateDiagonalTailChunk001Sub000Block161Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block161Part022CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block161Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block161Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block161Part022CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block161Part022SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block161Part022] using hcert

def TailChunk001Sub000Block161Part023SupportExplicit : Finset ℕ :=
  ([23159] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block161Part023 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block161Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23159
    = surrogateDiagTailX0RatChunk001Sub000Block161Part023

theorem surrogateDiagonalTailChunk001Sub000Block161Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block161Part023CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block161Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block161Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block161Part023CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block161Part023SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block161Part023] using hcert

def TailChunk001Sub000Block161Part024SupportExplicit : Finset ℕ :=
  ([23161] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block161Part024 : ℚ :=
  (56505416125 : ℚ) / 34584191301333712896

def SurrogateDiagonalTailChunk001Sub000Block161Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23161
    = surrogateDiagTailX0RatChunk001Sub000Block161Part024

theorem surrogateDiagonalTailChunk001Sub000Block161Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block161Part024CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block161Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block161Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block161Part024CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block161Part024SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block161Part024] using hcert

def surrogateDiagonalTailChunk001Sub000Block161HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block161Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block161Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block161Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block161Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block161Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block161Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block161Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block161Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block161Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block161Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block161Head : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block161Part000
    + surrogateDiagTailX0RatChunk001Sub000Block161Part001
    + surrogateDiagTailX0RatChunk001Sub000Block161Part002
    + surrogateDiagTailX0RatChunk001Sub000Block161Part003
    + surrogateDiagTailX0RatChunk001Sub000Block161Part004
    + surrogateDiagTailX0RatChunk001Sub000Block161Part005
    + surrogateDiagTailX0RatChunk001Sub000Block161Part006
    + surrogateDiagTailX0RatChunk001Sub000Block161Part007
    + surrogateDiagTailX0RatChunk001Sub000Block161Part008
    + surrogateDiagTailX0RatChunk001Sub000Block161Part009

def surrogateDiagonalTailChunk001Sub000Block161MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block161Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block161Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block161Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block161Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block161Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block161Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block161Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block161Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block161Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block161Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block161Mid : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block161Part010
    + surrogateDiagTailX0RatChunk001Sub000Block161Part011
    + surrogateDiagTailX0RatChunk001Sub000Block161Part012
    + surrogateDiagTailX0RatChunk001Sub000Block161Part013
    + surrogateDiagTailX0RatChunk001Sub000Block161Part014
    + surrogateDiagTailX0RatChunk001Sub000Block161Part015
    + surrogateDiagTailX0RatChunk001Sub000Block161Part016
    + surrogateDiagTailX0RatChunk001Sub000Block161Part017
    + surrogateDiagTailX0RatChunk001Sub000Block161Part018
    + surrogateDiagTailX0RatChunk001Sub000Block161Part019

def surrogateDiagonalTailChunk001Sub000Block161TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block161Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block161Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block161Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block161Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block161Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block161Tail : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block161Part020
    + surrogateDiagTailX0RatChunk001Sub000Block161Part021
    + surrogateDiagTailX0RatChunk001Sub000Block161Part022
    + surrogateDiagTailX0RatChunk001Sub000Block161Part023
    + surrogateDiagTailX0RatChunk001Sub000Block161Part024

def surrogateDiagonalTailChunk001Sub000Block161Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk001Sub000Block161HeadSum X0
    + surrogateDiagonalTailChunk001Sub000Block161MidSum X0
    + surrogateDiagonalTailChunk001Sub000Block161TailSum X0

def surrogateDiagTailX0RatChunk001Sub000Block161 : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block161Part000
    + surrogateDiagTailX0RatChunk001Sub000Block161Part001
    + surrogateDiagTailX0RatChunk001Sub000Block161Part002
    + surrogateDiagTailX0RatChunk001Sub000Block161Part003
    + surrogateDiagTailX0RatChunk001Sub000Block161Part004
    + surrogateDiagTailX0RatChunk001Sub000Block161Part005
    + surrogateDiagTailX0RatChunk001Sub000Block161Part006
    + surrogateDiagTailX0RatChunk001Sub000Block161Part007
    + surrogateDiagTailX0RatChunk001Sub000Block161Part008
    + surrogateDiagTailX0RatChunk001Sub000Block161Part009
    + surrogateDiagTailX0RatChunk001Sub000Block161Part010
    + surrogateDiagTailX0RatChunk001Sub000Block161Part011
    + surrogateDiagTailX0RatChunk001Sub000Block161Part012
    + surrogateDiagTailX0RatChunk001Sub000Block161Part013
    + surrogateDiagTailX0RatChunk001Sub000Block161Part014
    + surrogateDiagTailX0RatChunk001Sub000Block161Part015
    + surrogateDiagTailX0RatChunk001Sub000Block161Part016
    + surrogateDiagTailX0RatChunk001Sub000Block161Part017
    + surrogateDiagTailX0RatChunk001Sub000Block161Part018
    + surrogateDiagTailX0RatChunk001Sub000Block161Part019
    + surrogateDiagTailX0RatChunk001Sub000Block161Part020
    + surrogateDiagTailX0RatChunk001Sub000Block161Part021
    + surrogateDiagTailX0RatChunk001Sub000Block161Part022
    + surrogateDiagTailX0RatChunk001Sub000Block161Part023
    + surrogateDiagTailX0RatChunk001Sub000Block161Part024

theorem surrogateDiagTailX0RatChunk001Sub000Block161_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk001Sub000Block161Head + surrogateDiagTailX0RatChunk001Sub000Block161Mid + surrogateDiagTailX0RatChunk001Sub000Block161Tail =
      surrogateDiagTailX0RatChunk001Sub000Block161 := by
  unfold surrogateDiagTailX0RatChunk001Sub000Block161Head surrogateDiagTailX0RatChunk001Sub000Block161Mid surrogateDiagTailX0RatChunk001Sub000Block161Tail surrogateDiagTailX0RatChunk001Sub000Block161
  ring

def SurrogateDiagonalTailChunk001Sub000Block161HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block161HeadSum X0 = surrogateDiagTailX0RatChunk001Sub000Block161Head

def SurrogateDiagonalTailChunk001Sub000Block161MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block161MidSum X0 = surrogateDiagTailX0RatChunk001Sub000Block161Mid

def SurrogateDiagonalTailChunk001Sub000Block161TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block161TailSum X0 = surrogateDiagTailX0RatChunk001Sub000Block161Tail

theorem surrogateDiagonalTailChunk001Sub000Block161_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk001Sub000Block161HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk001Sub000Block161MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk001Sub000Block161TailCertificateAt X0) :
    surrogateDiagonalTailChunk001Sub000Block161Sum X0 = surrogateDiagTailX0RatChunk001Sub000Block161 := by
  unfold SurrogateDiagonalTailChunk001Sub000Block161HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk001Sub000Block161MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk001Sub000Block161TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk001Sub000Block161Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk001Sub000Block161_eq_head_add_mid_add_tail

/-- Block 162 covers tail-support indices [14050,14075) and q from 23162 to 23199. -/

def TailChunk001Sub000Block162Part000SupportExplicit : Finset ℕ :=
  ([23162] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block162Part000 : ℚ :=
  (108291091375 : ℚ) / 39797449289315647488

def SurrogateDiagonalTailChunk001Sub000Block162Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23162
    = surrogateDiagTailX0RatChunk001Sub000Block162Part000

theorem surrogateDiagonalTailChunk001Sub000Block162Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block162Part000CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block162Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block162Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block162Part000CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block162Part000SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block162Part000] using hcert

def TailChunk001Sub000Block162Part001SupportExplicit : Finset ℕ :=
  ([23163] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block162Part001 : ℚ :=
  (29552292475 : ℚ) / 708034574702900736

def SurrogateDiagonalTailChunk001Sub000Block162Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23163
    = surrogateDiagTailX0RatChunk001Sub000Block162Part001

theorem surrogateDiagonalTailChunk001Sub000Block162Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block162Part001CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block162Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block162Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block162Part001CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block162Part001SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block162Part001] using hcert

def TailChunk001Sub000Block162Part002SupportExplicit : Finset ℕ :=
  ([23165] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block162Part002 : ℚ :=
  (2568617007 : ℚ) / 245578069547417600

def SurrogateDiagonalTailChunk001Sub000Block162Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23165
    = surrogateDiagTailX0RatChunk001Sub000Block162Part002

theorem surrogateDiagonalTailChunk001Sub000Block162Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block162Part002CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block162Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block162Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block162Part002CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block162Part002SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block162Part002] using hcert

def TailChunk001Sub000Block162Part003SupportExplicit : Finset ℕ :=
  ([23167] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block162Part003 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block162Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23167
    = surrogateDiagTailX0RatChunk001Sub000Block162Part003

theorem surrogateDiagonalTailChunk001Sub000Block162Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block162Part003CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block162Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block162Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block162Part003CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block162Part003SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block162Part003] using hcert

def TailChunk001Sub000Block162Part004SupportExplicit : Finset ℕ :=
  ([23169] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block162Part004 : ℚ :=
  (1863727622225 : ℚ) / 71127252813094530624

def SurrogateDiagonalTailChunk001Sub000Block162Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23169
    = surrogateDiagTailX0RatChunk001Sub000Block162Part004

theorem surrogateDiagonalTailChunk001Sub000Block162Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block162Part004CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block162Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block162Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block162Part004CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block162Part004SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block162Part004] using hcert

def TailChunk001Sub000Block162Part005SupportExplicit : Finset ℕ :=
  ([23170] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block162Part005 : ℚ :=
  (35688765091 : ℚ) / 393538817721139200

def SurrogateDiagonalTailChunk001Sub000Block162Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23170
    = surrogateDiagTailX0RatChunk001Sub000Block162Part005

theorem surrogateDiagonalTailChunk001Sub000Block162Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block162Part005CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block162Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block162Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block162Part005CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block162Part005SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block162Part005] using hcert

def TailChunk001Sub000Block162Part006SupportExplicit : Finset ℕ :=
  ([23171] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block162Part006 : ℚ :=
  (801893110975 : ℚ) / 450993457426436456448

def SurrogateDiagonalTailChunk001Sub000Block162Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23171
    = surrogateDiagTailX0RatChunk001Sub000Block162Part006

theorem surrogateDiagonalTailChunk001Sub000Block162Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block162Part006CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block162Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block162Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block162Part006CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block162Part006SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block162Part006] using hcert

def TailChunk001Sub000Block162Part007SupportExplicit : Finset ℕ :=
  ([23173] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block162Part007 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block162Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23173
    = surrogateDiagTailX0RatChunk001Sub000Block162Part007

theorem surrogateDiagonalTailChunk001Sub000Block162Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block162Part007CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block162Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block162Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block162Part007CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block162Part007SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block162Part007] using hcert

def TailChunk001Sub000Block162Part008SupportExplicit : Finset ℕ :=
  ([23174] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block162Part008 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block162Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23174
    = surrogateDiagTailX0RatChunk001Sub000Block162Part008

theorem surrogateDiagonalTailChunk001Sub000Block162Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block162Part008CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block162Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block162Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block162Part008CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block162Part008SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block162Part008] using hcert

def TailChunk001Sub000Block162Part009SupportExplicit : Finset ℕ :=
  ([23178] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block162Part009 : ℚ :=
  (466407670475 : ℚ) / 4450060584588807744

def SurrogateDiagonalTailChunk001Sub000Block162Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23178
    = surrogateDiagTailX0RatChunk001Sub000Block162Part009

theorem surrogateDiagonalTailChunk001Sub000Block162Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block162Part009CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block162Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block162Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block162Part009CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block162Part009SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block162Part009] using hcert

def TailChunk001Sub000Block162Part010SupportExplicit : Finset ℕ :=
  ([23179] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block162Part010 : ℚ :=
  (149731428175 : ℚ) / 130714164267837460992

def SurrogateDiagonalTailChunk001Sub000Block162Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23179
    = surrogateDiagTailX0RatChunk001Sub000Block162Part010

theorem surrogateDiagonalTailChunk001Sub000Block162Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block162Part010CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block162Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block162Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block162Part010CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block162Part010SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block162Part010] using hcert

def TailChunk001Sub000Block162Part011SupportExplicit : Finset ℕ :=
  ([23181] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block162Part011 : ℚ :=
  (1865658622175 : ℚ) / 71274743178971671104

def SurrogateDiagonalTailChunk001Sub000Block162Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23181
    = surrogateDiagTailX0RatChunk001Sub000Block162Part011

theorem surrogateDiagonalTailChunk001Sub000Block162Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block162Part011CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block162Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block162Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block162Part011CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block162Part011SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block162Part011] using hcert

def TailChunk001Sub000Block162Part012SupportExplicit : Finset ℕ :=
  ([23182] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block162Part012 : ℚ :=
  (37021517825 : ℚ) / 20762822585861858304

def SurrogateDiagonalTailChunk001Sub000Block162Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23182
    = surrogateDiagTailX0RatChunk001Sub000Block162Part012

theorem surrogateDiagonalTailChunk001Sub000Block162Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block162Part012CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block162Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block162Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block162Part012CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block162Part012SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block162Part012] using hcert

def TailChunk001Sub000Block162Part013SupportExplicit : Finset ℕ :=
  ([23183] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block162Part013 : ℚ :=
  (25198627225 : ℚ) / 170356860523854692352

def SurrogateDiagonalTailChunk001Sub000Block162Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23183
    = surrogateDiagTailX0RatChunk001Sub000Block162Part013

theorem surrogateDiagonalTailChunk001Sub000Block162Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block162Part013CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block162Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block162Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block162Part013CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block162Part013SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block162Part013] using hcert

def TailChunk001Sub000Block162Part014SupportExplicit : Finset ℕ :=
  ([23185] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block162Part014 : ℚ :=
  (448177202625 : ℚ) / 98564217554533974016

def SurrogateDiagonalTailChunk001Sub000Block162Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23185
    = surrogateDiagTailX0RatChunk001Sub000Block162Part014

theorem surrogateDiagonalTailChunk001Sub000Block162Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block162Part014CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block162Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block162Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block162Part014CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block162Part014SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block162Part014] using hcert

def TailChunk001Sub000Block162Part015SupportExplicit : Finset ℕ :=
  ([23186] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block162Part015 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block162Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23186
    = surrogateDiagTailX0RatChunk001Sub000Block162Part015

theorem surrogateDiagonalTailChunk001Sub000Block162Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block162Part015CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block162Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block162Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block162Part015CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block162Part015SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block162Part015] using hcert

def TailChunk001Sub000Block162Part016SupportExplicit : Finset ℕ :=
  ([23187] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block162Part016 : ℚ :=
  (73338160769 : ℚ) / 2586200674755609600

def SurrogateDiagonalTailChunk001Sub000Block162Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23187
    = surrogateDiagTailX0RatChunk001Sub000Block162Part016

theorem surrogateDiagonalTailChunk001Sub000Block162Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block162Part016CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block162Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block162Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block162Part016CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block162Part016SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block162Part016] using hcert

def TailChunk001Sub000Block162Part017SupportExplicit : Finset ℕ :=
  ([23189] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block162Part017 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block162Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23189
    = surrogateDiagTailX0RatChunk001Sub000Block162Part017

theorem surrogateDiagonalTailChunk001Sub000Block162Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block162Part017CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block162Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block162Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block162Part017CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block162Part017SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block162Part017] using hcert

def TailChunk001Sub000Block162Part018SupportExplicit : Finset ℕ :=
  ([23190] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block162Part018 : ℚ :=
  (1045560735025 : ℚ) / 3637943988650508288

def SurrogateDiagonalTailChunk001Sub000Block162Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23190
    = surrogateDiagTailX0RatChunk001Sub000Block162Part018

theorem surrogateDiagonalTailChunk001Sub000Block162Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block162Part018CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block162Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block162Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block162Part018CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block162Part018SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block162Part018] using hcert

def TailChunk001Sub000Block162Part019SupportExplicit : Finset ℕ :=
  ([23191] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block162Part019 : ℚ :=
  (686384309675 : ℚ) / 194967928408868388864

def SurrogateDiagonalTailChunk001Sub000Block162Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23191
    = surrogateDiagTailX0RatChunk001Sub000Block162Part019

theorem surrogateDiagonalTailChunk001Sub000Block162Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block162Part019CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block162Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block162Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block162Part019CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block162Part019SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block162Part019] using hcert

def TailChunk001Sub000Block162Part020SupportExplicit : Finset ℕ :=
  ([23194] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block162Part020 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block162Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23194
    = surrogateDiagTailX0RatChunk001Sub000Block162Part020

theorem surrogateDiagonalTailChunk001Sub000Block162Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block162Part020CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block162Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block162Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block162Part020CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block162Part020SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block162Part020] using hcert

def TailChunk001Sub000Block162Part021SupportExplicit : Finset ℕ :=
  ([23195] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block162Part021 : ℚ :=
  (1345690857625 : ℚ) / 296203237742547191808

def SurrogateDiagonalTailChunk001Sub000Block162Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23195
    = surrogateDiagTailX0RatChunk001Sub000Block162Part021

theorem surrogateDiagonalTailChunk001Sub000Block162Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block162Part021CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block162Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block162Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block162Part021CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block162Part021SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block162Part021] using hcert

def TailChunk001Sub000Block162Part022SupportExplicit : Finset ℕ :=
  ([23197] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block162Part022 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block162Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23197
    = surrogateDiagTailX0RatChunk001Sub000Block162Part022

theorem surrogateDiagonalTailChunk001Sub000Block162Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block162Part022CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block162Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block162Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block162Part022CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block162Part022SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block162Part022] using hcert

def TailChunk001Sub000Block162Part023SupportExplicit : Finset ℕ :=
  ([23198] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block162Part023 : ℚ :=
  (9552906475 : ℚ) / 451314649094602752

def SurrogateDiagonalTailChunk001Sub000Block162Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23198
    = surrogateDiagTailX0RatChunk001Sub000Block162Part023

theorem surrogateDiagonalTailChunk001Sub000Block162Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block162Part023CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block162Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block162Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block162Part023CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block162Part023SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block162Part023] using hcert

def TailChunk001Sub000Block162Part024SupportExplicit : Finset ℕ :=
  ([23199] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block162Part024 : ℚ :=
  (130201034899 : ℚ) / 2821674129437491200

def SurrogateDiagonalTailChunk001Sub000Block162Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23199
    = surrogateDiagTailX0RatChunk001Sub000Block162Part024

theorem surrogateDiagonalTailChunk001Sub000Block162Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block162Part024CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block162Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block162Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block162Part024CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block162Part024SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block162Part024] using hcert

def surrogateDiagonalTailChunk001Sub000Block162HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block162Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block162Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block162Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block162Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block162Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block162Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block162Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block162Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block162Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block162Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block162Head : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block162Part000
    + surrogateDiagTailX0RatChunk001Sub000Block162Part001
    + surrogateDiagTailX0RatChunk001Sub000Block162Part002
    + surrogateDiagTailX0RatChunk001Sub000Block162Part003
    + surrogateDiagTailX0RatChunk001Sub000Block162Part004
    + surrogateDiagTailX0RatChunk001Sub000Block162Part005
    + surrogateDiagTailX0RatChunk001Sub000Block162Part006
    + surrogateDiagTailX0RatChunk001Sub000Block162Part007
    + surrogateDiagTailX0RatChunk001Sub000Block162Part008
    + surrogateDiagTailX0RatChunk001Sub000Block162Part009

def surrogateDiagonalTailChunk001Sub000Block162MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block162Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block162Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block162Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block162Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block162Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block162Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block162Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block162Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block162Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block162Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block162Mid : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block162Part010
    + surrogateDiagTailX0RatChunk001Sub000Block162Part011
    + surrogateDiagTailX0RatChunk001Sub000Block162Part012
    + surrogateDiagTailX0RatChunk001Sub000Block162Part013
    + surrogateDiagTailX0RatChunk001Sub000Block162Part014
    + surrogateDiagTailX0RatChunk001Sub000Block162Part015
    + surrogateDiagTailX0RatChunk001Sub000Block162Part016
    + surrogateDiagTailX0RatChunk001Sub000Block162Part017
    + surrogateDiagTailX0RatChunk001Sub000Block162Part018
    + surrogateDiagTailX0RatChunk001Sub000Block162Part019

def surrogateDiagonalTailChunk001Sub000Block162TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block162Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block162Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block162Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block162Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block162Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block162Tail : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block162Part020
    + surrogateDiagTailX0RatChunk001Sub000Block162Part021
    + surrogateDiagTailX0RatChunk001Sub000Block162Part022
    + surrogateDiagTailX0RatChunk001Sub000Block162Part023
    + surrogateDiagTailX0RatChunk001Sub000Block162Part024

def surrogateDiagonalTailChunk001Sub000Block162Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk001Sub000Block162HeadSum X0
    + surrogateDiagonalTailChunk001Sub000Block162MidSum X0
    + surrogateDiagonalTailChunk001Sub000Block162TailSum X0

def surrogateDiagTailX0RatChunk001Sub000Block162 : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block162Part000
    + surrogateDiagTailX0RatChunk001Sub000Block162Part001
    + surrogateDiagTailX0RatChunk001Sub000Block162Part002
    + surrogateDiagTailX0RatChunk001Sub000Block162Part003
    + surrogateDiagTailX0RatChunk001Sub000Block162Part004
    + surrogateDiagTailX0RatChunk001Sub000Block162Part005
    + surrogateDiagTailX0RatChunk001Sub000Block162Part006
    + surrogateDiagTailX0RatChunk001Sub000Block162Part007
    + surrogateDiagTailX0RatChunk001Sub000Block162Part008
    + surrogateDiagTailX0RatChunk001Sub000Block162Part009
    + surrogateDiagTailX0RatChunk001Sub000Block162Part010
    + surrogateDiagTailX0RatChunk001Sub000Block162Part011
    + surrogateDiagTailX0RatChunk001Sub000Block162Part012
    + surrogateDiagTailX0RatChunk001Sub000Block162Part013
    + surrogateDiagTailX0RatChunk001Sub000Block162Part014
    + surrogateDiagTailX0RatChunk001Sub000Block162Part015
    + surrogateDiagTailX0RatChunk001Sub000Block162Part016
    + surrogateDiagTailX0RatChunk001Sub000Block162Part017
    + surrogateDiagTailX0RatChunk001Sub000Block162Part018
    + surrogateDiagTailX0RatChunk001Sub000Block162Part019
    + surrogateDiagTailX0RatChunk001Sub000Block162Part020
    + surrogateDiagTailX0RatChunk001Sub000Block162Part021
    + surrogateDiagTailX0RatChunk001Sub000Block162Part022
    + surrogateDiagTailX0RatChunk001Sub000Block162Part023
    + surrogateDiagTailX0RatChunk001Sub000Block162Part024

theorem surrogateDiagTailX0RatChunk001Sub000Block162_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk001Sub000Block162Head + surrogateDiagTailX0RatChunk001Sub000Block162Mid + surrogateDiagTailX0RatChunk001Sub000Block162Tail =
      surrogateDiagTailX0RatChunk001Sub000Block162 := by
  unfold surrogateDiagTailX0RatChunk001Sub000Block162Head surrogateDiagTailX0RatChunk001Sub000Block162Mid surrogateDiagTailX0RatChunk001Sub000Block162Tail surrogateDiagTailX0RatChunk001Sub000Block162
  ring

def SurrogateDiagonalTailChunk001Sub000Block162HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block162HeadSum X0 = surrogateDiagTailX0RatChunk001Sub000Block162Head

def SurrogateDiagonalTailChunk001Sub000Block162MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block162MidSum X0 = surrogateDiagTailX0RatChunk001Sub000Block162Mid

def SurrogateDiagonalTailChunk001Sub000Block162TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block162TailSum X0 = surrogateDiagTailX0RatChunk001Sub000Block162Tail

theorem surrogateDiagonalTailChunk001Sub000Block162_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk001Sub000Block162HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk001Sub000Block162MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk001Sub000Block162TailCertificateAt X0) :
    surrogateDiagonalTailChunk001Sub000Block162Sum X0 = surrogateDiagTailX0RatChunk001Sub000Block162 := by
  unfold SurrogateDiagonalTailChunk001Sub000Block162HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk001Sub000Block162MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk001Sub000Block162TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk001Sub000Block162Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk001Sub000Block162_eq_head_add_mid_add_tail

/-- Block 163 covers tail-support indices [14075,14100) and q from 23201 to 23241. -/

def TailChunk001Sub000Block163Part000SupportExplicit : Finset ℕ :=
  ([23201] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block163Part000 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block163Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23201
    = surrogateDiagTailX0RatChunk001Sub000Block163Part000

theorem surrogateDiagonalTailChunk001Sub000Block163Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block163Part000CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block163Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block163Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block163Part000CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block163Part000SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block163Part000] using hcert

def TailChunk001Sub000Block163Part001SupportExplicit : Finset ℕ :=
  ([23203] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block163Part001 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block163Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23203
    = surrogateDiagTailX0RatChunk001Sub000Block163Part001

theorem surrogateDiagonalTailChunk001Sub000Block163Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block163Part001CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block163Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block163Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block163Part001CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block163Part001SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block163Part001] using hcert

def TailChunk001Sub000Block163Part002SupportExplicit : Finset ℕ :=
  ([23205] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block163Part002 : ℚ :=
  (31152212675 : ℚ) / 222695634845564928

def SurrogateDiagonalTailChunk001Sub000Block163Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23205
    = surrogateDiagTailX0RatChunk001Sub000Block163Part002

theorem surrogateDiagonalTailChunk001Sub000Block163Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block163Part002CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block163Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block163Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block163Part002CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block163Part002SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block163Part002] using hcert

def TailChunk001Sub000Block163Part003SupportExplicit : Finset ℕ :=
  ([23206] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block163Part003 : ℚ :=
  (2033284367 : ℚ) / 809642417832345600

def SurrogateDiagonalTailChunk001Sub000Block163Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23206
    = surrogateDiagTailX0RatChunk001Sub000Block163Part003

theorem surrogateDiagonalTailChunk001Sub000Block163Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block163Part003CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block163Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block163Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block163Part003CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block163Part003SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block163Part003] using hcert

def TailChunk001Sub000Block163Part004SupportExplicit : Finset ℕ :=
  ([23207] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block163Part004 : ℚ :=
  (324130923775 : ℚ) / 604727488863011340288

def SurrogateDiagonalTailChunk001Sub000Block163Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23207
    = surrogateDiagTailX0RatChunk001Sub000Block163Part004

theorem surrogateDiagonalTailChunk001Sub000Block163Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block163Part004CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block163Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block163Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block163Part004CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block163Part004SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block163Part004] using hcert

def TailChunk001Sub000Block163Part005SupportExplicit : Finset ℕ :=
  ([23209] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block163Part005 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block163Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23209
    = surrogateDiagTailX0RatChunk001Sub000Block163Part005

theorem surrogateDiagonalTailChunk001Sub000Block163Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block163Part005CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block163Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block163Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block163Part005CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block163Part005SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block163Part005] using hcert

def TailChunk001Sub000Block163Part006SupportExplicit : Finset ℕ :=
  ([23210] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block163Part006 : ℚ :=
  (33238889899 : ℚ) / 497970934272000000

def SurrogateDiagonalTailChunk001Sub000Block163Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23210
    = surrogateDiagTailX0RatChunk001Sub000Block163Part006

theorem surrogateDiagonalTailChunk001Sub000Block163Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block163Part006CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block163Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block163Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block163Part006CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block163Part006SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block163Part006] using hcert

def TailChunk001Sub000Block163Part007SupportExplicit : Finset ℕ :=
  ([23213] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block163Part007 : ℚ :=
  (23206956025 : ℚ) / 172153384522360602912

def SurrogateDiagonalTailChunk001Sub000Block163Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23213
    = surrogateDiagTailX0RatChunk001Sub000Block163Part007

theorem surrogateDiagonalTailChunk001Sub000Block163Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block163Part007CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block163Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block163Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block163Part007CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block163Part007SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block163Part007] using hcert

def TailChunk001Sub000Block163Part008SupportExplicit : Finset ℕ :=
  ([23214] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block163Part008 : ℚ :=
  (951915028375 : ℚ) / 7861224550975930368

def SurrogateDiagonalTailChunk001Sub000Block163Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23214
    = surrogateDiagTailX0RatChunk001Sub000Block163Part008

theorem surrogateDiagonalTailChunk001Sub000Block163Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block163Part008CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block163Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block163Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block163Part008CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block163Part008SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block163Part008] using hcert

def TailChunk001Sub000Block163Part009SupportExplicit : Finset ℕ :=
  ([23215] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block163Part009 : ℚ :=
  (449336952375 : ℚ) / 99075463774986704896

def SurrogateDiagonalTailChunk001Sub000Block163Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23215
    = surrogateDiagTailX0RatChunk001Sub000Block163Part009

theorem surrogateDiagonalTailChunk001Sub000Block163Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block163Part009CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block163Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block163Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block163Part009CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block163Part009SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block163Part009] using hcert

def TailChunk001Sub000Block163Part010SupportExplicit : Finset ℕ :=
  ([23217] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block163Part010 : ℚ :=
  (73612103963 : ℚ) / 2613749839806873600

def SurrogateDiagonalTailChunk001Sub000Block163Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23217
    = surrogateDiagTailX0RatChunk001Sub000Block163Part010

theorem surrogateDiagonalTailChunk001Sub000Block163Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block163Part010CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block163Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block163Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block163Part010CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block163Part010SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block163Part010] using hcert

def TailChunk001Sub000Block163Part011SupportExplicit : Finset ℕ :=
  ([23218] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block163Part011 : ℚ :=
  (243986032475 : ℚ) / 12185495525554274304

def SurrogateDiagonalTailChunk001Sub000Block163Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23218
    = surrogateDiagTailX0RatChunk001Sub000Block163Part011

theorem surrogateDiagonalTailChunk001Sub000Block163Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block163Part011CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block163Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block163Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block163Part011CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block163Part011SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block163Part011] using hcert

def TailChunk001Sub000Block163Part012SupportExplicit : Finset ℕ :=
  ([23219] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block163Part012 : ℚ :=
  (60937659187 : ℚ) / 13255628730923059200

def SurrogateDiagonalTailChunk001Sub000Block163Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23219
    = surrogateDiagTailX0RatChunk001Sub000Block163Part012

theorem surrogateDiagonalTailChunk001Sub000Block163Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block163Part012CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block163Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block163Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block163Part012CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block163Part012SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block163Part012] using hcert

def TailChunk001Sub000Block163Part013SupportExplicit : Finset ℕ :=
  ([23221] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block163Part013 : ℚ :=
  (33502481887 : ℚ) / 19825158648882000000

def SurrogateDiagonalTailChunk001Sub000Block163Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23221
    = surrogateDiagTailX0RatChunk001Sub000Block163Part013

theorem surrogateDiagonalTailChunk001Sub000Block163Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block163Part013CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block163Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block163Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block163Part013CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block163Part013SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block163Part013] using hcert

def TailChunk001Sub000Block163Part014SupportExplicit : Finset ℕ :=
  ([23222] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block163Part014 : ℚ :=
  (104122915925 : ℚ) / 17726144794056720384

def SurrogateDiagonalTailChunk001Sub000Block163Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23222
    = surrogateDiagTailX0RatChunk001Sub000Block163Part014

theorem surrogateDiagonalTailChunk001Sub000Block163Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block163Part014CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block163Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block163Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block163Part014CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block163Part014SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block163Part014] using hcert

def TailChunk001Sub000Block163Part015SupportExplicit : Finset ℕ :=
  ([23223] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block163Part015 : ℚ :=
  (1872424997 : ℚ) / 71792766437351040

def SurrogateDiagonalTailChunk001Sub000Block163Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23223
    = surrogateDiagTailX0RatChunk001Sub000Block163Part015

theorem surrogateDiagonalTailChunk001Sub000Block163Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block163Part015CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block163Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block163Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block163Part015CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block163Part015SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block163Part015] using hcert

def TailChunk001Sub000Block163Part016SupportExplicit : Finset ℕ :=
  ([23227] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block163Part016 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block163Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23227
    = surrogateDiagTailX0RatChunk001Sub000Block163Part016

theorem surrogateDiagonalTailChunk001Sub000Block163Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block163Part016CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block163Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block163Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block163Part016CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block163Part016SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block163Part016] using hcert

def TailChunk001Sub000Block163Part017SupportExplicit : Finset ℕ :=
  ([23230] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block163Part017 : ℚ :=
  (94534553 : ℚ) / 1874422809600000

def SurrogateDiagonalTailChunk001Sub000Block163Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23230
    = surrogateDiagTailX0RatChunk001Sub000Block163Part017

theorem surrogateDiagonalTailChunk001Sub000Block163Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block163Part017CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block163Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block163Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block163Part017CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block163Part017SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block163Part017] using hcert

def TailChunk001Sub000Block163Part018SupportExplicit : Finset ℕ :=
  ([23231] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block163Part018 : ℚ :=
  (75200080025 : ℚ) / 65945880958955694336

def SurrogateDiagonalTailChunk001Sub000Block163Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23231
    = surrogateDiagTailX0RatChunk001Sub000Block163Part018

theorem surrogateDiagonalTailChunk001Sub000Block163Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block163Part018CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block163Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block163Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block163Part018CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block163Part018SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block163Part018] using hcert

def TailChunk001Sub000Block163Part019SupportExplicit : Finset ℕ :=
  ([23233] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block163Part019 : ℚ :=
  (688870062575 : ℚ) / 196384583283593269824

def SurrogateDiagonalTailChunk001Sub000Block163Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23233
    = surrogateDiagTailX0RatChunk001Sub000Block163Part019

theorem surrogateDiagonalTailChunk001Sub000Block163Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block163Part019CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block163Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block163Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block163Part019CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block163Part019SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block163Part019] using hcert

def TailChunk001Sub000Block163Part020SupportExplicit : Finset ℕ :=
  ([23234] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block163Part020 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block163Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23234
    = surrogateDiagTailX0RatChunk001Sub000Block163Part020

theorem surrogateDiagonalTailChunk001Sub000Block163Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block163Part020CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block163Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block163Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block163Part020CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block163Part020SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block163Part020] using hcert

def TailChunk001Sub000Block163Part021SupportExplicit : Finset ℕ :=
  ([23235] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block163Part021 : ℚ :=
  (274799825075 : ℚ) / 4901052855456497664

def SurrogateDiagonalTailChunk001Sub000Block163Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23235
    = surrogateDiagTailX0RatChunk001Sub000Block163Part021

theorem surrogateDiagonalTailChunk001Sub000Block163Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block163Part021CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block163Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block163Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block163Part021CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block163Part021SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block163Part021] using hcert

def TailChunk001Sub000Block163Part022SupportExplicit : Finset ℕ :=
  ([23237] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block163Part022 : ℚ :=
  (378719756725 : ℚ) / 585331238985149824128

def SurrogateDiagonalTailChunk001Sub000Block163Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23237
    = surrogateDiagTailX0RatChunk001Sub000Block163Part022

theorem surrogateDiagonalTailChunk001Sub000Block163Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block163Part022CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block163Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block163Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block163Part022CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block163Part022SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block163Part022] using hcert

def TailChunk001Sub000Block163Part023SupportExplicit : Finset ℕ :=
  ([23239] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block163Part023 : ℚ :=
  (471207907075 : ℚ) / 570570858871977934848

def SurrogateDiagonalTailChunk001Sub000Block163Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23239
    = surrogateDiagTailX0RatChunk001Sub000Block163Part023

theorem surrogateDiagonalTailChunk001Sub000Block163Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block163Part023CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block163Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block163Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block163Part023CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block163Part023SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block163Part023] using hcert

def TailChunk001Sub000Block163Part024SupportExplicit : Finset ℕ :=
  ([23241] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block163Part024 : ℚ :=
  (16380275801 : ℚ) / 580833297734860800

def SurrogateDiagonalTailChunk001Sub000Block163Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23241
    = surrogateDiagTailX0RatChunk001Sub000Block163Part024

theorem surrogateDiagonalTailChunk001Sub000Block163Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block163Part024CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block163Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block163Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block163Part024CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block163Part024SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block163Part024] using hcert

def surrogateDiagonalTailChunk001Sub000Block163HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block163Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block163Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block163Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block163Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block163Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block163Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block163Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block163Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block163Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block163Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block163Head : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block163Part000
    + surrogateDiagTailX0RatChunk001Sub000Block163Part001
    + surrogateDiagTailX0RatChunk001Sub000Block163Part002
    + surrogateDiagTailX0RatChunk001Sub000Block163Part003
    + surrogateDiagTailX0RatChunk001Sub000Block163Part004
    + surrogateDiagTailX0RatChunk001Sub000Block163Part005
    + surrogateDiagTailX0RatChunk001Sub000Block163Part006
    + surrogateDiagTailX0RatChunk001Sub000Block163Part007
    + surrogateDiagTailX0RatChunk001Sub000Block163Part008
    + surrogateDiagTailX0RatChunk001Sub000Block163Part009

def surrogateDiagonalTailChunk001Sub000Block163MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block163Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block163Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block163Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block163Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block163Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block163Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block163Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block163Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block163Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block163Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block163Mid : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block163Part010
    + surrogateDiagTailX0RatChunk001Sub000Block163Part011
    + surrogateDiagTailX0RatChunk001Sub000Block163Part012
    + surrogateDiagTailX0RatChunk001Sub000Block163Part013
    + surrogateDiagTailX0RatChunk001Sub000Block163Part014
    + surrogateDiagTailX0RatChunk001Sub000Block163Part015
    + surrogateDiagTailX0RatChunk001Sub000Block163Part016
    + surrogateDiagTailX0RatChunk001Sub000Block163Part017
    + surrogateDiagTailX0RatChunk001Sub000Block163Part018
    + surrogateDiagTailX0RatChunk001Sub000Block163Part019

def surrogateDiagonalTailChunk001Sub000Block163TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block163Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block163Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block163Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block163Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block163Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block163Tail : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block163Part020
    + surrogateDiagTailX0RatChunk001Sub000Block163Part021
    + surrogateDiagTailX0RatChunk001Sub000Block163Part022
    + surrogateDiagTailX0RatChunk001Sub000Block163Part023
    + surrogateDiagTailX0RatChunk001Sub000Block163Part024

def surrogateDiagonalTailChunk001Sub000Block163Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk001Sub000Block163HeadSum X0
    + surrogateDiagonalTailChunk001Sub000Block163MidSum X0
    + surrogateDiagonalTailChunk001Sub000Block163TailSum X0

def surrogateDiagTailX0RatChunk001Sub000Block163 : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block163Part000
    + surrogateDiagTailX0RatChunk001Sub000Block163Part001
    + surrogateDiagTailX0RatChunk001Sub000Block163Part002
    + surrogateDiagTailX0RatChunk001Sub000Block163Part003
    + surrogateDiagTailX0RatChunk001Sub000Block163Part004
    + surrogateDiagTailX0RatChunk001Sub000Block163Part005
    + surrogateDiagTailX0RatChunk001Sub000Block163Part006
    + surrogateDiagTailX0RatChunk001Sub000Block163Part007
    + surrogateDiagTailX0RatChunk001Sub000Block163Part008
    + surrogateDiagTailX0RatChunk001Sub000Block163Part009
    + surrogateDiagTailX0RatChunk001Sub000Block163Part010
    + surrogateDiagTailX0RatChunk001Sub000Block163Part011
    + surrogateDiagTailX0RatChunk001Sub000Block163Part012
    + surrogateDiagTailX0RatChunk001Sub000Block163Part013
    + surrogateDiagTailX0RatChunk001Sub000Block163Part014
    + surrogateDiagTailX0RatChunk001Sub000Block163Part015
    + surrogateDiagTailX0RatChunk001Sub000Block163Part016
    + surrogateDiagTailX0RatChunk001Sub000Block163Part017
    + surrogateDiagTailX0RatChunk001Sub000Block163Part018
    + surrogateDiagTailX0RatChunk001Sub000Block163Part019
    + surrogateDiagTailX0RatChunk001Sub000Block163Part020
    + surrogateDiagTailX0RatChunk001Sub000Block163Part021
    + surrogateDiagTailX0RatChunk001Sub000Block163Part022
    + surrogateDiagTailX0RatChunk001Sub000Block163Part023
    + surrogateDiagTailX0RatChunk001Sub000Block163Part024

theorem surrogateDiagTailX0RatChunk001Sub000Block163_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk001Sub000Block163Head + surrogateDiagTailX0RatChunk001Sub000Block163Mid + surrogateDiagTailX0RatChunk001Sub000Block163Tail =
      surrogateDiagTailX0RatChunk001Sub000Block163 := by
  unfold surrogateDiagTailX0RatChunk001Sub000Block163Head surrogateDiagTailX0RatChunk001Sub000Block163Mid surrogateDiagTailX0RatChunk001Sub000Block163Tail surrogateDiagTailX0RatChunk001Sub000Block163
  ring

def SurrogateDiagonalTailChunk001Sub000Block163HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block163HeadSum X0 = surrogateDiagTailX0RatChunk001Sub000Block163Head

def SurrogateDiagonalTailChunk001Sub000Block163MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block163MidSum X0 = surrogateDiagTailX0RatChunk001Sub000Block163Mid

def SurrogateDiagonalTailChunk001Sub000Block163TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block163TailSum X0 = surrogateDiagTailX0RatChunk001Sub000Block163Tail

theorem surrogateDiagonalTailChunk001Sub000Block163_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk001Sub000Block163HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk001Sub000Block163MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk001Sub000Block163TailCertificateAt X0) :
    surrogateDiagonalTailChunk001Sub000Block163Sum X0 = surrogateDiagTailX0RatChunk001Sub000Block163 := by
  unfold SurrogateDiagonalTailChunk001Sub000Block163HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk001Sub000Block163MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk001Sub000Block163TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk001Sub000Block163Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk001Sub000Block163_eq_head_add_mid_add_tail

/-- Block 164 covers tail-support indices [14100,14125) and q from 23242 to 23282. -/

def TailChunk001Sub000Block164Part000SupportExplicit : Finset ℕ :=
  ([23242] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block164Part000 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block164Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23242
    = surrogateDiagTailX0RatChunk001Sub000Block164Part000

theorem surrogateDiagonalTailChunk001Sub000Block164Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block164Part000CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block164Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block164Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block164Part000CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block164Part000SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block164Part000] using hcert

def TailChunk001Sub000Block164Part001SupportExplicit : Finset ℕ :=
  ([23243] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block164Part001 : ℚ :=
  (1868614093 : ℚ) / 1658369338874265600

def SurrogateDiagonalTailChunk001Sub000Block164Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23243
    = surrogateDiagTailX0RatChunk001Sub000Block164Part001

theorem surrogateDiagonalTailChunk001Sub000Block164Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block164Part001CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block164Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block164Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block164Part001CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block164Part001SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block164Part001] using hcert

def TailChunk001Sub000Block164Part002SupportExplicit : Finset ℕ :=
  ([23245] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block164Part002 : ℚ :=
  (450498202125 : ℚ) / 99588696271962505216

def SurrogateDiagonalTailChunk001Sub000Block164Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23245
    = surrogateDiagTailX0RatChunk001Sub000Block164Part002

theorem surrogateDiagonalTailChunk001Sub000Block164Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block164Part002CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block164Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block164Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block164Part002CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block164Part002SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block164Part002] using hcert

def TailChunk001Sub000Block164Part003SupportExplicit : Finset ℕ :=
  ([23246] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block164Part003 : ℚ :=
  (77912656375 : ℚ) / 41760252753143973888

def SurrogateDiagonalTailChunk001Sub000Block164Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23246
    = surrogateDiagTailX0RatChunk001Sub000Block164Part003

theorem surrogateDiagonalTailChunk001Sub000Block164Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block164Part003CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block164Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block164Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block164Part003CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block164Part003SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block164Part003] using hcert

def TailChunk001Sub000Block164Part004SupportExplicit : Finset ℕ :=
  ([23249] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block164Part004 : ℚ :=
  (14738249875 : ℚ) / 75555222139641923712

def SurrogateDiagonalTailChunk001Sub000Block164Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23249
    = surrogateDiagTailX0RatChunk001Sub000Block164Part004

theorem surrogateDiagonalTailChunk001Sub000Block164Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block164Part004CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block164Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block164Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block164Part004CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block164Part004SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block164Part004] using hcert

def TailChunk001Sub000Block164Part005SupportExplicit : Finset ℕ :=
  ([23251] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block164Part005 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block164Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23251
    = surrogateDiagTailX0RatChunk001Sub000Block164Part005

theorem surrogateDiagonalTailChunk001Sub000Block164Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block164Part005CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block164Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block164Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block164Part005CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block164Part005SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block164Part005] using hcert

def TailChunk001Sub000Block164Part006SupportExplicit : Finset ℕ :=
  ([23253] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block164Part006 : ℚ :=
  (18350365675 : ℚ) / 603294664035926016

def SurrogateDiagonalTailChunk001Sub000Block164Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23253
    = surrogateDiagTailX0RatChunk001Sub000Block164Part006

theorem surrogateDiagonalTailChunk001Sub000Block164Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block164Part006CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block164Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block164Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block164Part006CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block164Part006SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block164Part006] using hcert

def TailChunk001Sub000Block164Part007SupportExplicit : Finset ℕ :=
  ([23254] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block164Part007 : ℚ :=
  (5436692843 : ℚ) / 131246244000000000

def SurrogateDiagonalTailChunk001Sub000Block164Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23254
    = surrogateDiagTailX0RatChunk001Sub000Block164Part007

theorem surrogateDiagonalTailChunk001Sub000Block164Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block164Part007CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block164Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block164Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block164Part007CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block164Part007SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block164Part007] using hcert

def TailChunk001Sub000Block164Part008SupportExplicit : Finset ℕ :=
  ([23255] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block164Part008 : ℚ :=
  (10821254849 : ℚ) / 2394245185286400000

def SurrogateDiagonalTailChunk001Sub000Block164Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23255
    = surrogateDiagTailX0RatChunk001Sub000Block164Part008

theorem surrogateDiagonalTailChunk001Sub000Block164Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block164Part008CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block164Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block164Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block164Part008CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block164Part008SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block164Part008] using hcert

def TailChunk001Sub000Block164Part009SupportExplicit : Finset ℕ :=
  ([23257] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block164Part009 : ℚ :=
  (301470176525 : ℚ) / 264967071160073601024

def SurrogateDiagonalTailChunk001Sub000Block164Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23257
    = surrogateDiagTailX0RatChunk001Sub000Block164Part009

theorem surrogateDiagonalTailChunk001Sub000Block164Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block164Part009CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block164Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block164Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block164Part009CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block164Part009SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block164Part009] using hcert

def TailChunk001Sub000Block164Part010SupportExplicit : Finset ℕ :=
  ([23258] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block164Part010 : ℚ :=
  (664146429 : ℚ) / 3278820966400000

def SurrogateDiagonalTailChunk001Sub000Block164Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23258
    = surrogateDiagTailX0RatChunk001Sub000Block164Part010

theorem surrogateDiagonalTailChunk001Sub000Block164Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block164Part010CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block164Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block164Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block164Part010CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block164Part010SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block164Part010] using hcert

def TailChunk001Sub000Block164Part011SupportExplicit : Finset ℕ :=
  ([23259] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block164Part011 : ℚ :=
  (939117248425 : ℚ) / 36119514688426156032

def SurrogateDiagonalTailChunk001Sub000Block164Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23259
    = surrogateDiagTailX0RatChunk001Sub000Block164Part011

theorem surrogateDiagonalTailChunk001Sub000Block164Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block164Part011CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block164Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block164Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block164Part011CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block164Part011SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block164Part011] using hcert

def TailChunk001Sub000Block164Part012SupportExplicit : Finset ℕ :=
  ([23261] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block164Part012 : ℚ :=
  (691605165925 : ℚ) / 394666598703286850688

def SurrogateDiagonalTailChunk001Sub000Block164Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23261
    = surrogateDiagTailX0RatChunk001Sub000Block164Part012

theorem surrogateDiagonalTailChunk001Sub000Block164Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block164Part012CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block164Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block164Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block164Part012CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block164Part012SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block164Part012] using hcert

def TailChunk001Sub000Block164Part013SupportExplicit : Finset ℕ :=
  ([23262] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block164Part013 : ℚ :=
  (2348090504675 : ℚ) / 4514939336053269504

def SurrogateDiagonalTailChunk001Sub000Block164Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23262
    = surrogateDiagTailX0RatChunk001Sub000Block164Part013

theorem surrogateDiagonalTailChunk001Sub000Block164Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block164Part013CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block164Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block164Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block164Part013CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block164Part013SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block164Part013] using hcert

def TailChunk001Sub000Block164Part014SupportExplicit : Finset ℕ :=
  ([23263] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block164Part014 : ℚ :=
  (5350397 : ℚ) / 20003187549542400

def SurrogateDiagonalTailChunk001Sub000Block164Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23263
    = surrogateDiagTailX0RatChunk001Sub000Block164Part014

theorem surrogateDiagonalTailChunk001Sub000Block164Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block164Part014CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block164Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block164Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block164Part014CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block164Part014SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block164Part014] using hcert

def TailChunk001Sub000Block164Part015SupportExplicit : Finset ℕ :=
  ([23266] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block164Part015 : ℚ :=
  (2114479515625 : ℚ) / 11444173718395625472

def SurrogateDiagonalTailChunk001Sub000Block164Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23266
    = surrogateDiagTailX0RatChunk001Sub000Block164Part015

theorem surrogateDiagonalTailChunk001Sub000Block164Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block164Part015CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block164Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block164Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block164Part015CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block164Part015SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block164Part015] using hcert

def TailChunk001Sub000Block164Part016SupportExplicit : Finset ℕ :=
  ([23267] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block164Part016 : ℚ :=
  (159924533725 : ℚ) / 672878536584114751488

def SurrogateDiagonalTailChunk001Sub000Block164Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23267
    = surrogateDiagTailX0RatChunk001Sub000Block164Part016

theorem surrogateDiagonalTailChunk001Sub000Block164Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block164Part016CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block164Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block164Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block164Part016CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block164Part016SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block164Part016] using hcert

def TailChunk001Sub000Block164Part017SupportExplicit : Finset ℕ :=
  ([23269] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block164Part017 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block164Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23269
    = surrogateDiagTailX0RatChunk001Sub000Block164Part017

theorem surrogateDiagonalTailChunk001Sub000Block164Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block164Part017CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block164Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block164Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block164Part017CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block164Part017SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block164Part017] using hcert

def TailChunk001Sub000Block164Part018SupportExplicit : Finset ℕ :=
  ([23270] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block164Part018 : ℚ :=
  (1336629377725 : ℚ) / 3331285283834560512

def SurrogateDiagonalTailChunk001Sub000Block164Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23270
    = surrogateDiagTailX0RatChunk001Sub000Block164Part018

theorem surrogateDiagonalTailChunk001Sub000Block164Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block164Part018CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block164Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block164Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block164Part018CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block164Part018SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block164Part018] using hcert

def TailChunk001Sub000Block164Part019SupportExplicit : Finset ℕ :=
  ([23271] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block164Part019 : ℚ :=
  (4196814725 : ℚ) / 161580903979892208

def SurrogateDiagonalTailChunk001Sub000Block164Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23271
    = surrogateDiagTailX0RatChunk001Sub000Block164Part019

theorem surrogateDiagonalTailChunk001Sub000Block164Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block164Part019CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block164Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block164Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block164Part019CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block164Part019SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block164Part019] using hcert

def TailChunk001Sub000Block164Part020SupportExplicit : Finset ℕ :=
  ([23277] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block164Part020 : ℚ :=
  (1881142621775 : ℚ) / 72462939412466424384

def SurrogateDiagonalTailChunk001Sub000Block164Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23277
    = surrogateDiagTailX0RatChunk001Sub000Block164Part020

theorem surrogateDiagonalTailChunk001Sub000Block164Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block164Part020CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block164Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block164Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block164Part020CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block164Part020SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block164Part020] using hcert

def TailChunk001Sub000Block164Part021SupportExplicit : Finset ℕ :=
  ([23278] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block164Part021 : ℚ :=
  (2055799666525 : ℚ) / 10647303782740918272

def SurrogateDiagonalTailChunk001Sub000Block164Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23278
    = surrogateDiagTailX0RatChunk001Sub000Block164Part021

theorem surrogateDiagonalTailChunk001Sub000Block164Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block164Part021CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block164Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block164Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block164Part021CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block164Part021SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block164Part021] using hcert

def TailChunk001Sub000Block164Part022SupportExplicit : Finset ℕ :=
  ([23279] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block164Part022 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block164Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23279
    = surrogateDiagTailX0RatChunk001Sub000Block164Part022

theorem surrogateDiagonalTailChunk001Sub000Block164Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block164Part022CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block164Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block164Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block164Part022CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block164Part022SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block164Part022] using hcert

def TailChunk001Sub000Block164Part023SupportExplicit : Finset ℕ :=
  ([23281] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block164Part023 : ℚ :=
  (10500371 : ℚ) / 26372460937500000

def SurrogateDiagonalTailChunk001Sub000Block164Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23281
    = surrogateDiagTailX0RatChunk001Sub000Block164Part023

theorem surrogateDiagonalTailChunk001Sub000Block164Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block164Part023CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block164Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block164Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block164Part023CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block164Part023SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block164Part023] using hcert

def TailChunk001Sub000Block164Part024SupportExplicit : Finset ℕ :=
  ([23282] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block164Part024 : ℚ :=
  (410185024375 : ℚ) / 1545382377568619208

def SurrogateDiagonalTailChunk001Sub000Block164Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23282
    = surrogateDiagTailX0RatChunk001Sub000Block164Part024

theorem surrogateDiagonalTailChunk001Sub000Block164Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block164Part024CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block164Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block164Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block164Part024CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block164Part024SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block164Part024] using hcert

def surrogateDiagonalTailChunk001Sub000Block164HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block164Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block164Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block164Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block164Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block164Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block164Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block164Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block164Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block164Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block164Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block164Head : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block164Part000
    + surrogateDiagTailX0RatChunk001Sub000Block164Part001
    + surrogateDiagTailX0RatChunk001Sub000Block164Part002
    + surrogateDiagTailX0RatChunk001Sub000Block164Part003
    + surrogateDiagTailX0RatChunk001Sub000Block164Part004
    + surrogateDiagTailX0RatChunk001Sub000Block164Part005
    + surrogateDiagTailX0RatChunk001Sub000Block164Part006
    + surrogateDiagTailX0RatChunk001Sub000Block164Part007
    + surrogateDiagTailX0RatChunk001Sub000Block164Part008
    + surrogateDiagTailX0RatChunk001Sub000Block164Part009

def surrogateDiagonalTailChunk001Sub000Block164MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block164Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block164Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block164Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block164Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block164Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block164Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block164Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block164Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block164Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block164Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block164Mid : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block164Part010
    + surrogateDiagTailX0RatChunk001Sub000Block164Part011
    + surrogateDiagTailX0RatChunk001Sub000Block164Part012
    + surrogateDiagTailX0RatChunk001Sub000Block164Part013
    + surrogateDiagTailX0RatChunk001Sub000Block164Part014
    + surrogateDiagTailX0RatChunk001Sub000Block164Part015
    + surrogateDiagTailX0RatChunk001Sub000Block164Part016
    + surrogateDiagTailX0RatChunk001Sub000Block164Part017
    + surrogateDiagTailX0RatChunk001Sub000Block164Part018
    + surrogateDiagTailX0RatChunk001Sub000Block164Part019

def surrogateDiagonalTailChunk001Sub000Block164TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block164Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block164Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block164Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block164Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block164Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block164Tail : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block164Part020
    + surrogateDiagTailX0RatChunk001Sub000Block164Part021
    + surrogateDiagTailX0RatChunk001Sub000Block164Part022
    + surrogateDiagTailX0RatChunk001Sub000Block164Part023
    + surrogateDiagTailX0RatChunk001Sub000Block164Part024

def surrogateDiagonalTailChunk001Sub000Block164Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk001Sub000Block164HeadSum X0
    + surrogateDiagonalTailChunk001Sub000Block164MidSum X0
    + surrogateDiagonalTailChunk001Sub000Block164TailSum X0

def surrogateDiagTailX0RatChunk001Sub000Block164 : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block164Part000
    + surrogateDiagTailX0RatChunk001Sub000Block164Part001
    + surrogateDiagTailX0RatChunk001Sub000Block164Part002
    + surrogateDiagTailX0RatChunk001Sub000Block164Part003
    + surrogateDiagTailX0RatChunk001Sub000Block164Part004
    + surrogateDiagTailX0RatChunk001Sub000Block164Part005
    + surrogateDiagTailX0RatChunk001Sub000Block164Part006
    + surrogateDiagTailX0RatChunk001Sub000Block164Part007
    + surrogateDiagTailX0RatChunk001Sub000Block164Part008
    + surrogateDiagTailX0RatChunk001Sub000Block164Part009
    + surrogateDiagTailX0RatChunk001Sub000Block164Part010
    + surrogateDiagTailX0RatChunk001Sub000Block164Part011
    + surrogateDiagTailX0RatChunk001Sub000Block164Part012
    + surrogateDiagTailX0RatChunk001Sub000Block164Part013
    + surrogateDiagTailX0RatChunk001Sub000Block164Part014
    + surrogateDiagTailX0RatChunk001Sub000Block164Part015
    + surrogateDiagTailX0RatChunk001Sub000Block164Part016
    + surrogateDiagTailX0RatChunk001Sub000Block164Part017
    + surrogateDiagTailX0RatChunk001Sub000Block164Part018
    + surrogateDiagTailX0RatChunk001Sub000Block164Part019
    + surrogateDiagTailX0RatChunk001Sub000Block164Part020
    + surrogateDiagTailX0RatChunk001Sub000Block164Part021
    + surrogateDiagTailX0RatChunk001Sub000Block164Part022
    + surrogateDiagTailX0RatChunk001Sub000Block164Part023
    + surrogateDiagTailX0RatChunk001Sub000Block164Part024

theorem surrogateDiagTailX0RatChunk001Sub000Block164_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk001Sub000Block164Head + surrogateDiagTailX0RatChunk001Sub000Block164Mid + surrogateDiagTailX0RatChunk001Sub000Block164Tail =
      surrogateDiagTailX0RatChunk001Sub000Block164 := by
  unfold surrogateDiagTailX0RatChunk001Sub000Block164Head surrogateDiagTailX0RatChunk001Sub000Block164Mid surrogateDiagTailX0RatChunk001Sub000Block164Tail surrogateDiagTailX0RatChunk001Sub000Block164
  ring

def SurrogateDiagonalTailChunk001Sub000Block164HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block164HeadSum X0 = surrogateDiagTailX0RatChunk001Sub000Block164Head

def SurrogateDiagonalTailChunk001Sub000Block164MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block164MidSum X0 = surrogateDiagTailX0RatChunk001Sub000Block164Mid

def SurrogateDiagonalTailChunk001Sub000Block164TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block164TailSum X0 = surrogateDiagTailX0RatChunk001Sub000Block164Tail

theorem surrogateDiagonalTailChunk001Sub000Block164_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk001Sub000Block164HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk001Sub000Block164MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk001Sub000Block164TailCertificateAt X0) :
    surrogateDiagonalTailChunk001Sub000Block164Sum X0 = surrogateDiagTailX0RatChunk001Sub000Block164 := by
  unfold SurrogateDiagonalTailChunk001Sub000Block164HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk001Sub000Block164MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk001Sub000Block164TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk001Sub000Block164Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk001Sub000Block164_eq_head_add_mid_add_tail

/-- Block 165 covers tail-support indices [14125,14150) and q from 23285 to 23321. -/

def TailChunk001Sub000Block165Part000SupportExplicit : Finset ℕ :=
  ([23285] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block165Part000 : ℚ :=
  (1356146605375 : ℚ) / 300828314738714738688

def SurrogateDiagonalTailChunk001Sub000Block165Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23285
    = surrogateDiagTailX0RatChunk001Sub000Block165Part000

theorem surrogateDiagonalTailChunk001Sub000Block165Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block165Part000CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block165Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block165Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block165Part000CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block165Part000SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block165Part000] using hcert

def TailChunk001Sub000Block165Part001SupportExplicit : Finset ℕ :=
  ([23286] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block165Part001 : ℚ :=
  (94117551209 : ℚ) / 181344229081497600

def SurrogateDiagonalTailChunk001Sub000Block165Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23286
    = surrogateDiagTailX0RatChunk001Sub000Block165Part001

theorem surrogateDiagonalTailChunk001Sub000Block165Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block165Part001CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block165Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block165Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block165Part001CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block165Part001SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block165Part001] using hcert

def TailChunk001Sub000Block165Part002SupportExplicit : Finset ℕ :=
  ([23287] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block165Part002 : ℚ :=
  (10809820453 : ℚ) / 5507160156300902400

def SurrogateDiagonalTailChunk001Sub000Block165Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23287
    = surrogateDiagTailX0RatChunk001Sub000Block165Part002

theorem surrogateDiagonalTailChunk001Sub000Block165Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block165Part002CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block165Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block165Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block165Part002CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block165Part002SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block165Part002] using hcert

def TailChunk001Sub000Block165Part003SupportExplicit : Finset ℕ :=
  ([23289] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block165Part003 : ℚ :=
  (3303369468325 : ℚ) / 78146743438531657728

def SurrogateDiagonalTailChunk001Sub000Block165Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23289
    = surrogateDiagTailX0RatChunk001Sub000Block165Part003

theorem surrogateDiagonalTailChunk001Sub000Block165Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block165Part003CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block165Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block165Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block165Part003CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block165Part003SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block165Part003] using hcert

def TailChunk001Sub000Block165Part004SupportExplicit : Finset ℕ :=
  ([23290] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block165Part004 : ℚ :=
  (1303254163225 : ℚ) / 3587917075219218432

def SurrogateDiagonalTailChunk001Sub000Block165Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23290
    = surrogateDiagTailX0RatChunk001Sub000Block165Part004

theorem surrogateDiagonalTailChunk001Sub000Block165Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block165Part004CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block165Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block165Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block165Part004CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block165Part004SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block165Part004] using hcert

def TailChunk001Sub000Block165Part005SupportExplicit : Finset ℕ :=
  ([23291] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block165Part005 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block165Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23291
    = surrogateDiagTailX0RatChunk001Sub000Block165Part005

theorem surrogateDiagonalTailChunk001Sub000Block165Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block165Part005CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block165Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block165Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block165Part005CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block165Part005SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block165Part005] using hcert

def TailChunk001Sub000Block165Part006SupportExplicit : Finset ℕ :=
  ([23293] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block165Part006 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block165Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23293
    = surrogateDiagTailX0RatChunk001Sub000Block165Part006

theorem surrogateDiagonalTailChunk001Sub000Block165Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block165Part006CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block165Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block165Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block165Part006CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block165Part006SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block165Part006] using hcert

def TailChunk001Sub000Block165Part007SupportExplicit : Finset ℕ :=
  ([23294] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block165Part007 : ℚ :=
  (287220813275 : ℚ) / 1363825491694147584

def SurrogateDiagonalTailChunk001Sub000Block165Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23294
    = surrogateDiagTailX0RatChunk001Sub000Block165Part007

theorem surrogateDiagonalTailChunk001Sub000Block165Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block165Part007CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block165Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block165Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block165Part007CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block165Part007SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block165Part007] using hcert

def TailChunk001Sub000Block165Part008SupportExplicit : Finset ℕ :=
  ([23295] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block165Part008 : ℚ :=
  (828662208325 : ℚ) / 14855719246356283392

def SurrogateDiagonalTailChunk001Sub000Block165Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23295
    = surrogateDiagTailX0RatChunk001Sub000Block165Part008

theorem surrogateDiagonalTailChunk001Sub000Block165Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block165Part008CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block165Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block165Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block165Part008CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block165Part008SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block165Part008] using hcert

def TailChunk001Sub000Block165Part009SupportExplicit : Finset ℕ :=
  ([23297] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block165Part009 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block165Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23297
    = surrogateDiagTailX0RatChunk001Sub000Block165Part009

theorem surrogateDiagonalTailChunk001Sub000Block165Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block165Part009CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block165Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block165Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block165Part009CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block165Part009SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block165Part009] using hcert

def TailChunk001Sub000Block165Part010SupportExplicit : Finset ℕ :=
  ([23298] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block165Part010 : ℚ :=
  (979733229 : ℚ) / 1488996039393280

def SurrogateDiagonalTailChunk001Sub000Block165Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23298
    = surrogateDiagTailX0RatChunk001Sub000Block165Part010

theorem surrogateDiagonalTailChunk001Sub000Block165Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block165Part010CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block165Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block165Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block165Part010CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block165Part010SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block165Part010] using hcert

def TailChunk001Sub000Block165Part011SupportExplicit : Finset ℕ :=
  ([23299] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block165Part011 : ℚ :=
  (108884635425 : ℚ) / 204794541734040180736

def SurrogateDiagonalTailChunk001Sub000Block165Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23299
    = surrogateDiagTailX0RatChunk001Sub000Block165Part011

theorem surrogateDiagonalTailChunk001Sub000Block165Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block165Part011CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block165Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block165Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block165Part011CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block165Part011SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block165Part011] using hcert

def TailChunk001Sub000Block165Part012SupportExplicit : Finset ℕ :=
  ([23302] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block165Part012 : ℚ :=
  (109313575523 : ℚ) / 563099317344000000

def SurrogateDiagonalTailChunk001Sub000Block165Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23302
    = surrogateDiagTailX0RatChunk001Sub000Block165Part012

theorem surrogateDiagonalTailChunk001Sub000Block165Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block165Part012CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block165Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block165Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block165Part012CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block165Part012SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block165Part012] using hcert

def TailChunk001Sub000Block165Part013SupportExplicit : Finset ℕ :=
  ([23303] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block165Part013 : ℚ :=
  (53392224325 : ℚ) / 30578894359731634176

def SurrogateDiagonalTailChunk001Sub000Block165Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23303
    = surrogateDiagTailX0RatChunk001Sub000Block165Part013

theorem surrogateDiagonalTailChunk001Sub000Block165Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block165Part013CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block165Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block165Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block165Part013CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block165Part013SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block165Part013] using hcert

def TailChunk001Sub000Block165Part014SupportExplicit : Finset ℕ :=
  ([23305] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block165Part014 : ℚ :=
  (161041528825 : ℚ) / 29793031773184622592

def SurrogateDiagonalTailChunk001Sub000Block165Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23305
    = surrogateDiagTailX0RatChunk001Sub000Block165Part014

theorem surrogateDiagonalTailChunk001Sub000Block165Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block165Part014CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block165Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block165Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block165Part014CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block165Part014SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block165Part014] using hcert

def TailChunk001Sub000Block165Part015SupportExplicit : Finset ℕ :=
  ([23306] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block165Part015 : ℚ :=
  (325153252183 : ℚ) / 1654013570502787200

def SurrogateDiagonalTailChunk001Sub000Block165Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23306
    = surrogateDiagTailX0RatChunk001Sub000Block165Part015

theorem surrogateDiagonalTailChunk001Sub000Block165Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block165Part015CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block165Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block165Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block165Part015CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block165Part015SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block165Part015] using hcert

def TailChunk001Sub000Block165Part016SupportExplicit : Finset ℕ :=
  ([23307] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block165Part016 : ℚ :=
  (603790955825 : ℚ) / 18894477753065668608

def SurrogateDiagonalTailChunk001Sub000Block165Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23307
    = surrogateDiagTailX0RatChunk001Sub000Block165Part016

theorem surrogateDiagonalTailChunk001Sub000Block165Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block165Part016CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block165Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block165Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block165Part016CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block165Part016SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block165Part016] using hcert

def TailChunk001Sub000Block165Part017SupportExplicit : Finset ℕ :=
  ([23309] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block165Part017 : ℚ :=
  (51154296253 : ℚ) / 14284725280277299200

def SurrogateDiagonalTailChunk001Sub000Block165Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23309
    = surrogateDiagTailX0RatChunk001Sub000Block165Part017

theorem surrogateDiagonalTailChunk001Sub000Block165Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block165Part017CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block165Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block165Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block165Part017CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block165Part017SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block165Part017] using hcert

def TailChunk001Sub000Block165Part018SupportExplicit : Finset ℕ :=
  ([23311] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block165Part018 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block165Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23311
    = surrogateDiagTailX0RatChunk001Sub000Block165Part018

theorem surrogateDiagonalTailChunk001Sub000Block165Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block165Part018CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block165Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block165Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block165Part018CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block165Part018SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block165Part018] using hcert

def TailChunk001Sub000Block165Part019SupportExplicit : Finset ℕ :=
  ([23313] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block165Part019 : ℚ :=
  (261010624675 : ℚ) / 116379775291233927168

def SurrogateDiagonalTailChunk001Sub000Block165Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23313
    = surrogateDiagTailX0RatChunk001Sub000Block165Part019

theorem surrogateDiagonalTailChunk001Sub000Block165Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block165Part019CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block165Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block165Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block165Part019CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block165Part019SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block165Part019] using hcert

def TailChunk001Sub000Block165Part020SupportExplicit : Finset ℕ :=
  ([23314] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block165Part020 : ℚ :=
  (2123213265625 : ℚ) / 11538916286403482112

def SurrogateDiagonalTailChunk001Sub000Block165Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23314
    = surrogateDiagTailX0RatChunk001Sub000Block165Part020

theorem surrogateDiagonalTailChunk001Sub000Block165Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block165Part020CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block165Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block165Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block165Part020CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block165Part020SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block165Part020] using hcert

def TailChunk001Sub000Block165Part021SupportExplicit : Finset ℕ :=
  ([23315] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block165Part021 : ℚ :=
  (36747050125 : ℚ) / 8172485841712195584

def SurrogateDiagonalTailChunk001Sub000Block165Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23315
    = surrogateDiagTailX0RatChunk001Sub000Block165Part021

theorem surrogateDiagonalTailChunk001Sub000Block165Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block165Part021CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block165Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block165Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block165Part021CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block165Part021SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block165Part021] using hcert

def TailChunk001Sub000Block165Part022SupportExplicit : Finset ℕ :=
  ([23317] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block165Part022 : ℚ :=
  (27797246653 : ℚ) / 15939283155203203200

def SurrogateDiagonalTailChunk001Sub000Block165Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23317
    = surrogateDiagTailX0RatChunk001Sub000Block165Part022

theorem surrogateDiagonalTailChunk001Sub000Block165Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block165Part022CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block165Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block165Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block165Part022CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block165Part022SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block165Part022] using hcert

def TailChunk001Sub000Block165Part023SupportExplicit : Finset ℕ :=
  ([23318] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block165Part023 : ℚ :=
  (21992520453 : ℚ) / 114208831711969280

def SurrogateDiagonalTailChunk001Sub000Block165Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23318
    = surrogateDiagTailX0RatChunk001Sub000Block165Part023

theorem surrogateDiagonalTailChunk001Sub000Block165Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block165Part023CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block165Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block165Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block165Part023CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block165Part023SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block165Part023] using hcert

def TailChunk001Sub000Block165Part024SupportExplicit : Finset ℕ :=
  ([23321] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block165Part024 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block165Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23321
    = surrogateDiagTailX0RatChunk001Sub000Block165Part024

theorem surrogateDiagonalTailChunk001Sub000Block165Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block165Part024CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block165Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block165Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block165Part024CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block165Part024SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block165Part024] using hcert

def surrogateDiagonalTailChunk001Sub000Block165HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block165Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block165Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block165Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block165Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block165Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block165Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block165Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block165Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block165Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block165Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block165Head : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block165Part000
    + surrogateDiagTailX0RatChunk001Sub000Block165Part001
    + surrogateDiagTailX0RatChunk001Sub000Block165Part002
    + surrogateDiagTailX0RatChunk001Sub000Block165Part003
    + surrogateDiagTailX0RatChunk001Sub000Block165Part004
    + surrogateDiagTailX0RatChunk001Sub000Block165Part005
    + surrogateDiagTailX0RatChunk001Sub000Block165Part006
    + surrogateDiagTailX0RatChunk001Sub000Block165Part007
    + surrogateDiagTailX0RatChunk001Sub000Block165Part008
    + surrogateDiagTailX0RatChunk001Sub000Block165Part009

def surrogateDiagonalTailChunk001Sub000Block165MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block165Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block165Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block165Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block165Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block165Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block165Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block165Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block165Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block165Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block165Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block165Mid : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block165Part010
    + surrogateDiagTailX0RatChunk001Sub000Block165Part011
    + surrogateDiagTailX0RatChunk001Sub000Block165Part012
    + surrogateDiagTailX0RatChunk001Sub000Block165Part013
    + surrogateDiagTailX0RatChunk001Sub000Block165Part014
    + surrogateDiagTailX0RatChunk001Sub000Block165Part015
    + surrogateDiagTailX0RatChunk001Sub000Block165Part016
    + surrogateDiagTailX0RatChunk001Sub000Block165Part017
    + surrogateDiagTailX0RatChunk001Sub000Block165Part018
    + surrogateDiagTailX0RatChunk001Sub000Block165Part019

def surrogateDiagonalTailChunk001Sub000Block165TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block165Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block165Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block165Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block165Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block165Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block165Tail : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block165Part020
    + surrogateDiagTailX0RatChunk001Sub000Block165Part021
    + surrogateDiagTailX0RatChunk001Sub000Block165Part022
    + surrogateDiagTailX0RatChunk001Sub000Block165Part023
    + surrogateDiagTailX0RatChunk001Sub000Block165Part024

def surrogateDiagonalTailChunk001Sub000Block165Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk001Sub000Block165HeadSum X0
    + surrogateDiagonalTailChunk001Sub000Block165MidSum X0
    + surrogateDiagonalTailChunk001Sub000Block165TailSum X0

def surrogateDiagTailX0RatChunk001Sub000Block165 : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block165Part000
    + surrogateDiagTailX0RatChunk001Sub000Block165Part001
    + surrogateDiagTailX0RatChunk001Sub000Block165Part002
    + surrogateDiagTailX0RatChunk001Sub000Block165Part003
    + surrogateDiagTailX0RatChunk001Sub000Block165Part004
    + surrogateDiagTailX0RatChunk001Sub000Block165Part005
    + surrogateDiagTailX0RatChunk001Sub000Block165Part006
    + surrogateDiagTailX0RatChunk001Sub000Block165Part007
    + surrogateDiagTailX0RatChunk001Sub000Block165Part008
    + surrogateDiagTailX0RatChunk001Sub000Block165Part009
    + surrogateDiagTailX0RatChunk001Sub000Block165Part010
    + surrogateDiagTailX0RatChunk001Sub000Block165Part011
    + surrogateDiagTailX0RatChunk001Sub000Block165Part012
    + surrogateDiagTailX0RatChunk001Sub000Block165Part013
    + surrogateDiagTailX0RatChunk001Sub000Block165Part014
    + surrogateDiagTailX0RatChunk001Sub000Block165Part015
    + surrogateDiagTailX0RatChunk001Sub000Block165Part016
    + surrogateDiagTailX0RatChunk001Sub000Block165Part017
    + surrogateDiagTailX0RatChunk001Sub000Block165Part018
    + surrogateDiagTailX0RatChunk001Sub000Block165Part019
    + surrogateDiagTailX0RatChunk001Sub000Block165Part020
    + surrogateDiagTailX0RatChunk001Sub000Block165Part021
    + surrogateDiagTailX0RatChunk001Sub000Block165Part022
    + surrogateDiagTailX0RatChunk001Sub000Block165Part023
    + surrogateDiagTailX0RatChunk001Sub000Block165Part024

theorem surrogateDiagTailX0RatChunk001Sub000Block165_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk001Sub000Block165Head + surrogateDiagTailX0RatChunk001Sub000Block165Mid + surrogateDiagTailX0RatChunk001Sub000Block165Tail =
      surrogateDiagTailX0RatChunk001Sub000Block165 := by
  unfold surrogateDiagTailX0RatChunk001Sub000Block165Head surrogateDiagTailX0RatChunk001Sub000Block165Mid surrogateDiagTailX0RatChunk001Sub000Block165Tail surrogateDiagTailX0RatChunk001Sub000Block165
  ring

def SurrogateDiagonalTailChunk001Sub000Block165HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block165HeadSum X0 = surrogateDiagTailX0RatChunk001Sub000Block165Head

def SurrogateDiagonalTailChunk001Sub000Block165MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block165MidSum X0 = surrogateDiagTailX0RatChunk001Sub000Block165Mid

def SurrogateDiagonalTailChunk001Sub000Block165TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block165TailSum X0 = surrogateDiagTailX0RatChunk001Sub000Block165Tail

theorem surrogateDiagonalTailChunk001Sub000Block165_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk001Sub000Block165HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk001Sub000Block165MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk001Sub000Block165TailCertificateAt X0) :
    surrogateDiagonalTailChunk001Sub000Block165Sum X0 = surrogateDiagTailX0RatChunk001Sub000Block165 := by
  unfold SurrogateDiagonalTailChunk001Sub000Block165HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk001Sub000Block165MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk001Sub000Block165TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk001Sub000Block165Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk001Sub000Block165_eq_head_add_mid_add_tail

/-- Block 166 covers tail-support indices [14150,14175) and q from 23323 to 23363. -/

def TailChunk001Sub000Block166Part000SupportExplicit : Finset ℕ :=
  ([23323] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block166Part000 : ℚ :=
  (1512377199 : ℚ) / 9265164412835430400

def SurrogateDiagonalTailChunk001Sub000Block166Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23323
    = surrogateDiagTailX0RatChunk001Sub000Block166Part000

theorem surrogateDiagonalTailChunk001Sub000Block166Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block166Part000CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block166Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block166Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block166Part000CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block166Part000SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block166Part000] using hcert

def TailChunk001Sub000Block166Part001SupportExplicit : Finset ℕ :=
  ([23326] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block166Part001 : ℚ :=
  (1376260438975 : ℚ) / 7158039514698451968

def SurrogateDiagonalTailChunk001Sub000Block166Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23326
    = surrogateDiagTailX0RatChunk001Sub000Block166Part001

theorem surrogateDiagonalTailChunk001Sub000Block166Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block166Part001CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block166Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block166Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block166Part001CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block166Part001SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block166Part001] using hcert

def TailChunk001Sub000Block166Part002SupportExplicit : Finset ℕ :=
  ([23327] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block166Part002 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block166Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23327
    = surrogateDiagTailX0RatChunk001Sub000Block166Part002

theorem surrogateDiagonalTailChunk001Sub000Block166Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block166Part002CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block166Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block166Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block166Part002CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block166Part002SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block166Part002] using hcert

def TailChunk001Sub000Block166Part003SupportExplicit : Finset ℕ :=
  ([23329] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block166Part003 : ℚ :=
  (7747649401 : ℚ) / 26651408032019251200

def SurrogateDiagonalTailChunk001Sub000Block166Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23329
    = surrogateDiagTailX0RatChunk001Sub000Block166Part003

theorem surrogateDiagonalTailChunk001Sub000Block166Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block166Part003CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block166Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block166Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block166Part003CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block166Part003SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block166Part003] using hcert

def TailChunk001Sub000Block166Part004SupportExplicit : Finset ℕ :=
  ([23330] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block166Part004 : ℚ :=
  (5779907184775 : ℚ) / 18931324883347734528

def SurrogateDiagonalTailChunk001Sub000Block166Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23330
    = surrogateDiagTailX0RatChunk001Sub000Block166Part004

theorem surrogateDiagonalTailChunk001Sub000Block166Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block166Part004CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block166Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block166Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block166Part004CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block166Part004SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block166Part004] using hcert

def TailChunk001Sub000Block166Part005SupportExplicit : Finset ℕ :=
  ([23331] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block166Part005 : ℚ :=
  (35288730847 : ℚ) / 2074014720000000000

def SurrogateDiagonalTailChunk001Sub000Block166Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23331
    = surrogateDiagTailX0RatChunk001Sub000Block166Part005

theorem surrogateDiagonalTailChunk001Sub000Block166Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block166Part005CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block166Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block166Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block166Part005CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block166Part005SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block166Part005] using hcert

def TailChunk001Sub000Block166Part006SupportExplicit : Finset ℕ :=
  ([23333] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block166Part006 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block166Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23333
    = surrogateDiagTailX0RatChunk001Sub000Block166Part006

theorem surrogateDiagonalTailChunk001Sub000Block166Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block166Part006CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block166Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block166Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block166Part006CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block166Part006SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block166Part006] using hcert

def TailChunk001Sub000Block166Part007SupportExplicit : Finset ℕ :=
  ([23334] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block166Part007 : ℚ :=
  (3779760611125 : ℚ) / 9142224179377471488

def SurrogateDiagonalTailChunk001Sub000Block166Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23334
    = surrogateDiagTailX0RatChunk001Sub000Block166Part007

theorem surrogateDiagonalTailChunk001Sub000Block166Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block166Part007CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block166Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block166Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block166Part007CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block166Part007SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block166Part007] using hcert

def TailChunk001Sub000Block166Part008SupportExplicit : Finset ℕ :=
  ([23335] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block166Part008 : ℚ :=
  (544361327825 : ℚ) / 72677948563593363456

def SurrogateDiagonalTailChunk001Sub000Block166Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23335
    = surrogateDiagTailX0RatChunk001Sub000Block166Part008

theorem surrogateDiagonalTailChunk001Sub000Block166Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block166Part008CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block166Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block166Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block166Part008CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block166Part008SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block166Part008] using hcert

def TailChunk001Sub000Block166Part009SupportExplicit : Finset ℕ :=
  ([23338] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block166Part009 : ℚ :=
  (7360022375 : ℚ) / 27862741069642143

def SurrogateDiagonalTailChunk001Sub000Block166Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23338
    = surrogateDiagTailX0RatChunk001Sub000Block166Part009

theorem surrogateDiagonalTailChunk001Sub000Block166Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block166Part009CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block166Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block166Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block166Part009CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block166Part009SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block166Part009] using hcert

def TailChunk001Sub000Block166Part010SupportExplicit : Finset ℕ :=
  ([23339] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block166Part010 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block166Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23339
    = surrogateDiagTailX0RatChunk001Sub000Block166Part010

theorem surrogateDiagonalTailChunk001Sub000Block166Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block166Part010CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block166Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block166Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block166Part010CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block166Part010SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block166Part010] using hcert

def TailChunk001Sub000Block166Part011SupportExplicit : Finset ℕ :=
  ([23341] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block166Part011 : ℚ :=
  (38031975 : ℚ) / 61720001260158976

def SurrogateDiagonalTailChunk001Sub000Block166Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23341
    = surrogateDiagTailX0RatChunk001Sub000Block166Part011

theorem surrogateDiagonalTailChunk001Sub000Block166Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block166Part011CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block166Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block166Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block166Part011CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block166Part011SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block166Part011] using hcert

def TailChunk001Sub000Block166Part012SupportExplicit : Finset ℕ :=
  ([23342] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block166Part012 : ℚ :=
  (289482197407 : ℚ) / 1262729455392000000

def SurrogateDiagonalTailChunk001Sub000Block166Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23342
    = surrogateDiagTailX0RatChunk001Sub000Block166Part012

theorem surrogateDiagonalTailChunk001Sub000Block166Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block166Part012CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block166Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block166Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block166Part012CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block166Part012SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block166Part012] using hcert

def TailChunk001Sub000Block166Part013SupportExplicit : Finset ℕ :=
  ([23343] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block166Part013 : ℚ :=
  (6533387221 : ℚ) / 5063512500000000000

def SurrogateDiagonalTailChunk001Sub000Block166Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23343
    = surrogateDiagTailX0RatChunk001Sub000Block166Part013

theorem surrogateDiagonalTailChunk001Sub000Block166Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block166Part013CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block166Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block166Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block166Part013CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block166Part013SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block166Part013] using hcert

def TailChunk001Sub000Block166Part014SupportExplicit : Finset ℕ :=
  ([23345] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block166Part014 : ℚ :=
  (2090218076425 : ℚ) / 119452343479113351168

def SurrogateDiagonalTailChunk001Sub000Block166Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23345
    = surrogateDiagTailX0RatChunk001Sub000Block166Part014

theorem surrogateDiagonalTailChunk001Sub000Block166Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block166Part014CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block166Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block166Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block166Part014CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block166Part014SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block166Part014] using hcert

def TailChunk001Sub000Block166Part015SupportExplicit : Finset ℕ :=
  ([23347] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block166Part015 : ℚ :=
  (8376511627 : ℚ) / 26464217128044595200

def SurrogateDiagonalTailChunk001Sub000Block166Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23347
    = surrogateDiagTailX0RatChunk001Sub000Block166Part015

theorem surrogateDiagonalTailChunk001Sub000Block166Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block166Part015CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block166Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block166Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block166Part015CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block166Part015SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block166Part015] using hcert

def TailChunk001Sub000Block166Part016SupportExplicit : Finset ℕ :=
  ([23349] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block166Part016 : ℚ :=
  (5755300321 : ℚ) / 5227499679613747200

def SurrogateDiagonalTailChunk001Sub000Block166Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23349
    = surrogateDiagTailX0RatChunk001Sub000Block166Part016

theorem surrogateDiagonalTailChunk001Sub000Block166Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block166Part016CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block166Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block166Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block166Part016CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block166Part016SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block166Part016] using hcert

def TailChunk001Sub000Block166Part017SupportExplicit : Finset ℕ :=
  ([23351] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block166Part017 : ℚ :=
  (382392551725 : ℚ) / 596912050460929148928

def SurrogateDiagonalTailChunk001Sub000Block166Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23351
    = surrogateDiagTailX0RatChunk001Sub000Block166Part017

theorem surrogateDiagonalTailChunk001Sub000Block166Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block166Part017CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block166Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block166Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block166Part017CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block166Part017SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block166Part017] using hcert

def TailChunk001Sub000Block166Part018SupportExplicit : Finset ℕ :=
  ([23354] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block166Part018 : ℚ :=
  (2130505140625 : ℚ) / 11618316759467511072

def SurrogateDiagonalTailChunk001Sub000Block166Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23354
    = surrogateDiagTailX0RatChunk001Sub000Block166Part018

theorem surrogateDiagonalTailChunk001Sub000Block166Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block166Part018CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block166Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block166Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block166Part018CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block166Part018SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block166Part018] using hcert

def TailChunk001Sub000Block166Part019SupportExplicit : Finset ℕ :=
  ([23357] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block166Part019 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block166Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23357
    = surrogateDiagTailX0RatChunk001Sub000Block166Part019

theorem surrogateDiagonalTailChunk001Sub000Block166Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block166Part019CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block166Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block166Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block166Part019CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block166Part019SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block166Part019] using hcert

def TailChunk001Sub000Block166Part020SupportExplicit : Finset ℕ :=
  ([23358] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block166Part020 : ℚ :=
  (1736693588975 : ℚ) / 3542714578699812864

def SurrogateDiagonalTailChunk001Sub000Block166Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23358
    = surrogateDiagTailX0RatChunk001Sub000Block166Part020

theorem surrogateDiagonalTailChunk001Sub000Block166Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block166Part020CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block166Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block166Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block166Part020CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block166Part020SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block166Part020] using hcert

def TailChunk001Sub000Block166Part021SupportExplicit : Finset ℕ :=
  ([23359] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block166Part021 : ℚ :=
  (6705817667 : ℚ) / 1548363157973452800

def SurrogateDiagonalTailChunk001Sub000Block166Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23359
    = surrogateDiagTailX0RatChunk001Sub000Block166Part021

theorem surrogateDiagonalTailChunk001Sub000Block166Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block166Part021CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block166Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block166Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block166Part021CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block166Part021SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block166Part021] using hcert

def TailChunk001Sub000Block166Part022SupportExplicit : Finset ℕ :=
  ([23361] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block166Part022 : ℚ :=
  (31529491975 : ℚ) / 8160808922311458816

def SurrogateDiagonalTailChunk001Sub000Block166Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23361
    = surrogateDiagTailX0RatChunk001Sub000Block166Part022

theorem surrogateDiagonalTailChunk001Sub000Block166Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block166Part022CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block166Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block166Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block166Part022CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block166Part022SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block166Part022] using hcert

def TailChunk001Sub000Block166Part023SupportExplicit : Finset ℕ :=
  ([23362] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block166Part023 : ℚ :=
  (3411144025 : ℚ) / 18614793436004352

def SurrogateDiagonalTailChunk001Sub000Block166Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23362
    = surrogateDiagTailX0RatChunk001Sub000Block166Part023

theorem surrogateDiagonalTailChunk001Sub000Block166Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block166Part023CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block166Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block166Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block166Part023CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block166Part023SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block166Part023] using hcert

def TailChunk001Sub000Block166Part024SupportExplicit : Finset ℕ :=
  ([23363] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block166Part024 : ℚ :=
  (1827164453 : ℚ) / 9200767336742246400

def SurrogateDiagonalTailChunk001Sub000Block166Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23363
    = surrogateDiagTailX0RatChunk001Sub000Block166Part024

theorem surrogateDiagonalTailChunk001Sub000Block166Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block166Part024CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block166Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block166Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block166Part024CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block166Part024SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block166Part024] using hcert

def surrogateDiagonalTailChunk001Sub000Block166HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block166Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block166Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block166Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block166Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block166Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block166Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block166Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block166Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block166Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block166Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block166Head : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block166Part000
    + surrogateDiagTailX0RatChunk001Sub000Block166Part001
    + surrogateDiagTailX0RatChunk001Sub000Block166Part002
    + surrogateDiagTailX0RatChunk001Sub000Block166Part003
    + surrogateDiagTailX0RatChunk001Sub000Block166Part004
    + surrogateDiagTailX0RatChunk001Sub000Block166Part005
    + surrogateDiagTailX0RatChunk001Sub000Block166Part006
    + surrogateDiagTailX0RatChunk001Sub000Block166Part007
    + surrogateDiagTailX0RatChunk001Sub000Block166Part008
    + surrogateDiagTailX0RatChunk001Sub000Block166Part009

def surrogateDiagonalTailChunk001Sub000Block166MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block166Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block166Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block166Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block166Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block166Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block166Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block166Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block166Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block166Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block166Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block166Mid : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block166Part010
    + surrogateDiagTailX0RatChunk001Sub000Block166Part011
    + surrogateDiagTailX0RatChunk001Sub000Block166Part012
    + surrogateDiagTailX0RatChunk001Sub000Block166Part013
    + surrogateDiagTailX0RatChunk001Sub000Block166Part014
    + surrogateDiagTailX0RatChunk001Sub000Block166Part015
    + surrogateDiagTailX0RatChunk001Sub000Block166Part016
    + surrogateDiagTailX0RatChunk001Sub000Block166Part017
    + surrogateDiagTailX0RatChunk001Sub000Block166Part018
    + surrogateDiagTailX0RatChunk001Sub000Block166Part019

def surrogateDiagonalTailChunk001Sub000Block166TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block166Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block166Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block166Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block166Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block166Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block166Tail : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block166Part020
    + surrogateDiagTailX0RatChunk001Sub000Block166Part021
    + surrogateDiagTailX0RatChunk001Sub000Block166Part022
    + surrogateDiagTailX0RatChunk001Sub000Block166Part023
    + surrogateDiagTailX0RatChunk001Sub000Block166Part024

def surrogateDiagonalTailChunk001Sub000Block166Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk001Sub000Block166HeadSum X0
    + surrogateDiagonalTailChunk001Sub000Block166MidSum X0
    + surrogateDiagonalTailChunk001Sub000Block166TailSum X0

def surrogateDiagTailX0RatChunk001Sub000Block166 : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block166Part000
    + surrogateDiagTailX0RatChunk001Sub000Block166Part001
    + surrogateDiagTailX0RatChunk001Sub000Block166Part002
    + surrogateDiagTailX0RatChunk001Sub000Block166Part003
    + surrogateDiagTailX0RatChunk001Sub000Block166Part004
    + surrogateDiagTailX0RatChunk001Sub000Block166Part005
    + surrogateDiagTailX0RatChunk001Sub000Block166Part006
    + surrogateDiagTailX0RatChunk001Sub000Block166Part007
    + surrogateDiagTailX0RatChunk001Sub000Block166Part008
    + surrogateDiagTailX0RatChunk001Sub000Block166Part009
    + surrogateDiagTailX0RatChunk001Sub000Block166Part010
    + surrogateDiagTailX0RatChunk001Sub000Block166Part011
    + surrogateDiagTailX0RatChunk001Sub000Block166Part012
    + surrogateDiagTailX0RatChunk001Sub000Block166Part013
    + surrogateDiagTailX0RatChunk001Sub000Block166Part014
    + surrogateDiagTailX0RatChunk001Sub000Block166Part015
    + surrogateDiagTailX0RatChunk001Sub000Block166Part016
    + surrogateDiagTailX0RatChunk001Sub000Block166Part017
    + surrogateDiagTailX0RatChunk001Sub000Block166Part018
    + surrogateDiagTailX0RatChunk001Sub000Block166Part019
    + surrogateDiagTailX0RatChunk001Sub000Block166Part020
    + surrogateDiagTailX0RatChunk001Sub000Block166Part021
    + surrogateDiagTailX0RatChunk001Sub000Block166Part022
    + surrogateDiagTailX0RatChunk001Sub000Block166Part023
    + surrogateDiagTailX0RatChunk001Sub000Block166Part024

theorem surrogateDiagTailX0RatChunk001Sub000Block166_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk001Sub000Block166Head + surrogateDiagTailX0RatChunk001Sub000Block166Mid + surrogateDiagTailX0RatChunk001Sub000Block166Tail =
      surrogateDiagTailX0RatChunk001Sub000Block166 := by
  unfold surrogateDiagTailX0RatChunk001Sub000Block166Head surrogateDiagTailX0RatChunk001Sub000Block166Mid surrogateDiagTailX0RatChunk001Sub000Block166Tail surrogateDiagTailX0RatChunk001Sub000Block166
  ring

def SurrogateDiagonalTailChunk001Sub000Block166HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block166HeadSum X0 = surrogateDiagTailX0RatChunk001Sub000Block166Head

def SurrogateDiagonalTailChunk001Sub000Block166MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block166MidSum X0 = surrogateDiagTailX0RatChunk001Sub000Block166Mid

def SurrogateDiagonalTailChunk001Sub000Block166TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block166TailSum X0 = surrogateDiagTailX0RatChunk001Sub000Block166Tail

theorem surrogateDiagonalTailChunk001Sub000Block166_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk001Sub000Block166HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk001Sub000Block166MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk001Sub000Block166TailCertificateAt X0) :
    surrogateDiagonalTailChunk001Sub000Block166Sum X0 = surrogateDiagTailX0RatChunk001Sub000Block166 := by
  unfold SurrogateDiagonalTailChunk001Sub000Block166HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk001Sub000Block166MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk001Sub000Block166TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk001Sub000Block166Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk001Sub000Block166_eq_head_add_mid_add_tail

/-- Block 167 covers tail-support indices [14175,14200) and q from 23365 to 23402. -/

def TailChunk001Sub000Block167Part000SupportExplicit : Finset ℕ :=
  ([23365] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block167Part000 : ℚ :=
  (2729152033525 : ℚ) / 304984775655495303168

def SurrogateDiagonalTailChunk001Sub000Block167Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23365
    = surrogateDiagTailX0RatChunk001Sub000Block167Part000

theorem surrogateDiagonalTailChunk001Sub000Block167Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block167Part000CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block167Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block167Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block167Part000CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block167Part000SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block167Part000] using hcert

def TailChunk001Sub000Block167Part001SupportExplicit : Finset ℕ :=
  ([23366] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block167Part001 : ℚ :=
  (1652604595075 : ℚ) / 6271278017605120512

def SurrogateDiagonalTailChunk001Sub000Block167Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23366
    = surrogateDiagTailX0RatChunk001Sub000Block167Part001

theorem surrogateDiagonalTailChunk001Sub000Block167Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block167Part001CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block167Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block167Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block167Part001CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block167Part001SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block167Part001] using hcert

def TailChunk001Sub000Block167Part002SupportExplicit : Finset ℕ :=
  ([23367] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block167Part002 : ℚ :=
  (41675 : ℚ) / 9810078975645696

def SurrogateDiagonalTailChunk001Sub000Block167Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23367
    = surrogateDiagTailX0RatChunk001Sub000Block167Part002

theorem surrogateDiagonalTailChunk001Sub000Block167Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block167Part002CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block167Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block167Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block167Part002CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block167Part002SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block167Part002] using hcert

def TailChunk001Sub000Block167Part003SupportExplicit : Finset ℕ :=
  ([23369] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block167Part003 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block167Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23369
    = surrogateDiagTailX0RatChunk001Sub000Block167Part003

theorem surrogateDiagonalTailChunk001Sub000Block167Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block167Part003CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block167Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block167Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block167Part003CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block167Part003SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block167Part003] using hcert

def TailChunk001Sub000Block167Part004SupportExplicit : Finset ℕ :=
  ([23370] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block167Part004 : ℚ :=
  (3242205113 : ℚ) / 3440541538713600

def SurrogateDiagonalTailChunk001Sub000Block167Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23370
    = surrogateDiagTailX0RatChunk001Sub000Block167Part004

theorem surrogateDiagonalTailChunk001Sub000Block167Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block167Part004CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block167Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block167Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block167Part004CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block167Part004SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block167Part004] using hcert

def TailChunk001Sub000Block167Part005SupportExplicit : Finset ℕ :=
  ([23371] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block167Part005 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block167Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23371
    = surrogateDiagTailX0RatChunk001Sub000Block167Part005

theorem surrogateDiagonalTailChunk001Sub000Block167Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block167Part005CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block167Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block167Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block167Part005CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block167Part005SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block167Part005] using hcert

def TailChunk001Sub000Block167Part006SupportExplicit : Finset ℕ :=
  ([23374] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block167Part006 : ℚ :=
  (897147133 : ℚ) / 3441975097688064

def SurrogateDiagonalTailChunk001Sub000Block167Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23374
    = surrogateDiagTailX0RatChunk001Sub000Block167Part006

theorem surrogateDiagonalTailChunk001Sub000Block167Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block167Part006CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block167Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block167Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block167Part006CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block167Part006SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block167Part006] using hcert

def TailChunk001Sub000Block167Part007SupportExplicit : Finset ℕ :=
  ([23377] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block167Part007 : ℚ :=
  (131944421 : ℚ) / 880778633910681600

def SurrogateDiagonalTailChunk001Sub000Block167Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23377
    = surrogateDiagTailX0RatChunk001Sub000Block167Part007

theorem surrogateDiagonalTailChunk001Sub000Block167Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block167Part007CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block167Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block167Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block167Part007CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block167Part007SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block167Part007] using hcert

def TailChunk001Sub000Block167Part008SupportExplicit : Finset ℕ :=
  ([23378] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block167Part008 : ℚ :=
  (2134886265625 : ℚ) / 11666153306677473792

def SurrogateDiagonalTailChunk001Sub000Block167Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23378
    = surrogateDiagTailX0RatChunk001Sub000Block167Part008

theorem surrogateDiagonalTailChunk001Sub000Block167Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block167Part008CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block167Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block167Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block167Part008CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block167Part008SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block167Part008] using hcert

def TailChunk001Sub000Block167Part009SupportExplicit : Finset ℕ :=
  ([23379] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block167Part009 : ℚ :=
  (125025 : ℚ) / 29490746260717568

def SurrogateDiagonalTailChunk001Sub000Block167Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23379
    = surrogateDiagTailX0RatChunk001Sub000Block167Part009

theorem surrogateDiagonalTailChunk001Sub000Block167Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block167Part009CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block167Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block167Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block167Part009CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block167Part009SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block167Part009] using hcert

def TailChunk001Sub000Block167Part010SupportExplicit : Finset ℕ :=
  ([23381] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block167Part010 : ℚ :=
  (101465362825 : ℚ) / 706092018763838663808

def SurrogateDiagonalTailChunk001Sub000Block167Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23381
    = surrogateDiagTailX0RatChunk001Sub000Block167Part010

theorem surrogateDiagonalTailChunk001Sub000Block167Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block167Part010CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block167Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block167Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block167Part010CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block167Part010SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block167Part010] using hcert

def TailChunk001Sub000Block167Part011SupportExplicit : Finset ℕ :=
  ([23383] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block167Part011 : ℚ :=
  (31603934275 : ℚ) / 173964080335390659072

def SurrogateDiagonalTailChunk001Sub000Block167Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23383
    = surrogateDiagTailX0RatChunk001Sub000Block167Part011

theorem surrogateDiagonalTailChunk001Sub000Block167Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block167Part011CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block167Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block167Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block167Part011CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block167Part011SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block167Part011] using hcert

def TailChunk001Sub000Block167Part012SupportExplicit : Finset ℕ :=
  ([23385] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block167Part012 : ℚ :=
  (114117975125 : ℚ) / 7543391241847934976

def SurrogateDiagonalTailChunk001Sub000Block167Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23385
    = surrogateDiagTailX0RatChunk001Sub000Block167Part012

theorem surrogateDiagonalTailChunk001Sub000Block167Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block167Part012CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block167Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block167Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block167Part012CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block167Part012SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block167Part012] using hcert

def TailChunk001Sub000Block167Part013SupportExplicit : Finset ℕ :=
  ([23386] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block167Part013 : ℚ :=
  (293402653921 : ℚ) / 1272286494753667200

def SurrogateDiagonalTailChunk001Sub000Block167Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23386
    = surrogateDiagTailX0RatChunk001Sub000Block167Part013

theorem surrogateDiagonalTailChunk001Sub000Block167Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block167Part013CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block167Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block167Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block167Part013CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block167Part013SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block167Part013] using hcert

def TailChunk001Sub000Block167Part014SupportExplicit : Finset ℕ :=
  ([23387] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block167Part014 : ℚ :=
  (1701546988375 : ℚ) / 288613542759852146688

def SurrogateDiagonalTailChunk001Sub000Block167Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23387
    = surrogateDiagTailX0RatChunk001Sub000Block167Part014

theorem surrogateDiagonalTailChunk001Sub000Block167Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block167Part014CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block167Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block167Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block167Part014CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block167Part014SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block167Part014] using hcert

def TailChunk001Sub000Block167Part015SupportExplicit : Finset ℕ :=
  ([23389] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block167Part015 : ℚ :=
  (1704981397 : ℚ) / 2670267727380124800

def SurrogateDiagonalTailChunk001Sub000Block167Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23389
    = surrogateDiagTailX0RatChunk001Sub000Block167Part015

theorem surrogateDiagonalTailChunk001Sub000Block167Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block167Part015CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block167Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block167Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block167Part015CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block167Part015SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block167Part015] using hcert

def TailChunk001Sub000Block167Part016SupportExplicit : Finset ℕ :=
  ([23390] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block167Part016 : ℚ :=
  (5809681237225 : ℚ) / 19126911636626884608

def SurrogateDiagonalTailChunk001Sub000Block167Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23390
    = surrogateDiagTailX0RatChunk001Sub000Block167Part016

theorem surrogateDiagonalTailChunk001Sub000Block167Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block167Part016CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block167Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block167Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block167Part016CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block167Part016SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block167Part016] using hcert

def TailChunk001Sub000Block167Part017SupportExplicit : Finset ℕ :=
  ([23393] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block167Part017 : ℚ :=
  (95221818775 : ℚ) / 710513139741589536768

def SurrogateDiagonalTailChunk001Sub000Block167Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23393
    = surrogateDiagTailX0RatChunk001Sub000Block167Part017

theorem surrogateDiagonalTailChunk001Sub000Block167Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block167Part017CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block167Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block167Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block167Part017CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block167Part017SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block167Part017] using hcert

def TailChunk001Sub000Block167Part018SupportExplicit : Finset ℕ :=
  ([23394] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block167Part018 : ℚ :=
  (1528154090675 : ℚ) / 2477541932881035264

def SurrogateDiagonalTailChunk001Sub000Block167Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23394
    = surrogateDiagTailX0RatChunk001Sub000Block167Part018

theorem surrogateDiagonalTailChunk001Sub000Block167Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block167Part018CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block167Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block167Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block167Part018CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block167Part018SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block167Part018] using hcert

def TailChunk001Sub000Block167Part019SupportExplicit : Finset ℕ :=
  ([23395] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block167Part019 : ℚ :=
  (456326950875 : ℚ) / 102184832967880185856

def SurrogateDiagonalTailChunk001Sub000Block167Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23395
    = surrogateDiagTailX0RatChunk001Sub000Block167Part019

theorem surrogateDiagonalTailChunk001Sub000Block167Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block167Part019CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block167Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block167Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block167Part019CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block167Part019SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block167Part019] using hcert

def TailChunk001Sub000Block167Part020SupportExplicit : Finset ℕ :=
  ([23397] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block167Part020 : ℚ :=
  (16544589703 : ℚ) / 4021053613048627200

def SurrogateDiagonalTailChunk001Sub000Block167Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23397
    = surrogateDiagTailX0RatChunk001Sub000Block167Part020

theorem surrogateDiagonalTailChunk001Sub000Block167Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block167Part020CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block167Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block167Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block167Part020CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block167Part020SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block167Part020] using hcert

def TailChunk001Sub000Block167Part021SupportExplicit : Finset ℕ :=
  ([23398] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block167Part021 : ℚ :=
  (2138540640625 : ℚ) / 11706129808426133202

def SurrogateDiagonalTailChunk001Sub000Block167Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23398
    = surrogateDiagTailX0RatChunk001Sub000Block167Part021

theorem surrogateDiagonalTailChunk001Sub000Block167Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block167Part021CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block167Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block167Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block167Part021CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block167Part021SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block167Part021] using hcert

def TailChunk001Sub000Block167Part022SupportExplicit : Finset ℕ :=
  ([23399] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block167Part022 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block167Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23399
    = surrogateDiagTailX0RatChunk001Sub000Block167Part022

theorem surrogateDiagonalTailChunk001Sub000Block167Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block167Part022CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block167Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block167Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block167Part022CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block167Part022SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block167Part022] using hcert

def TailChunk001Sub000Block167Part023SupportExplicit : Finset ℕ :=
  ([23401] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block167Part023 : ℚ :=
  (698858065175 : ℚ) / 202128543695153507904

def SurrogateDiagonalTailChunk001Sub000Block167Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23401
    = surrogateDiagTailX0RatChunk001Sub000Block167Part023

theorem surrogateDiagonalTailChunk001Sub000Block167Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block167Part023CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block167Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block167Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block167Part023CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block167Part023SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block167Part023] using hcert

def TailChunk001Sub000Block167Part024SupportExplicit : Finset ℕ :=
  ([23402] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block167Part024 : ℚ :=
  (136913401 : ℚ) / 749704794976800

def SurrogateDiagonalTailChunk001Sub000Block167Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23402
    = surrogateDiagTailX0RatChunk001Sub000Block167Part024

theorem surrogateDiagonalTailChunk001Sub000Block167Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block167Part024CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block167Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block167Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block167Part024CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block167Part024SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block167Part024] using hcert

def surrogateDiagonalTailChunk001Sub000Block167HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block167Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block167Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block167Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block167Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block167Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block167Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block167Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block167Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block167Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block167Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block167Head : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block167Part000
    + surrogateDiagTailX0RatChunk001Sub000Block167Part001
    + surrogateDiagTailX0RatChunk001Sub000Block167Part002
    + surrogateDiagTailX0RatChunk001Sub000Block167Part003
    + surrogateDiagTailX0RatChunk001Sub000Block167Part004
    + surrogateDiagTailX0RatChunk001Sub000Block167Part005
    + surrogateDiagTailX0RatChunk001Sub000Block167Part006
    + surrogateDiagTailX0RatChunk001Sub000Block167Part007
    + surrogateDiagTailX0RatChunk001Sub000Block167Part008
    + surrogateDiagTailX0RatChunk001Sub000Block167Part009

def surrogateDiagonalTailChunk001Sub000Block167MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block167Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block167Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block167Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block167Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block167Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block167Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block167Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block167Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block167Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block167Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block167Mid : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block167Part010
    + surrogateDiagTailX0RatChunk001Sub000Block167Part011
    + surrogateDiagTailX0RatChunk001Sub000Block167Part012
    + surrogateDiagTailX0RatChunk001Sub000Block167Part013
    + surrogateDiagTailX0RatChunk001Sub000Block167Part014
    + surrogateDiagTailX0RatChunk001Sub000Block167Part015
    + surrogateDiagTailX0RatChunk001Sub000Block167Part016
    + surrogateDiagTailX0RatChunk001Sub000Block167Part017
    + surrogateDiagTailX0RatChunk001Sub000Block167Part018
    + surrogateDiagTailX0RatChunk001Sub000Block167Part019

def surrogateDiagonalTailChunk001Sub000Block167TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block167Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block167Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block167Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block167Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block167Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block167Tail : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block167Part020
    + surrogateDiagTailX0RatChunk001Sub000Block167Part021
    + surrogateDiagTailX0RatChunk001Sub000Block167Part022
    + surrogateDiagTailX0RatChunk001Sub000Block167Part023
    + surrogateDiagTailX0RatChunk001Sub000Block167Part024

def surrogateDiagonalTailChunk001Sub000Block167Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk001Sub000Block167HeadSum X0
    + surrogateDiagonalTailChunk001Sub000Block167MidSum X0
    + surrogateDiagonalTailChunk001Sub000Block167TailSum X0

def surrogateDiagTailX0RatChunk001Sub000Block167 : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block167Part000
    + surrogateDiagTailX0RatChunk001Sub000Block167Part001
    + surrogateDiagTailX0RatChunk001Sub000Block167Part002
    + surrogateDiagTailX0RatChunk001Sub000Block167Part003
    + surrogateDiagTailX0RatChunk001Sub000Block167Part004
    + surrogateDiagTailX0RatChunk001Sub000Block167Part005
    + surrogateDiagTailX0RatChunk001Sub000Block167Part006
    + surrogateDiagTailX0RatChunk001Sub000Block167Part007
    + surrogateDiagTailX0RatChunk001Sub000Block167Part008
    + surrogateDiagTailX0RatChunk001Sub000Block167Part009
    + surrogateDiagTailX0RatChunk001Sub000Block167Part010
    + surrogateDiagTailX0RatChunk001Sub000Block167Part011
    + surrogateDiagTailX0RatChunk001Sub000Block167Part012
    + surrogateDiagTailX0RatChunk001Sub000Block167Part013
    + surrogateDiagTailX0RatChunk001Sub000Block167Part014
    + surrogateDiagTailX0RatChunk001Sub000Block167Part015
    + surrogateDiagTailX0RatChunk001Sub000Block167Part016
    + surrogateDiagTailX0RatChunk001Sub000Block167Part017
    + surrogateDiagTailX0RatChunk001Sub000Block167Part018
    + surrogateDiagTailX0RatChunk001Sub000Block167Part019
    + surrogateDiagTailX0RatChunk001Sub000Block167Part020
    + surrogateDiagTailX0RatChunk001Sub000Block167Part021
    + surrogateDiagTailX0RatChunk001Sub000Block167Part022
    + surrogateDiagTailX0RatChunk001Sub000Block167Part023
    + surrogateDiagTailX0RatChunk001Sub000Block167Part024

theorem surrogateDiagTailX0RatChunk001Sub000Block167_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk001Sub000Block167Head + surrogateDiagTailX0RatChunk001Sub000Block167Mid + surrogateDiagTailX0RatChunk001Sub000Block167Tail =
      surrogateDiagTailX0RatChunk001Sub000Block167 := by
  unfold surrogateDiagTailX0RatChunk001Sub000Block167Head surrogateDiagTailX0RatChunk001Sub000Block167Mid surrogateDiagTailX0RatChunk001Sub000Block167Tail surrogateDiagTailX0RatChunk001Sub000Block167
  ring

def SurrogateDiagonalTailChunk001Sub000Block167HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block167HeadSum X0 = surrogateDiagTailX0RatChunk001Sub000Block167Head

def SurrogateDiagonalTailChunk001Sub000Block167MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block167MidSum X0 = surrogateDiagTailX0RatChunk001Sub000Block167Mid

def SurrogateDiagonalTailChunk001Sub000Block167TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block167TailSum X0 = surrogateDiagTailX0RatChunk001Sub000Block167Tail

theorem surrogateDiagonalTailChunk001Sub000Block167_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk001Sub000Block167HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk001Sub000Block167MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk001Sub000Block167TailCertificateAt X0) :
    surrogateDiagonalTailChunk001Sub000Block167Sum X0 = surrogateDiagTailX0RatChunk001Sub000Block167 := by
  unfold SurrogateDiagonalTailChunk001Sub000Block167HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk001Sub000Block167MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk001Sub000Block167TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk001Sub000Block167Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk001Sub000Block167_eq_head_add_mid_add_tail

/-- Block 168 covers tail-support indices [14200,14225) and q from 23403 to 23442. -/

def TailChunk001Sub000Block168Part000SupportExplicit : Finset ℕ :=
  ([23403] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block168Part000 : ℚ :=
  (183536965225 : ℚ) / 126858082620025602048

def SurrogateDiagonalTailChunk001Sub000Block168Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23403
    = surrogateDiagTailX0RatChunk001Sub000Block168Part000

theorem surrogateDiagonalTailChunk001Sub000Block168Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block168Part000CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block168Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block168Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block168Part000CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block168Part000SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block168Part000] using hcert

def TailChunk001Sub000Block168Part001SupportExplicit : Finset ℕ :=
  ([23405] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block168Part001 : ℚ :=
  (59011694317 : ℚ) / 10499699520000000000

def SurrogateDiagonalTailChunk001Sub000Block168Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23405
    = surrogateDiagTailX0RatChunk001Sub000Block168Part001

theorem surrogateDiagonalTailChunk001Sub000Block168Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block168Part001CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block168Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block168Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block168Part001CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block168Part001SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block168Part001] using hcert

def TailChunk001Sub000Block168Part002SupportExplicit : Finset ℕ :=
  ([23406] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block168Part002 : ℚ :=
  (3633682097575 : ℚ) / 8099040632399874048

def SurrogateDiagonalTailChunk001Sub000Block168Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23406
    = surrogateDiagTailX0RatChunk001Sub000Block168Part002

theorem surrogateDiagonalTailChunk001Sub000Block168Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block168Part002CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block168Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block168Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block168Part002CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block168Part002SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block168Part002] using hcert

def TailChunk001Sub000Block168Part003SupportExplicit : Finset ℕ :=
  ([23407] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block168Part003 : ℚ :=
  (27277815025 : ℚ) / 176645558191295373312

def SurrogateDiagonalTailChunk001Sub000Block168Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23407
    = surrogateDiagTailX0RatChunk001Sub000Block168Part003

theorem surrogateDiagonalTailChunk001Sub000Block168Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block168Part003CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block168Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block168Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block168Part003CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block168Part003SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block168Part003] using hcert

def TailChunk001Sub000Block168Part004SupportExplicit : Finset ℕ :=
  ([23410] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block168Part004 : ℚ :=
  (232784916919 : ℚ) / 767697710056243200

def SurrogateDiagonalTailChunk001Sub000Block168Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23410
    = surrogateDiagTailX0RatChunk001Sub000Block168Part004

theorem surrogateDiagonalTailChunk001Sub000Block168Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block168Part004CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block168Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block168Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block168Part004CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block168Part004SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block168Part004] using hcert

def TailChunk001Sub000Block168Part005SupportExplicit : Finset ℕ :=
  ([23411] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block168Part005 : ℚ :=
  (1559755457 : ℚ) / 5405753446502400000

def SurrogateDiagonalTailChunk001Sub000Block168Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23411
    = surrogateDiagTailX0RatChunk001Sub000Block168Part005

theorem surrogateDiagonalTailChunk001Sub000Block168Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block168Part005CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block168Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block168Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block168Part005CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block168Part005SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block168Part005] using hcert

def TailChunk001Sub000Block168Part006SupportExplicit : Finset ℕ :=
  ([23413] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block168Part006 : ℚ :=
  (12220202351 : ℚ) / 10886088462336000000

def SurrogateDiagonalTailChunk001Sub000Block168Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23413
    = surrogateDiagTailX0RatChunk001Sub000Block168Part006

theorem surrogateDiagonalTailChunk001Sub000Block168Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block168Part006CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block168Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block168Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block168Part006CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block168Part006SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block168Part006] using hcert

def TailChunk001Sub000Block168Part007SupportExplicit : Finset ℕ :=
  ([23414] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block168Part007 : ℚ :=
  (2653157386425 : ℚ) / 13003227970282756096

def SurrogateDiagonalTailChunk001Sub000Block168Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23414
    = surrogateDiagTailX0RatChunk001Sub000Block168Part007

theorem surrogateDiagonalTailChunk001Sub000Block168Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block168Part007CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block168Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block168Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block168Part007CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block168Part007SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block168Part007] using hcert

def TailChunk001Sub000Block168Part008SupportExplicit : Finset ℕ :=
  ([23415] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block168Part008 : ℚ :=
  (1117962769525 : ℚ) / 32240643853685096448

def SurrogateDiagonalTailChunk001Sub000Block168Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23415
    = surrogateDiagTailX0RatChunk001Sub000Block168Part008

theorem surrogateDiagonalTailChunk001Sub000Block168Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block168Part008CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block168Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block168Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block168Part008CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block168Part008SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block168Part008] using hcert

def TailChunk001Sub000Block168Part009SupportExplicit : Finset ℕ :=
  ([23417] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block168Part009 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block168Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23417
    = surrogateDiagTailX0RatChunk001Sub000Block168Part009

theorem surrogateDiagonalTailChunk001Sub000Block168Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block168Part009CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block168Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block168Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block168Part009CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block168Part009SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block168Part009] using hcert

def TailChunk001Sub000Block168Part010SupportExplicit : Finset ℕ :=
  ([23419] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block168Part010 : ℚ :=
  (4867768951 : ℚ) / 2930051843398041600

def SurrogateDiagonalTailChunk001Sub000Block168Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23419
    = surrogateDiagTailX0RatChunk001Sub000Block168Part010

theorem surrogateDiagonalTailChunk001Sub000Block168Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block168Part010CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block168Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block168Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block168Part010CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block168Part010SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block168Part010] using hcert

def TailChunk001Sub000Block168Part011SupportExplicit : Finset ℕ :=
  ([23421] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block168Part011 : ℚ :=
  (9827 : ℚ) / 8295959347200

def SurrogateDiagonalTailChunk001Sub000Block168Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23421
    = surrogateDiagTailX0RatChunk001Sub000Block168Part011

theorem surrogateDiagonalTailChunk001Sub000Block168Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block168Part011CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block168Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block168Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block168Part011CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block168Part011SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block168Part011] using hcert

def TailChunk001Sub000Block168Part012SupportExplicit : Finset ℕ :=
  ([23423] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block168Part012 : ℚ :=
  (48428349275 : ℚ) / 231952107113854212096

def SurrogateDiagonalTailChunk001Sub000Block168Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23423
    = surrogateDiagTailX0RatChunk001Sub000Block168Part012

theorem surrogateDiagonalTailChunk001Sub000Block168Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block168Part012CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block168Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block168Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block168Part012CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block168Part012SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block168Part012] using hcert

def TailChunk001Sub000Block168Part013SupportExplicit : Finset ℕ :=
  ([23426] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block168Part013 : ℚ :=
  (2221869411875 : ℚ) / 8281783889093984256

def SurrogateDiagonalTailChunk001Sub000Block168Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23426
    = surrogateDiagTailX0RatChunk001Sub000Block168Part013

theorem surrogateDiagonalTailChunk001Sub000Block168Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block168Part013CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block168Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block168Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block168Part013CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block168Part013SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block168Part013] using hcert

def TailChunk001Sub000Block168Part014SupportExplicit : Finset ℕ :=
  ([23429] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block168Part014 : ℚ :=
  (701607167125 : ℚ) / 406195966827381161088

def SurrogateDiagonalTailChunk001Sub000Block168Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23429
    = surrogateDiagTailX0RatChunk001Sub000Block168Part014

theorem surrogateDiagonalTailChunk001Sub000Block168Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block168Part014CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block168Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block168Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block168Part014CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block168Part014SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block168Part014] using hcert

def TailChunk001Sub000Block168Part015SupportExplicit : Finset ℕ :=
  ([23430] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block168Part015 : ℚ :=
  (31773024579 : ℚ) / 32788209664000000

def SurrogateDiagonalTailChunk001Sub000Block168Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23430
    = surrogateDiagTailX0RatChunk001Sub000Block168Part015

theorem surrogateDiagonalTailChunk001Sub000Block168Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block168Part015CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block168Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block168Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block168Part015CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block168Part015SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block168Part015] using hcert

def TailChunk001Sub000Block168Part016SupportExplicit : Finset ℕ :=
  ([23431] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block168Part016 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block168Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23431
    = surrogateDiagTailX0RatChunk001Sub000Block168Part016

theorem surrogateDiagonalTailChunk001Sub000Block168Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block168Part016CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block168Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block168Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block168Part016CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block168Part016SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block168Part016] using hcert

def TailChunk001Sub000Block168Part017SupportExplicit : Finset ℕ :=
  ([23433] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block168Part017 : ℚ :=
  (2307556075 : ℚ) / 2827867462596919296

def SurrogateDiagonalTailChunk001Sub000Block168Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23433
    = surrogateDiagTailX0RatChunk001Sub000Block168Part017

theorem surrogateDiagonalTailChunk001Sub000Block168Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block168Part017CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block168Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block168Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block168Part017CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block168Part017SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block168Part017] using hcert

def TailChunk001Sub000Block168Part018SupportExplicit : Finset ℕ :=
  ([23434] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block168Part018 : ℚ :=
  (2145126390625 : ℚ) / 11778346314972309792

def SurrogateDiagonalTailChunk001Sub000Block168Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23434
    = surrogateDiagTailX0RatChunk001Sub000Block168Part018

theorem surrogateDiagonalTailChunk001Sub000Block168Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block168Part018CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block168Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block168Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block168Part018CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block168Part018SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block168Part018] using hcert

def TailChunk001Sub000Block168Part019SupportExplicit : Finset ℕ :=
  ([23435] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block168Part019 : ℚ :=
  (18138940625 : ℚ) / 3345599794952798208

def SurrogateDiagonalTailChunk001Sub000Block168Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23435
    = surrogateDiagTailX0RatChunk001Sub000Block168Part019

theorem surrogateDiagonalTailChunk001Sub000Block168Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block168Part019CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block168Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block168Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block168Part019CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block168Part019SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block168Part019] using hcert

def TailChunk001Sub000Block168Part020SupportExplicit : Finset ℕ :=
  ([23437] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block168Part020 : ℚ :=
  (110152371675 : ℚ) / 209694693035184750976

def SurrogateDiagonalTailChunk001Sub000Block168Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23437
    = surrogateDiagTailX0RatChunk001Sub000Block168Part020

theorem surrogateDiagonalTailChunk001Sub000Block168Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block168Part020CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block168Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block168Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block168Part020CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block168Part020SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block168Part020] using hcert

def TailChunk001Sub000Block168Part021SupportExplicit : Finset ℕ :=
  ([23438] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block168Part021 : ℚ :=
  (2145858765625 : ℚ) / 11786390946329510322

def SurrogateDiagonalTailChunk001Sub000Block168Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23438
    = surrogateDiagTailX0RatChunk001Sub000Block168Part021

theorem surrogateDiagonalTailChunk001Sub000Block168Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block168Part021CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block168Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block168Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block168Part021CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block168Part021SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block168Part021] using hcert

def TailChunk001Sub000Block168Part022SupportExplicit : Finset ℕ :=
  ([23439] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block168Part022 : ℚ :=
  (31510013 : ℚ) / 933306624000000

def SurrogateDiagonalTailChunk001Sub000Block168Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23439
    = surrogateDiagTailX0RatChunk001Sub000Block168Part022

theorem surrogateDiagonalTailChunk001Sub000Block168Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block168Part022CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block168Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block168Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block168Part022CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block168Part022SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block168Part022] using hcert

def TailChunk001Sub000Block168Part023SupportExplicit : Finset ℕ :=
  ([23441] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block168Part023 : ℚ :=
  (237552839 : ℚ) / 214453940649187500

def SurrogateDiagonalTailChunk001Sub000Block168Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23441
    = surrogateDiagTailX0RatChunk001Sub000Block168Part023

theorem surrogateDiagonalTailChunk001Sub000Block168Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block168Part023CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block168Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block168Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block168Part023CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block168Part023SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block168Part023] using hcert

def TailChunk001Sub000Block168Part024SupportExplicit : Finset ℕ :=
  ([23442] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block168Part024 : ℚ :=
  (298071808225 : ℚ) / 582043997349605448

def SurrogateDiagonalTailChunk001Sub000Block168Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23442
    = surrogateDiagTailX0RatChunk001Sub000Block168Part024

theorem surrogateDiagonalTailChunk001Sub000Block168Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block168Part024CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block168Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block168Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block168Part024CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block168Part024SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block168Part024] using hcert

def surrogateDiagonalTailChunk001Sub000Block168HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block168Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block168Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block168Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block168Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block168Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block168Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block168Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block168Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block168Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block168Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block168Head : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block168Part000
    + surrogateDiagTailX0RatChunk001Sub000Block168Part001
    + surrogateDiagTailX0RatChunk001Sub000Block168Part002
    + surrogateDiagTailX0RatChunk001Sub000Block168Part003
    + surrogateDiagTailX0RatChunk001Sub000Block168Part004
    + surrogateDiagTailX0RatChunk001Sub000Block168Part005
    + surrogateDiagTailX0RatChunk001Sub000Block168Part006
    + surrogateDiagTailX0RatChunk001Sub000Block168Part007
    + surrogateDiagTailX0RatChunk001Sub000Block168Part008
    + surrogateDiagTailX0RatChunk001Sub000Block168Part009

def surrogateDiagonalTailChunk001Sub000Block168MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block168Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block168Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block168Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block168Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block168Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block168Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block168Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block168Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block168Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block168Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block168Mid : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block168Part010
    + surrogateDiagTailX0RatChunk001Sub000Block168Part011
    + surrogateDiagTailX0RatChunk001Sub000Block168Part012
    + surrogateDiagTailX0RatChunk001Sub000Block168Part013
    + surrogateDiagTailX0RatChunk001Sub000Block168Part014
    + surrogateDiagTailX0RatChunk001Sub000Block168Part015
    + surrogateDiagTailX0RatChunk001Sub000Block168Part016
    + surrogateDiagTailX0RatChunk001Sub000Block168Part017
    + surrogateDiagTailX0RatChunk001Sub000Block168Part018
    + surrogateDiagTailX0RatChunk001Sub000Block168Part019

def surrogateDiagonalTailChunk001Sub000Block168TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block168Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block168Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block168Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block168Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block168Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block168Tail : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block168Part020
    + surrogateDiagTailX0RatChunk001Sub000Block168Part021
    + surrogateDiagTailX0RatChunk001Sub000Block168Part022
    + surrogateDiagTailX0RatChunk001Sub000Block168Part023
    + surrogateDiagTailX0RatChunk001Sub000Block168Part024

def surrogateDiagonalTailChunk001Sub000Block168Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk001Sub000Block168HeadSum X0
    + surrogateDiagonalTailChunk001Sub000Block168MidSum X0
    + surrogateDiagonalTailChunk001Sub000Block168TailSum X0

def surrogateDiagTailX0RatChunk001Sub000Block168 : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block168Part000
    + surrogateDiagTailX0RatChunk001Sub000Block168Part001
    + surrogateDiagTailX0RatChunk001Sub000Block168Part002
    + surrogateDiagTailX0RatChunk001Sub000Block168Part003
    + surrogateDiagTailX0RatChunk001Sub000Block168Part004
    + surrogateDiagTailX0RatChunk001Sub000Block168Part005
    + surrogateDiagTailX0RatChunk001Sub000Block168Part006
    + surrogateDiagTailX0RatChunk001Sub000Block168Part007
    + surrogateDiagTailX0RatChunk001Sub000Block168Part008
    + surrogateDiagTailX0RatChunk001Sub000Block168Part009
    + surrogateDiagTailX0RatChunk001Sub000Block168Part010
    + surrogateDiagTailX0RatChunk001Sub000Block168Part011
    + surrogateDiagTailX0RatChunk001Sub000Block168Part012
    + surrogateDiagTailX0RatChunk001Sub000Block168Part013
    + surrogateDiagTailX0RatChunk001Sub000Block168Part014
    + surrogateDiagTailX0RatChunk001Sub000Block168Part015
    + surrogateDiagTailX0RatChunk001Sub000Block168Part016
    + surrogateDiagTailX0RatChunk001Sub000Block168Part017
    + surrogateDiagTailX0RatChunk001Sub000Block168Part018
    + surrogateDiagTailX0RatChunk001Sub000Block168Part019
    + surrogateDiagTailX0RatChunk001Sub000Block168Part020
    + surrogateDiagTailX0RatChunk001Sub000Block168Part021
    + surrogateDiagTailX0RatChunk001Sub000Block168Part022
    + surrogateDiagTailX0RatChunk001Sub000Block168Part023
    + surrogateDiagTailX0RatChunk001Sub000Block168Part024

theorem surrogateDiagTailX0RatChunk001Sub000Block168_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk001Sub000Block168Head + surrogateDiagTailX0RatChunk001Sub000Block168Mid + surrogateDiagTailX0RatChunk001Sub000Block168Tail =
      surrogateDiagTailX0RatChunk001Sub000Block168 := by
  unfold surrogateDiagTailX0RatChunk001Sub000Block168Head surrogateDiagTailX0RatChunk001Sub000Block168Mid surrogateDiagTailX0RatChunk001Sub000Block168Tail surrogateDiagTailX0RatChunk001Sub000Block168
  ring

def SurrogateDiagonalTailChunk001Sub000Block168HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block168HeadSum X0 = surrogateDiagTailX0RatChunk001Sub000Block168Head

def SurrogateDiagonalTailChunk001Sub000Block168MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block168MidSum X0 = surrogateDiagTailX0RatChunk001Sub000Block168Mid

def SurrogateDiagonalTailChunk001Sub000Block168TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block168TailSum X0 = surrogateDiagTailX0RatChunk001Sub000Block168Tail

theorem surrogateDiagonalTailChunk001Sub000Block168_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk001Sub000Block168HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk001Sub000Block168MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk001Sub000Block168TailCertificateAt X0) :
    surrogateDiagonalTailChunk001Sub000Block168Sum X0 = surrogateDiagTailX0RatChunk001Sub000Block168 := by
  unfold SurrogateDiagonalTailChunk001Sub000Block168HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk001Sub000Block168MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk001Sub000Block168TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk001Sub000Block168Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk001Sub000Block168_eq_head_add_mid_add_tail

/-- Block 169 covers tail-support indices [14225,14250) and q from 23443 to 23487. -/

def TailChunk001Sub000Block169Part000SupportExplicit : Finset ℕ :=
  ([23443] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block169Part000 : ℚ :=
  (1038395273275 : ℚ) / 313426762317711802368

def SurrogateDiagonalTailChunk001Sub000Block169Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23443
    = surrogateDiagTailX0RatChunk001Sub000Block169Part000

theorem surrogateDiagonalTailChunk001Sub000Block169Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block169Part000CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block169Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block169Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block169Part000CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block169Part000SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block169Part000] using hcert

def TailChunk001Sub000Block169Part001SupportExplicit : Finset ℕ :=
  ([23446] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block169Part001 : ℚ :=
  (1122370262275 : ℚ) / 5399352579134029824

def SurrogateDiagonalTailChunk001Sub000Block169Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23446
    = surrogateDiagTailX0RatChunk001Sub000Block169Part001

theorem surrogateDiagonalTailChunk001Sub000Block169Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block169Part001CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block169Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block169Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block169Part001CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block169Part001SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block169Part001] using hcert

def TailChunk001Sub000Block169Part002SupportExplicit : Finset ℕ :=
  ([23447] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block169Part002 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block169Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23447
    = surrogateDiagTailX0RatChunk001Sub000Block169Part002

theorem surrogateDiagonalTailChunk001Sub000Block169Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block169Part002CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block169Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block169Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block169Part002CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block169Part002SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block169Part002] using hcert

def TailChunk001Sub000Block169Part003SupportExplicit : Finset ℕ :=
  ([23449] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block169Part003 : ℚ :=
  (98052297 : ℚ) / 735318786227708800

def SurrogateDiagonalTailChunk001Sub000Block169Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23449
    = surrogateDiagTailX0RatChunk001Sub000Block169Part003

theorem surrogateDiagonalTailChunk001Sub000Block169Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block169Part003CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block169Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block169Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block169Part003CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block169Part003SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block169Part003] using hcert

def TailChunk001Sub000Block169Part004SupportExplicit : Finset ℕ :=
  ([23451] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block169Part004 : ℚ :=
  (954685248025 : ℚ) / 37327169002019561472

def SurrogateDiagonalTailChunk001Sub000Block169Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23451
    = surrogateDiagTailX0RatChunk001Sub000Block169Part004

theorem surrogateDiagonalTailChunk001Sub000Block169Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block169Part004CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block169Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block169Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block169Part004CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block169Part004SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block169Part004] using hcert

def TailChunk001Sub000Block169Part005SupportExplicit : Finset ℕ :=
  ([23453] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block169Part005 : ℚ :=
  (28175215375 : ℚ) / 114768923014907068608

def SurrogateDiagonalTailChunk001Sub000Block169Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23453
    = surrogateDiagTailX0RatChunk001Sub000Block169Part005

theorem surrogateDiagonalTailChunk001Sub000Block169Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block169Part005CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block169Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block169Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block169Part005CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block169Part005SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block169Part005] using hcert

def TailChunk001Sub000Block169Part006SupportExplicit : Finset ℕ :=
  ([23455] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block169Part006 : ℚ :=
  (3669351603 : ℚ) / 825898975390791680

def SurrogateDiagonalTailChunk001Sub000Block169Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23455
    = surrogateDiagTailX0RatChunk001Sub000Block169Part006

theorem surrogateDiagonalTailChunk001Sub000Block169Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block169Part006CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block169Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block169Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block169Part006CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block169Part006SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block169Part006] using hcert

def TailChunk001Sub000Block169Part007SupportExplicit : Finset ℕ :=
  ([23457] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block169Part007 : ℚ :=
  (3351189466525 : ℚ) / 80428250422600040448

def SurrogateDiagonalTailChunk001Sub000Block169Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23457
    = surrogateDiagTailX0RatChunk001Sub000Block169Part007

theorem surrogateDiagonalTailChunk001Sub000Block169Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block169Part007CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block169Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block169Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block169Part007CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block169Part007SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block169Part007] using hcert

def TailChunk001Sub000Block169Part008SupportExplicit : Finset ℕ :=
  ([23458] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block169Part008 : ℚ :=
  (33720954175 : ℚ) / 172337154856943616

def SurrogateDiagonalTailChunk001Sub000Block169Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23458
    = surrogateDiagTailX0RatChunk001Sub000Block169Part008

theorem surrogateDiagonalTailChunk001Sub000Block169Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block169Part008CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block169Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block169Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block169Part008CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block169Part008SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block169Part008] using hcert

def TailChunk001Sub000Block169Part009SupportExplicit : Finset ℕ :=
  ([23459] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block169Part009 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block169Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23459
    = surrogateDiagTailX0RatChunk001Sub000Block169Part009

theorem surrogateDiagonalTailChunk001Sub000Block169Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block169Part009CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block169Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block169Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block169Part009CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block169Part009SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block169Part009] using hcert

def TailChunk001Sub000Block169Part010SupportExplicit : Finset ℕ :=
  ([23461] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block169Part010 : ℚ :=
  (253311207175 : ℚ) / 655095215175919730688

def SurrogateDiagonalTailChunk001Sub000Block169Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23461
    = surrogateDiagTailX0RatChunk001Sub000Block169Part010

theorem surrogateDiagonalTailChunk001Sub000Block169Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block169Part010CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block169Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block169Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block169Part010CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block169Part010SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block169Part010] using hcert

def TailChunk001Sub000Block169Part011SupportExplicit : Finset ℕ :=
  ([23462] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block169Part011 : ℚ :=
  (3440409025 : ℚ) / 18935592491636082

def SurrogateDiagonalTailChunk001Sub000Block169Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23462
    = surrogateDiagTailX0RatChunk001Sub000Block169Part011

theorem surrogateDiagonalTailChunk001Sub000Block169Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block169Part011CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block169Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block169Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block169Part011CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block169Part011SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block169Part011] using hcert

def TailChunk001Sub000Block169Part012SupportExplicit : Finset ℕ :=
  ([23466] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block169Part012 : ℚ :=
  (47789204947 : ℚ) / 93509098724128800

def SurrogateDiagonalTailChunk001Sub000Block169Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23466
    = surrogateDiagTailX0RatChunk001Sub000Block169Part012

theorem surrogateDiagonalTailChunk001Sub000Block169Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block169Part012CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block169Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block169Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block169Part012CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block169Part012SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block169Part012] using hcert

def TailChunk001Sub000Block169Part013SupportExplicit : Finset ℕ :=
  ([23467] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block169Part013 : ℚ :=
  (82256357 : ℚ) / 210033469270195200

def SurrogateDiagonalTailChunk001Sub000Block169Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23467
    = surrogateDiagTailX0RatChunk001Sub000Block169Part013

theorem surrogateDiagonalTailChunk001Sub000Block169Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block169Part013CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block169Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block169Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block169Part013CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block169Part013SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block169Part013] using hcert

def TailChunk001Sub000Block169Part014SupportExplicit : Finset ℕ :=
  ([23469] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block169Part014 : ℚ :=
  (1912302620975 : ℚ) / 74883837528988367424

def SurrogateDiagonalTailChunk001Sub000Block169Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23469
    = surrogateDiagTailX0RatChunk001Sub000Block169Part014

theorem surrogateDiagonalTailChunk001Sub000Block169Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block169Part014CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block169Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block169Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block169Part014CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block169Part014SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block169Part014] using hcert

def TailChunk001Sub000Block169Part015SupportExplicit : Finset ℕ :=
  ([23470] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block169Part015 : ℚ :=
  (5849498985025 : ℚ) / 19390046711435347968

def SurrogateDiagonalTailChunk001Sub000Block169Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23470
    = surrogateDiagTailX0RatChunk001Sub000Block169Part015

theorem surrogateDiagonalTailChunk001Sub000Block169Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block169Part015CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block169Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block169Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block169Part015CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block169Part015SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block169Part015] using hcert

def TailChunk001Sub000Block169Part016SupportExplicit : Finset ℕ :=
  ([23473] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block169Part016 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block169Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23473
    = surrogateDiagTailX0RatChunk001Sub000Block169Part016

theorem surrogateDiagonalTailChunk001Sub000Block169Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block169Part016CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block169Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block169Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block169Part016CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block169Part016SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block169Part016] using hcert

def TailChunk001Sub000Block169Part017SupportExplicit : Finset ℕ :=
  ([23477] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block169Part017 : ℚ :=
  (25134109 : ℚ) / 41272487342899200

def SurrogateDiagonalTailChunk001Sub000Block169Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23477
    = surrogateDiagTailX0RatChunk001Sub000Block169Part017

theorem surrogateDiagonalTailChunk001Sub000Block169Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block169Part017CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block169Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block169Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block169Part017CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block169Part017SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block169Part017] using hcert

def TailChunk001Sub000Block169Part018SupportExplicit : Finset ℕ :=
  ([23478] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block169Part018 : ℚ :=
  (3243195159025 : ℚ) / 3345599794952798208

def SurrogateDiagonalTailChunk001Sub000Block169Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23478
    = surrogateDiagTailX0RatChunk001Sub000Block169Part018

theorem surrogateDiagonalTailChunk001Sub000Block169Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block169Part018CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block169Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block169Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block169Part018CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block169Part018SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block169Part018] using hcert

def TailChunk001Sub000Block169Part019SupportExplicit : Finset ℕ :=
  ([23479] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block169Part019 : ℚ :=
  (150402839125 : ℚ) / 697797341980167456768

def SurrogateDiagonalTailChunk001Sub000Block169Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23479
    = surrogateDiagTailX0RatChunk001Sub000Block169Part019

theorem surrogateDiagonalTailChunk001Sub000Block169Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block169Part019CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block169Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block169Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block169Part019CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block169Part019SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block169Part019] using hcert

def TailChunk001Sub000Block169Part020SupportExplicit : Finset ℕ :=
  ([23482] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block169Part020 : ℚ :=
  (4160253881975 : ℚ) / 21745510041923832384

def SurrogateDiagonalTailChunk001Sub000Block169Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23482
    = surrogateDiagTailX0RatChunk001Sub000Block169Part020

theorem surrogateDiagonalTailChunk001Sub000Block169Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block169Part020CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block169Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block169Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block169Part020CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block169Part020SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block169Part020] using hcert

def TailChunk001Sub000Block169Part021SupportExplicit : Finset ℕ :=
  ([23483] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block169Part021 : ℚ :=
  (13269193891 : ℚ) / 25361694131857459200

def SurrogateDiagonalTailChunk001Sub000Block169Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23483
    = surrogateDiagTailX0RatChunk001Sub000Block169Part021

theorem surrogateDiagonalTailChunk001Sub000Block169Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block169Part021CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block169Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block169Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block169Part021CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block169Part021SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block169Part021] using hcert

def TailChunk001Sub000Block169Part022SupportExplicit : Finset ℕ :=
  ([23485] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block169Part022 : ℚ :=
  (69909862663 : ℚ) / 4300676923392000000

def SurrogateDiagonalTailChunk001Sub000Block169Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23485
    = surrogateDiagTailX0RatChunk001Sub000Block169Part022

theorem surrogateDiagonalTailChunk001Sub000Block169Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block169Part022CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block169Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block169Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block169Part022CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block169Part022SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block169Part022] using hcert

def TailChunk001Sub000Block169Part023SupportExplicit : Finset ℕ :=
  ([23486] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block169Part023 : ℚ :=
  (2154657015625 : ℚ) / 11883248298293583762

def SurrogateDiagonalTailChunk001Sub000Block169Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23486
    = surrogateDiagTailX0RatChunk001Sub000Block169Part023

theorem surrogateDiagonalTailChunk001Sub000Block169Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block169Part023CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block169Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block169Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block169Part023CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block169Part023SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block169Part023] using hcert

def TailChunk001Sub000Block169Part024SupportExplicit : Finset ℕ :=
  ([23487] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block169Part024 : ℚ :=
  (478809248975 : ℚ) / 18778466446686157056

def SurrogateDiagonalTailChunk001Sub000Block169Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23487
    = surrogateDiagTailX0RatChunk001Sub000Block169Part024

theorem surrogateDiagonalTailChunk001Sub000Block169Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block169Part024CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block169Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block169Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block169Part024CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block169Part024SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block169Part024] using hcert

def surrogateDiagonalTailChunk001Sub000Block169HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block169Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block169Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block169Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block169Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block169Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block169Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block169Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block169Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block169Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block169Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block169Head : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block169Part000
    + surrogateDiagTailX0RatChunk001Sub000Block169Part001
    + surrogateDiagTailX0RatChunk001Sub000Block169Part002
    + surrogateDiagTailX0RatChunk001Sub000Block169Part003
    + surrogateDiagTailX0RatChunk001Sub000Block169Part004
    + surrogateDiagTailX0RatChunk001Sub000Block169Part005
    + surrogateDiagTailX0RatChunk001Sub000Block169Part006
    + surrogateDiagTailX0RatChunk001Sub000Block169Part007
    + surrogateDiagTailX0RatChunk001Sub000Block169Part008
    + surrogateDiagTailX0RatChunk001Sub000Block169Part009

def surrogateDiagonalTailChunk001Sub000Block169MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block169Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block169Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block169Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block169Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block169Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block169Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block169Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block169Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block169Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block169Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block169Mid : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block169Part010
    + surrogateDiagTailX0RatChunk001Sub000Block169Part011
    + surrogateDiagTailX0RatChunk001Sub000Block169Part012
    + surrogateDiagTailX0RatChunk001Sub000Block169Part013
    + surrogateDiagTailX0RatChunk001Sub000Block169Part014
    + surrogateDiagTailX0RatChunk001Sub000Block169Part015
    + surrogateDiagTailX0RatChunk001Sub000Block169Part016
    + surrogateDiagTailX0RatChunk001Sub000Block169Part017
    + surrogateDiagTailX0RatChunk001Sub000Block169Part018
    + surrogateDiagTailX0RatChunk001Sub000Block169Part019

def surrogateDiagonalTailChunk001Sub000Block169TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block169Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block169Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block169Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block169Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block169Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block169Tail : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block169Part020
    + surrogateDiagTailX0RatChunk001Sub000Block169Part021
    + surrogateDiagTailX0RatChunk001Sub000Block169Part022
    + surrogateDiagTailX0RatChunk001Sub000Block169Part023
    + surrogateDiagTailX0RatChunk001Sub000Block169Part024

def surrogateDiagonalTailChunk001Sub000Block169Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk001Sub000Block169HeadSum X0
    + surrogateDiagonalTailChunk001Sub000Block169MidSum X0
    + surrogateDiagonalTailChunk001Sub000Block169TailSum X0

def surrogateDiagTailX0RatChunk001Sub000Block169 : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block169Part000
    + surrogateDiagTailX0RatChunk001Sub000Block169Part001
    + surrogateDiagTailX0RatChunk001Sub000Block169Part002
    + surrogateDiagTailX0RatChunk001Sub000Block169Part003
    + surrogateDiagTailX0RatChunk001Sub000Block169Part004
    + surrogateDiagTailX0RatChunk001Sub000Block169Part005
    + surrogateDiagTailX0RatChunk001Sub000Block169Part006
    + surrogateDiagTailX0RatChunk001Sub000Block169Part007
    + surrogateDiagTailX0RatChunk001Sub000Block169Part008
    + surrogateDiagTailX0RatChunk001Sub000Block169Part009
    + surrogateDiagTailX0RatChunk001Sub000Block169Part010
    + surrogateDiagTailX0RatChunk001Sub000Block169Part011
    + surrogateDiagTailX0RatChunk001Sub000Block169Part012
    + surrogateDiagTailX0RatChunk001Sub000Block169Part013
    + surrogateDiagTailX0RatChunk001Sub000Block169Part014
    + surrogateDiagTailX0RatChunk001Sub000Block169Part015
    + surrogateDiagTailX0RatChunk001Sub000Block169Part016
    + surrogateDiagTailX0RatChunk001Sub000Block169Part017
    + surrogateDiagTailX0RatChunk001Sub000Block169Part018
    + surrogateDiagTailX0RatChunk001Sub000Block169Part019
    + surrogateDiagTailX0RatChunk001Sub000Block169Part020
    + surrogateDiagTailX0RatChunk001Sub000Block169Part021
    + surrogateDiagTailX0RatChunk001Sub000Block169Part022
    + surrogateDiagTailX0RatChunk001Sub000Block169Part023
    + surrogateDiagTailX0RatChunk001Sub000Block169Part024

theorem surrogateDiagTailX0RatChunk001Sub000Block169_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk001Sub000Block169Head + surrogateDiagTailX0RatChunk001Sub000Block169Mid + surrogateDiagTailX0RatChunk001Sub000Block169Tail =
      surrogateDiagTailX0RatChunk001Sub000Block169 := by
  unfold surrogateDiagTailX0RatChunk001Sub000Block169Head surrogateDiagTailX0RatChunk001Sub000Block169Mid surrogateDiagTailX0RatChunk001Sub000Block169Tail surrogateDiagTailX0RatChunk001Sub000Block169
  ring

def SurrogateDiagonalTailChunk001Sub000Block169HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block169HeadSum X0 = surrogateDiagTailX0RatChunk001Sub000Block169Head

def SurrogateDiagonalTailChunk001Sub000Block169MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block169MidSum X0 = surrogateDiagTailX0RatChunk001Sub000Block169Mid

def SurrogateDiagonalTailChunk001Sub000Block169TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block169TailSum X0 = surrogateDiagTailX0RatChunk001Sub000Block169Tail

theorem surrogateDiagonalTailChunk001Sub000Block169_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk001Sub000Block169HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk001Sub000Block169MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk001Sub000Block169TailCertificateAt X0) :
    surrogateDiagonalTailChunk001Sub000Block169Sum X0 = surrogateDiagTailX0RatChunk001Sub000Block169 := by
  unfold SurrogateDiagonalTailChunk001Sub000Block169HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk001Sub000Block169MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk001Sub000Block169TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk001Sub000Block169Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk001Sub000Block169_eq_head_add_mid_add_tail

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

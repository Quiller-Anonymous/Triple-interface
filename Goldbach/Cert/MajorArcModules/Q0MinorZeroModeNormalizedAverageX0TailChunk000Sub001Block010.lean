import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0TailPilot25

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

open scoped BigOperators

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

/- Generated direct-term certificate blocks for tail chunk 000, subchunk 001, blocks [10,11). -/

/-- Block 010 covers tail-support indices [5250,5275) and q from 8683 to 8719. -/

def TailChunk000Sub001Block010Part000SupportExplicit : Finset ℕ :=
  ([8683] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block010Part000 : ℚ :=
  (7546817375 : ℚ) / 19703971312501248

def SurrogateDiagonalTailChunk000Sub001Block010Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8683
    = surrogateDiagTailX0RatChunk000Sub001Block010Part000

theorem surrogateDiagonalTailChunk000Sub001Block010Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block010Part000CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block010Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block010Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block010Part000CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block010Part000SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block010Part000] using hcert

def TailChunk000Sub001Block010Part001SupportExplicit : Finset ℕ :=
  ([8686] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block010Part001 : ℚ :=
  (9171509129 : ℚ) / 6224636678400000

def SurrogateDiagonalTailChunk000Sub001Block010Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8686
    = surrogateDiagTailX0RatChunk000Sub001Block010Part001

theorem surrogateDiagonalTailChunk000Sub001Block010Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block010Part001CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block010Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block010Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block010Part001CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block010Part001SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block010Part001] using hcert

def TailChunk000Sub001Block010Part002SupportExplicit : Finset ℕ :=
  ([8687] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block010Part002 : ℚ :=
  (1693735111025 : ℚ) / 2853722773870608384

def SurrogateDiagonalTailChunk000Sub001Block010Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8687
    = surrogateDiagTailX0RatChunk000Sub001Block010Part002

theorem surrogateDiagonalTailChunk000Sub001Block010Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block010Part002CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block010Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block010Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block010Part002CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block010Part002SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block010Part002] using hcert

def TailChunk000Sub001Block010Part003SupportExplicit : Finset ℕ :=
  ([8689] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block010Part003 : ℚ :=
  (1179667515625 : ℚ) / 3561607986690465792

def SurrogateDiagonalTailChunk000Sub001Block010Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8689
    = surrogateDiagTailX0RatChunk000Sub001Block010Part003

theorem surrogateDiagonalTailChunk000Sub001Block010Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block010Part003CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block010Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block010Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block010Part003CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block010Part003SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block010Part003] using hcert

def TailChunk000Sub001Block010Part004SupportExplicit : Finset ℕ :=
  ([8690] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block010Part004 : ℚ :=
  (4005233591 : ℚ) / 1053083278540800

def SurrogateDiagonalTailChunk000Sub001Block010Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8690
    = surrogateDiagTailX0RatChunk000Sub001Block010Part004

theorem surrogateDiagonalTailChunk000Sub001Block010Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block010Part004CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block010Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block010Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block010Part004CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block010Part004SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block010Part004] using hcert

def TailChunk000Sub001Block010Part005SupportExplicit : Finset ℕ :=
  ([8691] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block010Part005 : ℚ :=
  (1310962102925 : ℚ) / 1407055007087591424

def SurrogateDiagonalTailChunk000Sub001Block010Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8691
    = surrogateDiagTailX0RatChunk000Sub001Block010Part005

theorem surrogateDiagonalTailChunk000Sub001Block010Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block010Part005CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block010Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block010Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block010Part005CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block010Part005SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block010Part005] using hcert

def TailChunk000Sub001Block010Part006SupportExplicit : Finset ℕ :=
  ([8693] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block010Part006 : ℚ :=
  (1180753890625 : ℚ) / 3568171648597953312

def SurrogateDiagonalTailChunk000Sub001Block010Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8693
    = surrogateDiagTailX0RatChunk000Sub001Block010Part006

theorem surrogateDiagonalTailChunk000Sub001Block010Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block010Part006CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block010Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block010Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block010Part006CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block010Part006SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block010Part006] using hcert

def TailChunk000Sub001Block010Part007SupportExplicit : Finset ℕ :=
  ([8695] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block010Part007 : ℚ :=
  (1591189759625 : ℚ) / 2407011461837881344

def SurrogateDiagonalTailChunk000Sub001Block010Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8695
    = surrogateDiagTailX0RatChunk000Sub001Block010Part007

theorem surrogateDiagonalTailChunk000Sub001Block010Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block010Part007CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block010Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block010Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block010Part007CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block010Part007SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block010Part007] using hcert

def TailChunk000Sub001Block010Part008SupportExplicit : Finset ℕ :=
  ([8697] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block010Part008 : ℚ :=
  (86763918175 : ℚ) / 74631120031678464

def SurrogateDiagonalTailChunk000Sub001Block010Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8697
    = surrogateDiagTailX0RatChunk000Sub001Block010Part008

theorem surrogateDiagonalTailChunk000Sub001Block010Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block010Part008CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block010Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block010Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block010Part008CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block010Part008SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block010Part008] using hcert

def TailChunk000Sub001Block010Part009SupportExplicit : Finset ℕ :=
  ([8698] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block010Part009 : ℚ :=
  (2363752279975 : ℚ) / 893686094605665408

def SurrogateDiagonalTailChunk000Sub001Block010Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8698
    = surrogateDiagTailX0RatChunk000Sub001Block010Part009

theorem surrogateDiagonalTailChunk000Sub001Block010Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block010Part009CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block010Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block010Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block010Part009CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block010Part009SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block010Part009] using hcert

def TailChunk000Sub001Block010Part010SupportExplicit : Finset ℕ :=
  ([8699] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block010Part010 : ℚ :=
  (1182384390625 : ℚ) / 3578034146412545202

def SurrogateDiagonalTailChunk000Sub001Block010Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8699
    = surrogateDiagTailX0RatChunk000Sub001Block010Part010

theorem surrogateDiagonalTailChunk000Sub001Block010Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block010Part010CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block010Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block010Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block010Part010CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block010Part010SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block010Part010] using hcert

def TailChunk000Sub001Block010Part011SupportExplicit : Finset ℕ :=
  ([8701] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block010Part011 : ℚ :=
  (3606550667 : ℚ) / 5665802629939200

def SurrogateDiagonalTailChunk000Sub001Block010Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8701
    = surrogateDiagTailX0RatChunk000Sub001Block010Part011

theorem surrogateDiagonalTailChunk000Sub001Block010Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block010Part011CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block010Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block010Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block010Part011CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block010Part011SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block010Part011] using hcert

def TailChunk000Sub001Block010Part012SupportExplicit : Finset ℕ :=
  ([8702] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block010Part012 : ℚ :=
  (2176179129625 : ℚ) / 709342967250044928

def SurrogateDiagonalTailChunk000Sub001Block010Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8702
    = surrogateDiagTailX0RatChunk000Sub001Block010Part012

theorem surrogateDiagonalTailChunk000Sub001Block010Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block010Part012CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block010Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block010Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block010Part012CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block010Part012SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block010Part012] using hcert

def TailChunk000Sub001Block010Part013SupportExplicit : Finset ℕ :=
  ([8705] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block010Part013 : ℚ :=
  (136313205157 : ℚ) / 234705792828211200

def SurrogateDiagonalTailChunk000Sub001Block010Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8705
    = surrogateDiagTailX0RatChunk000Sub001Block010Part013

theorem surrogateDiagonalTailChunk000Sub001Block010Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block010Part013CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block010Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block010Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block010Part013CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block010Part013SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block010Part013] using hcert

def TailChunk000Sub001Block010Part014SupportExplicit : Finset ℕ :=
  ([8706] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block010Part014 : ℚ :=
  (26296893347 : ℚ) / 3537112281000000

def SurrogateDiagonalTailChunk000Sub001Block010Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8706
    = surrogateDiagTailX0RatChunk000Sub001Block010Part014

theorem surrogateDiagonalTailChunk000Sub001Block010Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block010Part014CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block010Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block010Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block010Part014CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block010Part014SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block010Part014] using hcert

def TailChunk000Sub001Block010Part015SupportExplicit : Finset ℕ :=
  ([8707] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block010Part015 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block010Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8707
    = surrogateDiagTailX0RatChunk000Sub001Block010Part015

theorem surrogateDiagonalTailChunk000Sub001Block010Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block010Part015CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block010Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block010Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block010Part015CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block010Part015SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block010Part015] using hcert

def TailChunk000Sub001Block010Part016SupportExplicit : Finset ℕ :=
  ([8709] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block010Part016 : ℚ :=
  (263487682475 : ℚ) / 1418751972312051264

def SurrogateDiagonalTailChunk000Sub001Block010Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8709
    = surrogateDiagTailX0RatChunk000Sub001Block010Part016

theorem surrogateDiagonalTailChunk000Sub001Block010Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block010Part016CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block010Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block010Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block010Part016CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block010Part016SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block010Part016] using hcert

def TailChunk000Sub001Block010Part017SupportExplicit : Finset ℕ :=
  ([8710] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block010Part017 : ℚ :=
  (437651137625 : ℚ) / 125932421670764544

def SurrogateDiagonalTailChunk000Sub001Block010Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8710
    = surrogateDiagTailX0RatChunk000Sub001Block010Part017

theorem surrogateDiagonalTailChunk000Sub001Block010Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block010Part017CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block010Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block010Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block010Part017CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block010Part017SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block010Part017] using hcert

def TailChunk000Sub001Block010Part018SupportExplicit : Finset ℕ :=
  ([8711] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block010Part018 : ℚ :=
  (3890344309 : ℚ) / 497970934272000000

def SurrogateDiagonalTailChunk000Sub001Block010Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8711
    = surrogateDiagTailX0RatChunk000Sub001Block010Part018

theorem surrogateDiagonalTailChunk000Sub001Block010Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block010Part018CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block010Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block010Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block010Part018CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block010Part018SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block010Part018] using hcert

def TailChunk000Sub001Block010Part019SupportExplicit : Finset ℕ :=
  ([8713] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block010Part019 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block010Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8713
    = surrogateDiagTailX0RatChunk000Sub001Block010Part019

theorem surrogateDiagonalTailChunk000Sub001Block010Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block010Part019CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block010Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block010Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block010Part019CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block010Part019SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block010Part019] using hcert

def TailChunk000Sub001Block010Part020SupportExplicit : Finset ℕ :=
  ([8714] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block010Part020 : ℚ :=
  (296616390625 : ℚ) / 225070383994343712

def SurrogateDiagonalTailChunk000Sub001Block010Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8714
    = surrogateDiagTailX0RatChunk000Sub001Block010Part020

theorem surrogateDiagonalTailChunk000Sub001Block010Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block010Part020CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block010Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block010Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block010Part020CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block010Part020SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block010Part020] using hcert

def TailChunk000Sub001Block010Part021SupportExplicit : Finset ℕ :=
  ([8715] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block010Part021 : ℚ :=
  (702079253275 : ℚ) / 600132598702276608

def SurrogateDiagonalTailChunk000Sub001Block010Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8715
    = surrogateDiagTailX0RatChunk000Sub001Block010Part021

theorem surrogateDiagonalTailChunk000Sub001Block010Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block010Part021CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block010Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block010Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block010Part021CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block010Part021SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block010Part021] using hcert

def TailChunk000Sub001Block010Part022SupportExplicit : Finset ℕ :=
  ([8717] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block010Part022 : ℚ :=
  (40892689175 : ℚ) / 3986240771313795456

def SurrogateDiagonalTailChunk000Sub001Block010Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8717
    = surrogateDiagTailX0RatChunk000Sub001Block010Part022

theorem surrogateDiagonalTailChunk000Sub001Block010Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block010Part022CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block010Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block010Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block010Part022CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block010Part022SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block010Part022] using hcert

def TailChunk000Sub001Block010Part023SupportExplicit : Finset ℕ :=
  ([8718] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block010Part023 : ℚ :=
  (26374625 : ℚ) / 5926594341888

def SurrogateDiagonalTailChunk000Sub001Block010Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8718
    = surrogateDiagTailX0RatChunk000Sub001Block010Part023

theorem surrogateDiagonalTailChunk000Sub001Block010Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block010Part023CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block010Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block010Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block010Part023CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block010Part023SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block010Part023] using hcert

def TailChunk000Sub001Block010Part024SupportExplicit : Finset ℕ :=
  ([8719] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block010Part024 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block010Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8719
    = surrogateDiagTailX0RatChunk000Sub001Block010Part024

theorem surrogateDiagonalTailChunk000Sub001Block010Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block010Part024CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block010Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block010Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block010Part024CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block010Part024SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block010Part024] using hcert

def surrogateDiagonalTailChunk000Sub001Block010HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block010Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block010Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block010Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block010Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block010Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block010Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block010Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block010Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block010Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block010Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block010Head : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block010Part000
    + surrogateDiagTailX0RatChunk000Sub001Block010Part001
    + surrogateDiagTailX0RatChunk000Sub001Block010Part002
    + surrogateDiagTailX0RatChunk000Sub001Block010Part003
    + surrogateDiagTailX0RatChunk000Sub001Block010Part004
    + surrogateDiagTailX0RatChunk000Sub001Block010Part005
    + surrogateDiagTailX0RatChunk000Sub001Block010Part006
    + surrogateDiagTailX0RatChunk000Sub001Block010Part007
    + surrogateDiagTailX0RatChunk000Sub001Block010Part008
    + surrogateDiagTailX0RatChunk000Sub001Block010Part009

def surrogateDiagonalTailChunk000Sub001Block010MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block010Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block010Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block010Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block010Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block010Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block010Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block010Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block010Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block010Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block010Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block010Mid : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block010Part010
    + surrogateDiagTailX0RatChunk000Sub001Block010Part011
    + surrogateDiagTailX0RatChunk000Sub001Block010Part012
    + surrogateDiagTailX0RatChunk000Sub001Block010Part013
    + surrogateDiagTailX0RatChunk000Sub001Block010Part014
    + surrogateDiagTailX0RatChunk000Sub001Block010Part015
    + surrogateDiagTailX0RatChunk000Sub001Block010Part016
    + surrogateDiagTailX0RatChunk000Sub001Block010Part017
    + surrogateDiagTailX0RatChunk000Sub001Block010Part018
    + surrogateDiagTailX0RatChunk000Sub001Block010Part019

def surrogateDiagonalTailChunk000Sub001Block010TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block010Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block010Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block010Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block010Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block010Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block010Tail : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block010Part020
    + surrogateDiagTailX0RatChunk000Sub001Block010Part021
    + surrogateDiagTailX0RatChunk000Sub001Block010Part022
    + surrogateDiagTailX0RatChunk000Sub001Block010Part023
    + surrogateDiagTailX0RatChunk000Sub001Block010Part024

def surrogateDiagonalTailChunk000Sub001Block010Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub001Block010HeadSum X0
    + surrogateDiagonalTailChunk000Sub001Block010MidSum X0
    + surrogateDiagonalTailChunk000Sub001Block010TailSum X0

def surrogateDiagTailX0RatChunk000Sub001Block010 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block010Part000
    + surrogateDiagTailX0RatChunk000Sub001Block010Part001
    + surrogateDiagTailX0RatChunk000Sub001Block010Part002
    + surrogateDiagTailX0RatChunk000Sub001Block010Part003
    + surrogateDiagTailX0RatChunk000Sub001Block010Part004
    + surrogateDiagTailX0RatChunk000Sub001Block010Part005
    + surrogateDiagTailX0RatChunk000Sub001Block010Part006
    + surrogateDiagTailX0RatChunk000Sub001Block010Part007
    + surrogateDiagTailX0RatChunk000Sub001Block010Part008
    + surrogateDiagTailX0RatChunk000Sub001Block010Part009
    + surrogateDiagTailX0RatChunk000Sub001Block010Part010
    + surrogateDiagTailX0RatChunk000Sub001Block010Part011
    + surrogateDiagTailX0RatChunk000Sub001Block010Part012
    + surrogateDiagTailX0RatChunk000Sub001Block010Part013
    + surrogateDiagTailX0RatChunk000Sub001Block010Part014
    + surrogateDiagTailX0RatChunk000Sub001Block010Part015
    + surrogateDiagTailX0RatChunk000Sub001Block010Part016
    + surrogateDiagTailX0RatChunk000Sub001Block010Part017
    + surrogateDiagTailX0RatChunk000Sub001Block010Part018
    + surrogateDiagTailX0RatChunk000Sub001Block010Part019
    + surrogateDiagTailX0RatChunk000Sub001Block010Part020
    + surrogateDiagTailX0RatChunk000Sub001Block010Part021
    + surrogateDiagTailX0RatChunk000Sub001Block010Part022
    + surrogateDiagTailX0RatChunk000Sub001Block010Part023
    + surrogateDiagTailX0RatChunk000Sub001Block010Part024

theorem surrogateDiagTailX0RatChunk000Sub001Block010_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk000Sub001Block010Head + surrogateDiagTailX0RatChunk000Sub001Block010Mid + surrogateDiagTailX0RatChunk000Sub001Block010Tail =
      surrogateDiagTailX0RatChunk000Sub001Block010 := by
  unfold surrogateDiagTailX0RatChunk000Sub001Block010Head surrogateDiagTailX0RatChunk000Sub001Block010Mid surrogateDiagTailX0RatChunk000Sub001Block010Tail surrogateDiagTailX0RatChunk000Sub001Block010
  ring

def SurrogateDiagonalTailChunk000Sub001Block010HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block010HeadSum X0 = surrogateDiagTailX0RatChunk000Sub001Block010Head

def SurrogateDiagonalTailChunk000Sub001Block010MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block010MidSum X0 = surrogateDiagTailX0RatChunk000Sub001Block010Mid

def SurrogateDiagonalTailChunk000Sub001Block010TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block010TailSum X0 = surrogateDiagTailX0RatChunk000Sub001Block010Tail

theorem surrogateDiagonalTailChunk000Sub001Block010_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk000Sub001Block010HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk000Sub001Block010MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk000Sub001Block010TailCertificateAt X0) :
    surrogateDiagonalTailChunk000Sub001Block010Sum X0 = surrogateDiagTailX0RatChunk000Sub001Block010 := by
  unfold SurrogateDiagonalTailChunk000Sub001Block010HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk000Sub001Block010MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk000Sub001Block010TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk000Sub001Block010Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk000Sub001Block010_eq_head_add_mid_add_tail

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

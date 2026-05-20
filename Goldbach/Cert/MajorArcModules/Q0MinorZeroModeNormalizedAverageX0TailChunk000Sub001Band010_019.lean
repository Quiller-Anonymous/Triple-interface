import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0TailPilot25

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

open scoped BigOperators

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

/- Generated direct-term certificate blocks for tail chunk 000, subchunk 001, blocks [10,20). -/

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

/-- Block 011 covers tail-support indices [5275,5300) and q from 8723 to 8762. -/

def TailChunk000Sub001Block011Part000SupportExplicit : Finset ℕ :=
  ([8723] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block011Part000 : ℚ :=
  (5395916527 : ℚ) / 89597435904000000

def SurrogateDiagonalTailChunk000Sub001Block011Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8723
    = surrogateDiagTailX0RatChunk000Sub001Block011Part000

theorem surrogateDiagonalTailChunk000Sub001Block011Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block011Part000CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block011Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block011Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block011Part000CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block011Part000SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block011Part000] using hcert

def TailChunk000Sub001Block011Part001SupportExplicit : Finset ℕ :=
  ([8726] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block011Part001 : ℚ :=
  (297433890625 : ℚ) / 226313005661632242

def SurrogateDiagonalTailChunk000Sub001Block011Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8726
    = surrogateDiagTailX0RatChunk000Sub001Block011Part001

theorem surrogateDiagonalTailChunk000Sub001Block011Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block011Part001CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block011Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block011Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block011Part001CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block011Part001SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block011Part001] using hcert

def TailChunk000Sub001Block011Part002SupportExplicit : Finset ℕ :=
  ([8727] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block011Part002 : ℚ :=
  (528735711275 : ℚ) / 1430521714799453184

def SurrogateDiagonalTailChunk000Sub001Block011Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8727
    = surrogateDiagTailX0RatChunk000Sub001Block011Part002

theorem surrogateDiagonalTailChunk000Sub001Block011Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block011Part002CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block011Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block011Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block011Part002CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block011Part002SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block011Part002] using hcert

def TailChunk000Sub001Block011Part003SupportExplicit : Finset ℕ :=
  ([8729] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block011Part003 : ℚ :=
  (470926150675 : ℚ) / 6198136657161781248

def SurrogateDiagonalTailChunk000Sub001Block011Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8729
    = surrogateDiagTailX0RatChunk000Sub001Block011Part003

theorem surrogateDiagonalTailChunk000Sub001Block011Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block011Part003CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block011Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block011Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block011Part003CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block011Part003SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block011Part003] using hcert

def TailChunk000Sub001Block011Part004SupportExplicit : Finset ℕ :=
  ([8731] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block011Part004 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block011Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8731
    = surrogateDiagTailX0RatChunk000Sub001Block011Part004

theorem surrogateDiagonalTailChunk000Sub001Block011Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block011Part004CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block011Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block011Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block011Part004CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block011Part004SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block011Part004] using hcert

def TailChunk000Sub001Block011Part005SupportExplicit : Finset ℕ :=
  ([8733] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block011Part005 : ℚ :=
  (41854611181 : ℚ) / 98364628992000000

def SurrogateDiagonalTailChunk000Sub001Block011Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8733
    = surrogateDiagTailX0RatChunk000Sub001Block011Part005

theorem surrogateDiagonalTailChunk000Sub001Block011Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block011Part005CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block011Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block011Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block011Part005CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block011Part005SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block011Part005] using hcert

def TailChunk000Sub001Block011Part006SupportExplicit : Finset ℕ :=
  ([8734] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block011Part006 : ℚ :=
  (14680601087 : ℚ) / 8198725369190400

def SurrogateDiagonalTailChunk000Sub001Block011Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8734
    = surrogateDiagTailX0RatChunk000Sub001Block011Part006

theorem surrogateDiagonalTailChunk000Sub001Block011Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block011Part006CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block011Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block011Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block011Part006CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block011Part006SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block011Part006] using hcert

def TailChunk000Sub001Block011Part007SupportExplicit : Finset ℕ :=
  ([8735] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block011Part007 : ℚ :=
  (143154564175 : ℚ) / 1487249358754632192

def SurrogateDiagonalTailChunk000Sub001Block011Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8735
    = surrogateDiagTailX0RatChunk000Sub001Block011Part007

theorem surrogateDiagonalTailChunk000Sub001Block011Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block011Part007CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block011Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block011Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block011Part007CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block011Part007SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block011Part007] using hcert

def TailChunk000Sub001Block011Part008SupportExplicit : Finset ℕ :=
  ([8737] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block011Part008 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block011Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8737
    = surrogateDiagTailX0RatChunk000Sub001Block011Part008

theorem surrogateDiagonalTailChunk000Sub001Block011Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block011Part008CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block011Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block011Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block011Part008CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block011Part008SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block011Part008] using hcert

def TailChunk000Sub001Block011Part009SupportExplicit : Finset ℕ :=
  ([8738] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block011Part009 : ℚ :=
  (281876813875 : ℚ) / 175957044816248832

def SurrogateDiagonalTailChunk000Sub001Block011Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8738
    = surrogateDiagTailX0RatChunk000Sub001Block011Part009

theorem surrogateDiagonalTailChunk000Sub001Block011Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block011Part009CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block011Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block011Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block011Part009CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block011Part009SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block011Part009] using hcert

def TailChunk000Sub001Block011Part010SupportExplicit : Finset ℕ :=
  ([8741] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block011Part010 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block011Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8741
    = surrogateDiagTailX0RatChunk000Sub001Block011Part010

theorem surrogateDiagonalTailChunk000Sub001Block011Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block011Part010CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block011Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block011Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block011Part010CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block011Part010SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block011Part010] using hcert

def TailChunk000Sub001Block011Part011SupportExplicit : Finset ℕ :=
  ([8742] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block011Part011 : ℚ :=
  (30393462349 : ℚ) / 5803943532595200

def SurrogateDiagonalTailChunk000Sub001Block011Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8742
    = surrogateDiagTailX0RatChunk000Sub001Block011Part011

theorem surrogateDiagonalTailChunk000Sub001Block011Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block011Part011CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block011Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block011Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block011Part011CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block011Part011SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block011Part011] using hcert

def TailChunk000Sub001Block011Part012SupportExplicit : Finset ℕ :=
  ([8743] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block011Part012 : ℚ :=
  (391016811925 : ℚ) / 7861224550975930368

def SurrogateDiagonalTailChunk000Sub001Block011Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8743
    = surrogateDiagTailX0RatChunk000Sub001Block011Part012

theorem surrogateDiagonalTailChunk000Sub001Block011Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block011Part012CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block011Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block011Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block011Part012CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block011Part012SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block011Part012] using hcert

def TailChunk000Sub001Block011Part013SupportExplicit : Finset ℕ :=
  ([8745] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block011Part013 : ℚ :=
  (9610603963 : ℚ) / 7488592202956800

def SurrogateDiagonalTailChunk000Sub001Block011Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8745
    = surrogateDiagTailX0RatChunk000Sub001Block011Part013

theorem surrogateDiagonalTailChunk000Sub001Block011Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block011Part013CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block011Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block011Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block011Part013CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block011Part013SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block011Part013] using hcert

def TailChunk000Sub001Block011Part014SupportExplicit : Finset ℕ :=
  ([8746] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block011Part014 : ℚ :=
  (298798890625 : ℚ) / 228395467271622432

def SurrogateDiagonalTailChunk000Sub001Block011Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8746
    = surrogateDiagTailX0RatChunk000Sub001Block011Part014

theorem surrogateDiagonalTailChunk000Sub001Block011Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block011Part014CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block011Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block011Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block011Part014CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block011Part014SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block011Part014] using hcert

def TailChunk000Sub001Block011Part015SupportExplicit : Finset ℕ :=
  ([8747] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block011Part015 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block011Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8747
    = surrogateDiagTailX0RatChunk000Sub001Block011Part015

theorem surrogateDiagonalTailChunk000Sub001Block011Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block011Part015CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block011Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block011Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block011Part015CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block011Part015SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block011Part015] using hcert

def TailChunk000Sub001Block011Part016SupportExplicit : Finset ℕ :=
  ([8749] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block011Part016 : ℚ :=
  (397965325 : ℚ) / 18357200521003008

def SurrogateDiagonalTailChunk000Sub001Block011Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8749
    = surrogateDiagTailX0RatChunk000Sub001Block011Part016

theorem surrogateDiagonalTailChunk000Sub001Block011Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block011Part016CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block011Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block011Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block011Part016CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block011Part016SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block011Part016] using hcert

def TailChunk000Sub001Block011Part017SupportExplicit : Finset ℕ :=
  ([8751] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block011Part017 : ℚ :=
  (531647128475 : ℚ) / 1446328434628076544

def SurrogateDiagonalTailChunk000Sub001Block011Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8751
    = surrogateDiagTailX0RatChunk000Sub001Block011Part017

theorem surrogateDiagonalTailChunk000Sub001Block011Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block011Part017CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block011Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block011Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block011Part017CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block011Part017SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block011Part017] using hcert

def TailChunk000Sub001Block011Part018SupportExplicit : Finset ℕ :=
  ([8753] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block011Part018 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block011Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8753
    = surrogateDiagTailX0RatChunk000Sub001Block011Part018

theorem surrogateDiagonalTailChunk000Sub001Block011Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block011Part018CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block011Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block011Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block011Part018CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block011Part018SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block011Part018] using hcert

def TailChunk000Sub001Block011Part019SupportExplicit : Finset ℕ :=
  ([8754] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block011Part019 : ℚ :=
  (930805958275 : ℚ) / 180791054328509568

def SurrogateDiagonalTailChunk000Sub001Block011Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8754
    = surrogateDiagTailX0RatChunk000Sub001Block011Part019

theorem surrogateDiagonalTailChunk000Sub001Block011Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block011Part019CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block011Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block011Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block011Part019CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block011Part019SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block011Part019] using hcert

def TailChunk000Sub001Block011Part020SupportExplicit : Finset ℕ :=
  ([8755] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block011Part020 : ℚ :=
  (23923215725 : ℚ) / 168183612900900864

def SurrogateDiagonalTailChunk000Sub001Block011Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8755
    = surrogateDiagTailX0RatChunk000Sub001Block011Part020

theorem surrogateDiagonalTailChunk000Sub001Block011Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block011Part020CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block011Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block011Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block011Part020CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block011Part020SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block011Part020] using hcert

def TailChunk000Sub001Block011Part021SupportExplicit : Finset ℕ :=
  ([8758] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block011Part021 : ℚ :=
  (73422583 : ℚ) / 49401878400000

def SurrogateDiagonalTailChunk000Sub001Block011Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8758
    = surrogateDiagTailX0RatChunk000Sub001Block011Part021

theorem surrogateDiagonalTailChunk000Sub001Block011Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block011Part021CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block011Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block011Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block011Part021CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block011Part021SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block011Part021] using hcert

def TailChunk000Sub001Block011Part022SupportExplicit : Finset ℕ :=
  ([8759] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block011Part022 : ℚ :=
  (80429587 : ℚ) / 6268259015202816

def SurrogateDiagonalTailChunk000Sub001Block011Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8759
    = surrogateDiagTailX0RatChunk000Sub001Block011Part022

theorem surrogateDiagonalTailChunk000Sub001Block011Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block011Part022CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block011Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block011Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block011Part022CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block011Part022SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block011Part022] using hcert

def TailChunk000Sub001Block011Part023SupportExplicit : Finset ℕ :=
  ([8761] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block011Part023 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block011Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8761
    = surrogateDiagTailX0RatChunk000Sub001Block011Part023

theorem surrogateDiagonalTailChunk000Sub001Block011Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block011Part023CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block011Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block011Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block011Part023CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block011Part023SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block011Part023] using hcert

def TailChunk000Sub001Block011Part024SupportExplicit : Finset ℕ :=
  ([8762] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block011Part024 : ℚ :=
  (124312177475 : ℚ) / 73428802084012032

def SurrogateDiagonalTailChunk000Sub001Block011Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8762
    = surrogateDiagTailX0RatChunk000Sub001Block011Part024

theorem surrogateDiagonalTailChunk000Sub001Block011Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block011Part024CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block011Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block011Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block011Part024CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block011Part024SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block011Part024] using hcert

def surrogateDiagonalTailChunk000Sub001Block011HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block011Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block011Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block011Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block011Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block011Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block011Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block011Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block011Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block011Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block011Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block011Head : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block011Part000
    + surrogateDiagTailX0RatChunk000Sub001Block011Part001
    + surrogateDiagTailX0RatChunk000Sub001Block011Part002
    + surrogateDiagTailX0RatChunk000Sub001Block011Part003
    + surrogateDiagTailX0RatChunk000Sub001Block011Part004
    + surrogateDiagTailX0RatChunk000Sub001Block011Part005
    + surrogateDiagTailX0RatChunk000Sub001Block011Part006
    + surrogateDiagTailX0RatChunk000Sub001Block011Part007
    + surrogateDiagTailX0RatChunk000Sub001Block011Part008
    + surrogateDiagTailX0RatChunk000Sub001Block011Part009

def surrogateDiagonalTailChunk000Sub001Block011MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block011Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block011Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block011Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block011Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block011Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block011Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block011Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block011Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block011Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block011Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block011Mid : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block011Part010
    + surrogateDiagTailX0RatChunk000Sub001Block011Part011
    + surrogateDiagTailX0RatChunk000Sub001Block011Part012
    + surrogateDiagTailX0RatChunk000Sub001Block011Part013
    + surrogateDiagTailX0RatChunk000Sub001Block011Part014
    + surrogateDiagTailX0RatChunk000Sub001Block011Part015
    + surrogateDiagTailX0RatChunk000Sub001Block011Part016
    + surrogateDiagTailX0RatChunk000Sub001Block011Part017
    + surrogateDiagTailX0RatChunk000Sub001Block011Part018
    + surrogateDiagTailX0RatChunk000Sub001Block011Part019

def surrogateDiagonalTailChunk000Sub001Block011TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block011Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block011Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block011Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block011Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block011Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block011Tail : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block011Part020
    + surrogateDiagTailX0RatChunk000Sub001Block011Part021
    + surrogateDiagTailX0RatChunk000Sub001Block011Part022
    + surrogateDiagTailX0RatChunk000Sub001Block011Part023
    + surrogateDiagTailX0RatChunk000Sub001Block011Part024

def surrogateDiagonalTailChunk000Sub001Block011Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub001Block011HeadSum X0
    + surrogateDiagonalTailChunk000Sub001Block011MidSum X0
    + surrogateDiagonalTailChunk000Sub001Block011TailSum X0

def surrogateDiagTailX0RatChunk000Sub001Block011 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block011Part000
    + surrogateDiagTailX0RatChunk000Sub001Block011Part001
    + surrogateDiagTailX0RatChunk000Sub001Block011Part002
    + surrogateDiagTailX0RatChunk000Sub001Block011Part003
    + surrogateDiagTailX0RatChunk000Sub001Block011Part004
    + surrogateDiagTailX0RatChunk000Sub001Block011Part005
    + surrogateDiagTailX0RatChunk000Sub001Block011Part006
    + surrogateDiagTailX0RatChunk000Sub001Block011Part007
    + surrogateDiagTailX0RatChunk000Sub001Block011Part008
    + surrogateDiagTailX0RatChunk000Sub001Block011Part009
    + surrogateDiagTailX0RatChunk000Sub001Block011Part010
    + surrogateDiagTailX0RatChunk000Sub001Block011Part011
    + surrogateDiagTailX0RatChunk000Sub001Block011Part012
    + surrogateDiagTailX0RatChunk000Sub001Block011Part013
    + surrogateDiagTailX0RatChunk000Sub001Block011Part014
    + surrogateDiagTailX0RatChunk000Sub001Block011Part015
    + surrogateDiagTailX0RatChunk000Sub001Block011Part016
    + surrogateDiagTailX0RatChunk000Sub001Block011Part017
    + surrogateDiagTailX0RatChunk000Sub001Block011Part018
    + surrogateDiagTailX0RatChunk000Sub001Block011Part019
    + surrogateDiagTailX0RatChunk000Sub001Block011Part020
    + surrogateDiagTailX0RatChunk000Sub001Block011Part021
    + surrogateDiagTailX0RatChunk000Sub001Block011Part022
    + surrogateDiagTailX0RatChunk000Sub001Block011Part023
    + surrogateDiagTailX0RatChunk000Sub001Block011Part024

theorem surrogateDiagTailX0RatChunk000Sub001Block011_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk000Sub001Block011Head + surrogateDiagTailX0RatChunk000Sub001Block011Mid + surrogateDiagTailX0RatChunk000Sub001Block011Tail =
      surrogateDiagTailX0RatChunk000Sub001Block011 := by
  unfold surrogateDiagTailX0RatChunk000Sub001Block011Head surrogateDiagTailX0RatChunk000Sub001Block011Mid surrogateDiagTailX0RatChunk000Sub001Block011Tail surrogateDiagTailX0RatChunk000Sub001Block011
  ring

def SurrogateDiagonalTailChunk000Sub001Block011HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block011HeadSum X0 = surrogateDiagTailX0RatChunk000Sub001Block011Head

def SurrogateDiagonalTailChunk000Sub001Block011MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block011MidSum X0 = surrogateDiagTailX0RatChunk000Sub001Block011Mid

def SurrogateDiagonalTailChunk000Sub001Block011TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block011TailSum X0 = surrogateDiagTailX0RatChunk000Sub001Block011Tail

theorem surrogateDiagonalTailChunk000Sub001Block011_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk000Sub001Block011HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk000Sub001Block011MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk000Sub001Block011TailCertificateAt X0) :
    surrogateDiagonalTailChunk000Sub001Block011Sum X0 = surrogateDiagTailX0RatChunk000Sub001Block011 := by
  unfold SurrogateDiagonalTailChunk000Sub001Block011HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk000Sub001Block011MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk000Sub001Block011TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk000Sub001Block011Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk000Sub001Block011_eq_head_add_mid_add_tail

/-- Block 012 covers tail-support indices [5300,5325) and q from 8763 to 8801. -/

def TailChunk000Sub001Block012Part000SupportExplicit : Finset ℕ :=
  ([8763] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block012Part000 : ℚ :=
  (31684587925 : ℚ) / 131234264076174336

def SurrogateDiagonalTailChunk000Sub001Block012Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8763
    = surrogateDiagTailX0RatChunk000Sub001Block012Part000

theorem surrogateDiagonalTailChunk000Sub001Block012Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block012Part000CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block012Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block012Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block012Part000CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block012Part000SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block012Part000] using hcert

def TailChunk000Sub001Block012Part001SupportExplicit : Finset ℕ :=
  ([8765] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block012Part001 : ℚ :=
  (288275964725 : ℚ) / 3015596536632705024

def SurrogateDiagonalTailChunk000Sub001Block012Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8765
    = surrogateDiagTailX0RatChunk000Sub001Block012Part001

theorem surrogateDiagonalTailChunk000Sub001Block012Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block012Part001CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block012Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block012Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block012Part001CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block012Part001SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block012Part001] using hcert

def TailChunk000Sub001Block012Part002SupportExplicit : Finset ℕ :=
  ([8767] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block012Part002 : ℚ :=
  (961981297 : ℚ) / 40154952930309120

def SurrogateDiagonalTailChunk000Sub001Block012Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8767
    = surrogateDiagTailX0RatChunk000Sub001Block012Part002

theorem surrogateDiagonalTailChunk000Sub001Block012Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block012Part002CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block012Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block012Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block012Part002CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block012Part002SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block012Part002] using hcert

def TailChunk000Sub001Block012Part003SupportExplicit : Finset ℕ :=
  ([8769] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block012Part003 : ℚ :=
  (562730433325 : ℚ) / 2487340580582227968

def SurrogateDiagonalTailChunk000Sub001Block012Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8769
    = surrogateDiagTailX0RatChunk000Sub001Block012Part003

theorem surrogateDiagonalTailChunk000Sub001Block012Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block012Part003CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block012Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block012Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block012Part003CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block012Part003SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block012Part003] using hcert

def TailChunk000Sub001Block012Part004SupportExplicit : Finset ℕ :=
  ([8770] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block012Part004 : ℚ :=
  (480330921875 : ℚ) / 188474783539544064

def SurrogateDiagonalTailChunk000Sub001Block012Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8770
    = surrogateDiagTailX0RatChunk000Sub001Block012Part004

theorem surrogateDiagonalTailChunk000Sub001Block012Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block012Part004CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block012Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block012Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block012Part004CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block012Part004SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block012Part004] using hcert

def TailChunk000Sub001Block012Part005SupportExplicit : Finset ℕ :=
  ([8773] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block012Part005 : ℚ :=
  (36542111861 : ℚ) / 102470368506906240

def SurrogateDiagonalTailChunk000Sub001Block012Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8773
    = surrogateDiagTailX0RatChunk000Sub001Block012Part005

theorem surrogateDiagonalTailChunk000Sub001Block012Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block012Part005CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block012Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block012Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block012Part005CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block012Part005SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block012Part005] using hcert

def TailChunk000Sub001Block012Part006SupportExplicit : Finset ℕ :=
  ([8774] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block012Part006 : ℚ :=
  (30551818353 : ℚ) / 10775291352678400

def SurrogateDiagonalTailChunk000Sub001Block012Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8774
    = surrogateDiagTailX0RatChunk000Sub001Block012Part006

theorem surrogateDiagonalTailChunk000Sub001Block012Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block012Part006CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block012Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block012Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block012Part006CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block012Part006SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block012Part006] using hcert

def TailChunk000Sub001Block012Part007SupportExplicit : Finset ℕ :=
  ([8777] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block012Part007 : ℚ :=
  (651931789 : ℚ) / 1895265113227200

def SurrogateDiagonalTailChunk000Sub001Block012Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8777
    = surrogateDiagTailX0RatChunk000Sub001Block012Part007

theorem surrogateDiagonalTailChunk000Sub001Block012Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block012Part007CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block012Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block012Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block012Part007CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block012Part007SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block012Part007] using hcert

def TailChunk000Sub001Block012Part008SupportExplicit : Finset ℕ :=
  ([8778] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block012Part008 : ℚ :=
  (11939557379 : ℚ) / 725739230822400

def SurrogateDiagonalTailChunk000Sub001Block012Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8778
    = surrogateDiagTailX0RatChunk000Sub001Block012Part008

theorem surrogateDiagonalTailChunk000Sub001Block012Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block012Part008CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block012Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block012Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block012Part008CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block012Part008SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block012Part008] using hcert

def TailChunk000Sub001Block012Part009SupportExplicit : Finset ℕ :=
  ([8779] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block012Part009 : ℚ :=
  (1204231890625 : ℚ) / 3711497510562308082

def SurrogateDiagonalTailChunk000Sub001Block012Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8779
    = surrogateDiagTailX0RatChunk000Sub001Block012Part009

theorem surrogateDiagonalTailChunk000Sub001Block012Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block012Part009CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block012Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block012Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block012Part009CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block012Part009SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block012Part009] using hcert

def TailChunk000Sub001Block012Part010SupportExplicit : Finset ℕ :=
  ([8781] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block012Part010 : ℚ :=
  (669128547025 : ℚ) / 733135310728357152

def SurrogateDiagonalTailChunk000Sub001Block012Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8781
    = surrogateDiagTailX0RatChunk000Sub001Block012Part010

theorem surrogateDiagonalTailChunk000Sub001Block012Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block012Part010CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block012Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block012Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block012Part010CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block012Part010SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block012Part010] using hcert

def TailChunk000Sub001Block012Part011SupportExplicit : Finset ℕ :=
  ([8782] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block012Part011 : ℚ :=
  (96385124119 : ℚ) / 37148812117768200

def SurrogateDiagonalTailChunk000Sub001Block012Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8782
    = surrogateDiagTailX0RatChunk000Sub001Block012Part011

theorem surrogateDiagonalTailChunk000Sub001Block012Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block012Part011CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block012Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block012Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block012Part011CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block012Part011SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block012Part011] using hcert

def TailChunk000Sub001Block012Part012SupportExplicit : Finset ℕ :=
  ([8783] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block012Part012 : ℚ :=
  (1205329515625 : ℚ) / 3718267226105882322

def SurrogateDiagonalTailChunk000Sub001Block012Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8783
    = surrogateDiagTailX0RatChunk000Sub001Block012Part012

theorem surrogateDiagonalTailChunk000Sub001Block012Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block012Part012CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block012Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block012Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block012Part012CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block012Part012SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block012Part012] using hcert

def TailChunk000Sub001Block012Part013SupportExplicit : Finset ℕ :=
  ([8785] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block012Part013 : ℚ :=
  (13887072767 : ℚ) / 16203240000000000

def SurrogateDiagonalTailChunk000Sub001Block012Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8785
    = surrogateDiagTailX0RatChunk000Sub001Block012Part013

theorem surrogateDiagonalTailChunk000Sub001Block012Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block012Part013CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block012Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block012Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block012Part013CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block012Part013SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block012Part013] using hcert

def TailChunk000Sub001Block012Part014SupportExplicit : Finset ℕ :=
  ([8786] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block012Part014 : ℚ :=
  (46219591117 : ℚ) / 30534581871235200

def SurrogateDiagonalTailChunk000Sub001Block012Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8786
    = surrogateDiagTailX0RatChunk000Sub001Block012Part014

theorem surrogateDiagonalTailChunk000Sub001Block012Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block012Part014CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block012Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block012Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block012Part014CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block012Part014SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block012Part014] using hcert

def TailChunk000Sub001Block012Part015SupportExplicit : Finset ℕ :=
  ([8787] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block012Part015 : ℚ :=
  (101026604479 : ℚ) / 98364628992000000

def SurrogateDiagonalTailChunk000Sub001Block012Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8787
    = surrogateDiagTailX0RatChunk000Sub001Block012Part015

theorem surrogateDiagonalTailChunk000Sub001Block012Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block012Part015CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block012Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block012Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block012Part015CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block012Part015SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block012Part015] using hcert

def TailChunk000Sub001Block012Part016SupportExplicit : Finset ℕ :=
  ([8789] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block012Part016 : ℚ :=
  (75116666813 : ℚ) / 146746621663641600

def SurrogateDiagonalTailChunk000Sub001Block012Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8789
    = surrogateDiagTailX0RatChunk000Sub001Block012Part016

theorem surrogateDiagonalTailChunk000Sub001Block012Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block012Part016CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block012Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block012Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block012Part016CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block012Part016SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block012Part016] using hcert

def TailChunk000Sub001Block012Part017SupportExplicit : Finset ℕ :=
  ([8790] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block012Part017 : ℚ :=
  (334375017425 : ℚ) / 37229586872008704

def SurrogateDiagonalTailChunk000Sub001Block012Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8790
    = surrogateDiagTailX0RatChunk000Sub001Block012Part017

theorem surrogateDiagonalTailChunk000Sub001Block012Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block012Part017CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block012Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block012Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block012Part017CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block012Part017SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block012Part017] using hcert

def TailChunk000Sub001Block012Part018SupportExplicit : Finset ℕ :=
  ([8791] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block012Part018 : ℚ :=
  (1556406911775 : ℚ) / 4525477812682233856

def SurrogateDiagonalTailChunk000Sub001Block012Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8791
    = surrogateDiagTailX0RatChunk000Sub001Block012Part018

theorem surrogateDiagonalTailChunk000Sub001Block012Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block012Part018CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block012Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block012Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block012Part018CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block012Part018SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block012Part018] using hcert

def TailChunk000Sub001Block012Part019SupportExplicit : Finset ℕ :=
  ([8794] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block012Part019 : ℚ :=
  (302087640625 : ℚ) / 233452001960339232

def SurrogateDiagonalTailChunk000Sub001Block012Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8794
    = surrogateDiagTailX0RatChunk000Sub001Block012Part019

theorem surrogateDiagonalTailChunk000Sub001Block012Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block012Part019CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block012Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block012Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block012Part019CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block012Part019SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block012Part019] using hcert

def TailChunk000Sub001Block012Part020SupportExplicit : Finset ℕ :=
  ([8795] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block012Part020 : ℚ :=
  (3478675649425 : ℚ) / 6114237539368716288

def SurrogateDiagonalTailChunk000Sub001Block012Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8795
    = surrogateDiagTailX0RatChunk000Sub001Block012Part020

theorem surrogateDiagonalTailChunk000Sub001Block012Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block012Part020CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block012Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block012Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block012Part020CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block012Part020SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block012Part020] using hcert

def TailChunk000Sub001Block012Part021SupportExplicit : Finset ℕ :=
  ([8797] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block012Part021 : ℚ :=
  (123943468975 : ℚ) / 332186730942816288

def SurrogateDiagonalTailChunk000Sub001Block012Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8797
    = surrogateDiagTailX0RatChunk000Sub001Block012Part021

theorem surrogateDiagonalTailChunk000Sub001Block012Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block012Part021CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block012Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block012Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block012Part021CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block012Part021SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block012Part021] using hcert

def TailChunk000Sub001Block012Part022SupportExplicit : Finset ℕ :=
  ([8798] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block012Part022 : ℚ :=
  (392523475875 : ℚ) / 275533486875252736

def SurrogateDiagonalTailChunk000Sub001Block012Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8798
    = surrogateDiagTailX0RatChunk000Sub001Block012Part022

theorem surrogateDiagonalTailChunk000Sub001Block012Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block012Part022CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block012Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block012Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block012Part022CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block012Part022SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block012Part022] using hcert

def TailChunk000Sub001Block012Part023SupportExplicit : Finset ℕ :=
  ([8799] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block012Part023 : ℚ :=
  (2177194029625 : ℚ) / 1582912724204832768

def SurrogateDiagonalTailChunk000Sub001Block012Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8799
    = surrogateDiagTailX0RatChunk000Sub001Block012Part023

theorem surrogateDiagonalTailChunk000Sub001Block012Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block012Part023CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block012Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block012Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block012Part023CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block012Part023SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block012Part023] using hcert

def TailChunk000Sub001Block012Part024SupportExplicit : Finset ℕ :=
  ([8801] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block012Part024 : ℚ :=
  (4288545861775 : ℚ) / 10827760146625363968

def SurrogateDiagonalTailChunk000Sub001Block012Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8801
    = surrogateDiagTailX0RatChunk000Sub001Block012Part024

theorem surrogateDiagonalTailChunk000Sub001Block012Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block012Part024CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block012Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block012Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block012Part024CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block012Part024SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block012Part024] using hcert

def surrogateDiagonalTailChunk000Sub001Block012HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block012Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block012Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block012Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block012Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block012Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block012Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block012Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block012Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block012Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block012Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block012Head : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block012Part000
    + surrogateDiagTailX0RatChunk000Sub001Block012Part001
    + surrogateDiagTailX0RatChunk000Sub001Block012Part002
    + surrogateDiagTailX0RatChunk000Sub001Block012Part003
    + surrogateDiagTailX0RatChunk000Sub001Block012Part004
    + surrogateDiagTailX0RatChunk000Sub001Block012Part005
    + surrogateDiagTailX0RatChunk000Sub001Block012Part006
    + surrogateDiagTailX0RatChunk000Sub001Block012Part007
    + surrogateDiagTailX0RatChunk000Sub001Block012Part008
    + surrogateDiagTailX0RatChunk000Sub001Block012Part009

def surrogateDiagonalTailChunk000Sub001Block012MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block012Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block012Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block012Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block012Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block012Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block012Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block012Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block012Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block012Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block012Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block012Mid : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block012Part010
    + surrogateDiagTailX0RatChunk000Sub001Block012Part011
    + surrogateDiagTailX0RatChunk000Sub001Block012Part012
    + surrogateDiagTailX0RatChunk000Sub001Block012Part013
    + surrogateDiagTailX0RatChunk000Sub001Block012Part014
    + surrogateDiagTailX0RatChunk000Sub001Block012Part015
    + surrogateDiagTailX0RatChunk000Sub001Block012Part016
    + surrogateDiagTailX0RatChunk000Sub001Block012Part017
    + surrogateDiagTailX0RatChunk000Sub001Block012Part018
    + surrogateDiagTailX0RatChunk000Sub001Block012Part019

def surrogateDiagonalTailChunk000Sub001Block012TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block012Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block012Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block012Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block012Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block012Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block012Tail : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block012Part020
    + surrogateDiagTailX0RatChunk000Sub001Block012Part021
    + surrogateDiagTailX0RatChunk000Sub001Block012Part022
    + surrogateDiagTailX0RatChunk000Sub001Block012Part023
    + surrogateDiagTailX0RatChunk000Sub001Block012Part024

def surrogateDiagonalTailChunk000Sub001Block012Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub001Block012HeadSum X0
    + surrogateDiagonalTailChunk000Sub001Block012MidSum X0
    + surrogateDiagonalTailChunk000Sub001Block012TailSum X0

def surrogateDiagTailX0RatChunk000Sub001Block012 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block012Part000
    + surrogateDiagTailX0RatChunk000Sub001Block012Part001
    + surrogateDiagTailX0RatChunk000Sub001Block012Part002
    + surrogateDiagTailX0RatChunk000Sub001Block012Part003
    + surrogateDiagTailX0RatChunk000Sub001Block012Part004
    + surrogateDiagTailX0RatChunk000Sub001Block012Part005
    + surrogateDiagTailX0RatChunk000Sub001Block012Part006
    + surrogateDiagTailX0RatChunk000Sub001Block012Part007
    + surrogateDiagTailX0RatChunk000Sub001Block012Part008
    + surrogateDiagTailX0RatChunk000Sub001Block012Part009
    + surrogateDiagTailX0RatChunk000Sub001Block012Part010
    + surrogateDiagTailX0RatChunk000Sub001Block012Part011
    + surrogateDiagTailX0RatChunk000Sub001Block012Part012
    + surrogateDiagTailX0RatChunk000Sub001Block012Part013
    + surrogateDiagTailX0RatChunk000Sub001Block012Part014
    + surrogateDiagTailX0RatChunk000Sub001Block012Part015
    + surrogateDiagTailX0RatChunk000Sub001Block012Part016
    + surrogateDiagTailX0RatChunk000Sub001Block012Part017
    + surrogateDiagTailX0RatChunk000Sub001Block012Part018
    + surrogateDiagTailX0RatChunk000Sub001Block012Part019
    + surrogateDiagTailX0RatChunk000Sub001Block012Part020
    + surrogateDiagTailX0RatChunk000Sub001Block012Part021
    + surrogateDiagTailX0RatChunk000Sub001Block012Part022
    + surrogateDiagTailX0RatChunk000Sub001Block012Part023
    + surrogateDiagTailX0RatChunk000Sub001Block012Part024

theorem surrogateDiagTailX0RatChunk000Sub001Block012_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk000Sub001Block012Head + surrogateDiagTailX0RatChunk000Sub001Block012Mid + surrogateDiagTailX0RatChunk000Sub001Block012Tail =
      surrogateDiagTailX0RatChunk000Sub001Block012 := by
  unfold surrogateDiagTailX0RatChunk000Sub001Block012Head surrogateDiagTailX0RatChunk000Sub001Block012Mid surrogateDiagTailX0RatChunk000Sub001Block012Tail surrogateDiagTailX0RatChunk000Sub001Block012
  ring

def SurrogateDiagonalTailChunk000Sub001Block012HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block012HeadSum X0 = surrogateDiagTailX0RatChunk000Sub001Block012Head

def SurrogateDiagonalTailChunk000Sub001Block012MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block012MidSum X0 = surrogateDiagTailX0RatChunk000Sub001Block012Mid

def SurrogateDiagonalTailChunk000Sub001Block012TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block012TailSum X0 = surrogateDiagTailX0RatChunk000Sub001Block012Tail

theorem surrogateDiagonalTailChunk000Sub001Block012_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk000Sub001Block012HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk000Sub001Block012MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk000Sub001Block012TailCertificateAt X0) :
    surrogateDiagonalTailChunk000Sub001Block012Sum X0 = surrogateDiagTailX0RatChunk000Sub001Block012 := by
  unfold SurrogateDiagonalTailChunk000Sub001Block012HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk000Sub001Block012MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk000Sub001Block012TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk000Sub001Block012Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk000Sub001Block012_eq_head_add_mid_add_tail

/-- Block 013 covers tail-support indices [5325,5350) and q from 8803 to 8842. -/

def TailChunk000Sub001Block013Part000SupportExplicit : Finset ℕ :=
  ([8803] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block013Part000 : ℚ :=
  (1210825140625 : ℚ) / 3752254822680365202

def SurrogateDiagonalTailChunk000Sub001Block013Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8803
    = surrogateDiagTailX0RatChunk000Sub001Block013Part000

theorem surrogateDiagonalTailChunk000Sub001Block013Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block013Part000CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block013Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block013Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block013Part000CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block013Part000SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block013Part000] using hcert

def TailChunk000Sub001Block013Part001SupportExplicit : Finset ℕ :=
  ([8805] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block013Part001 : ℚ :=
  (31230856975 : ℚ) / 18871103516570112

def SurrogateDiagonalTailChunk000Sub001Block013Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8805
    = surrogateDiagTailX0RatChunk000Sub001Block013Part001

theorem surrogateDiagonalTailChunk000Sub001Block013Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block013Part001CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block013Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block013Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block013Part001CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block013Part001SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block013Part001] using hcert

def TailChunk000Sub001Block013Part002SupportExplicit : Finset ℕ :=
  ([8806] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block013Part002 : ℚ :=
  (327470142175 : ℚ) / 118905115577942016

def SurrogateDiagonalTailChunk000Sub001Block013Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8806
    = surrogateDiagTailX0RatChunk000Sub001Block013Part002

theorem surrogateDiagonalTailChunk000Sub001Block013Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block013Part002CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block013Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block013Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block013Part002CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block013Part002SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block013Part002] using hcert

def TailChunk000Sub001Block013Part003SupportExplicit : Finset ℕ :=
  ([8807] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block013Part003 : ℚ :=
  (1211925765625 : ℚ) / 3759080204860640562

def SurrogateDiagonalTailChunk000Sub001Block013Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8807
    = surrogateDiagTailX0RatChunk000Sub001Block013Part003

theorem surrogateDiagonalTailChunk000Sub001Block013Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block013Part003CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block013Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block013Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block013Part003CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block013Part003SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block013Part003] using hcert

def TailChunk000Sub001Block013Part004SupportExplicit : Finset ℕ :=
  ([8809] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block013Part004 : ℚ :=
  (755199670875 : ℚ) / 2078833866932765888

def SurrogateDiagonalTailChunk000Sub001Block013Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8809
    = surrogateDiagTailX0RatChunk000Sub001Block013Part004

theorem surrogateDiagonalTailChunk000Sub001Block013Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block013Part004CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block013Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block013Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block013Part004CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block013Part004SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block013Part004] using hcert

def TailChunk000Sub001Block013Part005SupportExplicit : Finset ℕ :=
  ([8810] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block013Part005 : ℚ :=
  (2714249139 : ℚ) / 1023684777082880

def SurrogateDiagonalTailChunk000Sub001Block013Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8810
    = surrogateDiagTailX0RatChunk000Sub001Block013Part005

theorem surrogateDiagonalTailChunk000Sub001Block013Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block013Part005CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block013Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block013Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block013Part005CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block013Part005SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block013Part005] using hcert

def TailChunk000Sub001Block013Part006SupportExplicit : Finset ℕ :=
  ([8813] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block013Part006 : ℚ :=
  (214442501075 : ℚ) / 450901748854587456

def SurrogateDiagonalTailChunk000Sub001Block013Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8813
    = surrogateDiagTailX0RatChunk000Sub001Block013Part006

theorem surrogateDiagonalTailChunk000Sub001Block013Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block013Part006CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block013Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block013Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block013Part006CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block013Part006SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block013Part006] using hcert

def TailChunk000Sub001Block013Part007SupportExplicit : Finset ℕ :=
  ([8814] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block013Part007 : ℚ :=
  (375410472275 : ℚ) / 65270046296899584

def SurrogateDiagonalTailChunk000Sub001Block013Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8814
    = surrogateDiagTailX0RatChunk000Sub001Block013Part007

theorem surrogateDiagonalTailChunk000Sub001Block013Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block013Part007CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block013Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block013Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block013Part007CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block013Part007SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block013Part007] using hcert

def TailChunk000Sub001Block013Part008SupportExplicit : Finset ℕ :=
  ([8815] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block013Part008 : ℚ :=
  (130889101351 : ℚ) / 203968894677811200

def SurrogateDiagonalTailChunk000Sub001Block013Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8815
    = surrogateDiagTailX0RatChunk000Sub001Block013Part008

theorem surrogateDiagonalTailChunk000Sub001Block013Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block013Part008CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block013Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block013Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block013Part008CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block013Part008SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block013Part008] using hcert

def TailChunk000Sub001Block013Part009SupportExplicit : Finset ℕ :=
  ([8817] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block013Part009 : ℚ :=
  (2158585706125 : ℚ) / 2980945303460162688

def SurrogateDiagonalTailChunk000Sub001Block013Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8817
    = surrogateDiagTailX0RatChunk000Sub001Block013Part009

theorem surrogateDiagonalTailChunk000Sub001Block013Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block013Part009CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block013Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block013Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block013Part009CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block013Part009SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block013Part009] using hcert

def TailChunk000Sub001Block013Part010SupportExplicit : Finset ℕ :=
  ([8818] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block013Part010 : ℚ :=
  (303738765625 : ℚ) / 236011524900966912

def SurrogateDiagonalTailChunk000Sub001Block013Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8818
    = surrogateDiagTailX0RatChunk000Sub001Block013Part010

theorem surrogateDiagonalTailChunk000Sub001Block013Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block013Part010CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block013Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block013Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block013Part010CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block013Part010SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block013Part010] using hcert

def TailChunk000Sub001Block013Part011SupportExplicit : Finset ℕ :=
  ([8819] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block013Part011 : ℚ :=
  (1215230640625 : ℚ) / 3779612229261203922

def SurrogateDiagonalTailChunk000Sub001Block013Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8819
    = surrogateDiagTailX0RatChunk000Sub001Block013Part011

theorem surrogateDiagonalTailChunk000Sub001Block013Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block013Part011CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block013Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block013Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block013Part011CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block013Part011SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block013Part011] using hcert

def TailChunk000Sub001Block013Part012SupportExplicit : Finset ℕ :=
  ([8821] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block013Part012 : ℚ :=
  (1945251025 : ℚ) / 6052867829259552

def SurrogateDiagonalTailChunk000Sub001Block013Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8821
    = surrogateDiagTailX0RatChunk000Sub001Block013Part012

theorem surrogateDiagonalTailChunk000Sub001Block013Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block013Part012CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block013Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block013Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block013Part012CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block013Part012SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block013Part012] using hcert

def TailChunk000Sub001Block013Part013SupportExplicit : Finset ℕ :=
  ([8822] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block013Part013 : ℚ :=
  (44933495149 : ℚ) / 25605120000000000

def SurrogateDiagonalTailChunk000Sub001Block013Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8822
    = surrogateDiagTailX0RatChunk000Sub001Block013Part013

theorem surrogateDiagonalTailChunk000Sub001Block013Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block013Part013CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block013Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block013Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block013Part013CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block013Part013SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block013Part013] using hcert

def TailChunk000Sub001Block013Part014SupportExplicit : Finset ℕ :=
  ([8823] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block013Part014 : ℚ :=
  (668331176325 : ℚ) / 764925792407781376

def SurrogateDiagonalTailChunk000Sub001Block013Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8823
    = surrogateDiagTailX0RatChunk000Sub001Block013Part014

theorem surrogateDiagonalTailChunk000Sub001Block013Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block013Part014CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block013Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block013Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block013Part014CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block013Part014SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block013Part014] using hcert

def TailChunk000Sub001Block013Part015SupportExplicit : Finset ℕ :=
  ([8826] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block013Part015 : ℚ :=
  (37847223727 : ℚ) / 7472676332419200

def SurrogateDiagonalTailChunk000Sub001Block013Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8826
    = surrogateDiagTailX0RatChunk000Sub001Block013Part015

theorem surrogateDiagonalTailChunk000Sub001Block013Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block013Part015CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block013Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block013Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block013Part015CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block013Part015SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block013Part015] using hcert

def TailChunk000Sub001Block013Part016SupportExplicit : Finset ℕ :=
  ([8827] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block013Part016 : ℚ :=
  (378450098875 : ℚ) / 634160616415690752

def SurrogateDiagonalTailChunk000Sub001Block013Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8827
    = surrogateDiagTailX0RatChunk000Sub001Block013Part016

theorem surrogateDiagonalTailChunk000Sub001Block013Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block013Part016CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block013Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block013Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block013Part016CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block013Part016SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block013Part016] using hcert

def TailChunk000Sub001Block013Part017SupportExplicit : Finset ℕ :=
  ([8830] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block013Part017 : ℚ :=
  (486924740375 : ℚ) / 193691770536305664

def SurrogateDiagonalTailChunk000Sub001Block013Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8830
    = surrogateDiagTailX0RatChunk000Sub001Block013Part017

theorem surrogateDiagonalTailChunk000Sub001Block013Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block013Part017CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block013Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block013Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block013Part017CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block013Part017SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block013Part017] using hcert

def TailChunk000Sub001Block013Part018SupportExplicit : Finset ℕ :=
  ([8831] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block013Part018 : ℚ :=
  (1949664025 : ℚ) / 6080365197083442

def SurrogateDiagonalTailChunk000Sub001Block013Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8831
    = surrogateDiagTailX0RatChunk000Sub001Block013Part018

theorem surrogateDiagonalTailChunk000Sub001Block013Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block013Part018CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block013Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block013Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block013Part018CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block013Part018SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block013Part018] using hcert

def TailChunk000Sub001Block013Part019SupportExplicit : Finset ℕ :=
  ([8834] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block013Part019 : ℚ :=
  (10687492783 : ℚ) / 5104980155872800

def SurrogateDiagonalTailChunk000Sub001Block013Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8834
    = surrogateDiagTailX0RatChunk000Sub001Block013Part019

theorem surrogateDiagonalTailChunk000Sub001Block013Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block013Part019CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block013Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block013Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block013Part019CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block013Part019SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block013Part019] using hcert

def TailChunk000Sub001Block013Part020SupportExplicit : Finset ℕ :=
  ([8835] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block013Part020 : ℚ :=
  (72246469153 : ℚ) / 34835483079475200

def SurrogateDiagonalTailChunk000Sub001Block013Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8835
    = surrogateDiagTailX0RatChunk000Sub001Block013Part020

theorem surrogateDiagonalTailChunk000Sub001Block013Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block013Part020CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block013Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block013Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block013Part020CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block013Part020SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block013Part020] using hcert

def TailChunk000Sub001Block013Part021SupportExplicit : Finset ℕ :=
  ([8837] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block013Part021 : ℚ :=
  (1220196390625 : ℚ) / 3810567827054936352

def SurrogateDiagonalTailChunk000Sub001Block013Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8837
    = surrogateDiagTailX0RatChunk000Sub001Block013Part021

theorem surrogateDiagonalTailChunk000Sub001Block013Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block013Part021CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block013Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block013Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block013Part021CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block013Part021SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block013Part021] using hcert

def TailChunk000Sub001Block013Part022SupportExplicit : Finset ℕ :=
  ([8839] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block013Part022 : ℚ :=
  (1220748765625 : ℚ) / 3814019037364427442

def SurrogateDiagonalTailChunk000Sub001Block013Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8839
    = surrogateDiagTailX0RatChunk000Sub001Block013Part022

theorem surrogateDiagonalTailChunk000Sub001Block013Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block013Part022CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block013Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block013Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block013Part022CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block013Part022SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block013Part022] using hcert

def TailChunk000Sub001Block013Part023SupportExplicit : Finset ℕ :=
  ([8841] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block013Part023 : ℚ :=
  (87921696787 : ℚ) / 64537033081651200

def SurrogateDiagonalTailChunk000Sub001Block013Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8841
    = surrogateDiagTailX0RatChunk000Sub001Block013Part023

theorem surrogateDiagonalTailChunk000Sub001Block013Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block013Part023CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block013Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block013Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block013Part023CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block013Part023SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block013Part023] using hcert

def TailChunk000Sub001Block013Part024SupportExplicit : Finset ℕ :=
  ([8842] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block013Part024 : ℚ :=
  (488631025 : ℚ) / 381747259144992

def SurrogateDiagonalTailChunk000Sub001Block013Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8842
    = surrogateDiagTailX0RatChunk000Sub001Block013Part024

theorem surrogateDiagonalTailChunk000Sub001Block013Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block013Part024CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block013Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block013Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block013Part024CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block013Part024SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block013Part024] using hcert

def surrogateDiagonalTailChunk000Sub001Block013HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block013Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block013Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block013Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block013Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block013Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block013Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block013Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block013Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block013Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block013Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block013Head : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block013Part000
    + surrogateDiagTailX0RatChunk000Sub001Block013Part001
    + surrogateDiagTailX0RatChunk000Sub001Block013Part002
    + surrogateDiagTailX0RatChunk000Sub001Block013Part003
    + surrogateDiagTailX0RatChunk000Sub001Block013Part004
    + surrogateDiagTailX0RatChunk000Sub001Block013Part005
    + surrogateDiagTailX0RatChunk000Sub001Block013Part006
    + surrogateDiagTailX0RatChunk000Sub001Block013Part007
    + surrogateDiagTailX0RatChunk000Sub001Block013Part008
    + surrogateDiagTailX0RatChunk000Sub001Block013Part009

def surrogateDiagonalTailChunk000Sub001Block013MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block013Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block013Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block013Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block013Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block013Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block013Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block013Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block013Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block013Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block013Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block013Mid : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block013Part010
    + surrogateDiagTailX0RatChunk000Sub001Block013Part011
    + surrogateDiagTailX0RatChunk000Sub001Block013Part012
    + surrogateDiagTailX0RatChunk000Sub001Block013Part013
    + surrogateDiagTailX0RatChunk000Sub001Block013Part014
    + surrogateDiagTailX0RatChunk000Sub001Block013Part015
    + surrogateDiagTailX0RatChunk000Sub001Block013Part016
    + surrogateDiagTailX0RatChunk000Sub001Block013Part017
    + surrogateDiagTailX0RatChunk000Sub001Block013Part018
    + surrogateDiagTailX0RatChunk000Sub001Block013Part019

def surrogateDiagonalTailChunk000Sub001Block013TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block013Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block013Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block013Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block013Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block013Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block013Tail : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block013Part020
    + surrogateDiagTailX0RatChunk000Sub001Block013Part021
    + surrogateDiagTailX0RatChunk000Sub001Block013Part022
    + surrogateDiagTailX0RatChunk000Sub001Block013Part023
    + surrogateDiagTailX0RatChunk000Sub001Block013Part024

def surrogateDiagonalTailChunk000Sub001Block013Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub001Block013HeadSum X0
    + surrogateDiagonalTailChunk000Sub001Block013MidSum X0
    + surrogateDiagonalTailChunk000Sub001Block013TailSum X0

def surrogateDiagTailX0RatChunk000Sub001Block013 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block013Part000
    + surrogateDiagTailX0RatChunk000Sub001Block013Part001
    + surrogateDiagTailX0RatChunk000Sub001Block013Part002
    + surrogateDiagTailX0RatChunk000Sub001Block013Part003
    + surrogateDiagTailX0RatChunk000Sub001Block013Part004
    + surrogateDiagTailX0RatChunk000Sub001Block013Part005
    + surrogateDiagTailX0RatChunk000Sub001Block013Part006
    + surrogateDiagTailX0RatChunk000Sub001Block013Part007
    + surrogateDiagTailX0RatChunk000Sub001Block013Part008
    + surrogateDiagTailX0RatChunk000Sub001Block013Part009
    + surrogateDiagTailX0RatChunk000Sub001Block013Part010
    + surrogateDiagTailX0RatChunk000Sub001Block013Part011
    + surrogateDiagTailX0RatChunk000Sub001Block013Part012
    + surrogateDiagTailX0RatChunk000Sub001Block013Part013
    + surrogateDiagTailX0RatChunk000Sub001Block013Part014
    + surrogateDiagTailX0RatChunk000Sub001Block013Part015
    + surrogateDiagTailX0RatChunk000Sub001Block013Part016
    + surrogateDiagTailX0RatChunk000Sub001Block013Part017
    + surrogateDiagTailX0RatChunk000Sub001Block013Part018
    + surrogateDiagTailX0RatChunk000Sub001Block013Part019
    + surrogateDiagTailX0RatChunk000Sub001Block013Part020
    + surrogateDiagTailX0RatChunk000Sub001Block013Part021
    + surrogateDiagTailX0RatChunk000Sub001Block013Part022
    + surrogateDiagTailX0RatChunk000Sub001Block013Part023
    + surrogateDiagTailX0RatChunk000Sub001Block013Part024

theorem surrogateDiagTailX0RatChunk000Sub001Block013_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk000Sub001Block013Head + surrogateDiagTailX0RatChunk000Sub001Block013Mid + surrogateDiagTailX0RatChunk000Sub001Block013Tail =
      surrogateDiagTailX0RatChunk000Sub001Block013 := by
  unfold surrogateDiagTailX0RatChunk000Sub001Block013Head surrogateDiagTailX0RatChunk000Sub001Block013Mid surrogateDiagTailX0RatChunk000Sub001Block013Tail surrogateDiagTailX0RatChunk000Sub001Block013
  ring

def SurrogateDiagonalTailChunk000Sub001Block013HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block013HeadSum X0 = surrogateDiagTailX0RatChunk000Sub001Block013Head

def SurrogateDiagonalTailChunk000Sub001Block013MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block013MidSum X0 = surrogateDiagTailX0RatChunk000Sub001Block013Mid

def SurrogateDiagonalTailChunk000Sub001Block013TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block013TailSum X0 = surrogateDiagTailX0RatChunk000Sub001Block013Tail

theorem surrogateDiagonalTailChunk000Sub001Block013_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk000Sub001Block013HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk000Sub001Block013MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk000Sub001Block013TailCertificateAt X0) :
    surrogateDiagonalTailChunk000Sub001Block013Sum X0 = surrogateDiagTailX0RatChunk000Sub001Block013 := by
  unfold SurrogateDiagonalTailChunk000Sub001Block013HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk000Sub001Block013MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk000Sub001Block013TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk000Sub001Block013Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk000Sub001Block013_eq_head_add_mid_add_tail

/-- Block 014 covers tail-support indices [5350,5375) and q from 8843 to 8885. -/

def TailChunk000Sub001Block014Part000SupportExplicit : Finset ℕ :=
  ([8843] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block014Part000 : ℚ :=
  (4667312045125 : ℚ) / 13475493850031474688

def SurrogateDiagonalTailChunk000Sub001Block014Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8843
    = surrogateDiagTailX0RatChunk000Sub001Block014Part000

theorem surrogateDiagonalTailChunk000Sub001Block014Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block014Part000CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block014Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block014Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block014Part000CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block014Part000SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block014Part000] using hcert

def TailChunk000Sub001Block014Part001SupportExplicit : Finset ℕ :=
  ([8845] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block014Part001 : ℚ :=
  (131112306961 : ℚ) / 203968894677811200

def SurrogateDiagonalTailChunk000Sub001Block014Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8845
    = surrogateDiagTailX0RatChunk000Sub001Block014Part001

theorem surrogateDiagonalTailChunk000Sub001Block014Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block014Part001CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block014Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block014Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block014Part001CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block014Part001SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block014Part001] using hcert

def TailChunk000Sub001Block014Part002SupportExplicit : Finset ℕ :=
  ([8846] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block014Part002 : ℚ :=
  (305670765625 : ℚ) / 239024170949544882

def SurrogateDiagonalTailChunk000Sub001Block014Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8846
    = surrogateDiagTailX0RatChunk000Sub001Block014Part002

theorem surrogateDiagonalTailChunk000Sub001Block014Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block014Part002CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block014Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block014Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block014Part002CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block014Part002SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block014Part002] using hcert

def TailChunk000Sub001Block014Part003SupportExplicit : Finset ℕ :=
  ([8849] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block014Part003 : ℚ :=
  (1223512515625 : ℚ) / 3831310266773348352

def SurrogateDiagonalTailChunk000Sub001Block014Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8849
    = surrogateDiagTailX0RatChunk000Sub001Block014Part003

theorem surrogateDiagonalTailChunk000Sub001Block014Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block014Part003CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block014Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block014Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block014Part003CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block014Part003SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block014Part003] using hcert

def TailChunk000Sub001Block014Part004SupportExplicit : Finset ℕ :=
  ([8851] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block014Part004 : ℚ :=
  (4722124742125 : ℚ) / 13882656742422693888

def SurrogateDiagonalTailChunk000Sub001Block014Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8851
    = surrogateDiagTailX0RatChunk000Sub001Block014Part004

theorem surrogateDiagonalTailChunk000Sub001Block014Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block014Part004CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block014Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block014Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block014Part004CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block014Part004SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block014Part004] using hcert

def TailChunk000Sub001Block014Part005SupportExplicit : Finset ℕ :=
  ([8853] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block014Part005 : ℚ :=
  (2427534341725 : ℚ) / 2164240811335385088

def SurrogateDiagonalTailChunk000Sub001Block014Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8853
    = surrogateDiagTailX0RatChunk000Sub001Block014Part005

theorem surrogateDiagonalTailChunk000Sub001Block014Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block014Part005CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block014Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block014Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block014Part005CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block014Part005SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block014Part005] using hcert

def TailChunk000Sub001Block014Part006SupportExplicit : Finset ℕ :=
  ([8854] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block014Part006 : ℚ :=
  (751002857875 : ℚ) / 253482256254468096

def SurrogateDiagonalTailChunk000Sub001Block014Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8854
    = surrogateDiagTailX0RatChunk000Sub001Block014Part006

theorem surrogateDiagonalTailChunk000Sub001Block014Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block014Part006CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block014Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block014Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block014Part006CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block014Part006SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block014Part006] using hcert

def TailChunk000Sub001Block014Part007SupportExplicit : Finset ℕ :=
  ([8855] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block014Part007 : ℚ :=
  (94062502351 : ℚ) / 77736062759731200

def SurrogateDiagonalTailChunk000Sub001Block014Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8855
    = surrogateDiagTailX0RatChunk000Sub001Block014Part007

theorem surrogateDiagonalTailChunk000Sub001Block014Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block014Part007CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block014Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block014Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block014Part007CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block014Part007SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block014Part007] using hcert

def TailChunk000Sub001Block014Part008SupportExplicit : Finset ℕ :=
  ([8857] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block014Part008 : ℚ :=
  (179368471603 : ℚ) / 479269900989235200

def SurrogateDiagonalTailChunk000Sub001Block014Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8857
    = surrogateDiagTailX0RatChunk000Sub001Block014Part008

theorem surrogateDiagonalTailChunk000Sub001Block014Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block014Part008CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block014Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block014Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block014Part008CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block014Part008SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block014Part008] using hcert

def TailChunk000Sub001Block014Part009SupportExplicit : Finset ℕ :=
  ([8858] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block014Part009 : ℚ :=
  (2337253451725 : ℚ) / 842218365626967168

def SurrogateDiagonalTailChunk000Sub001Block014Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8858
    = surrogateDiagTailX0RatChunk000Sub001Block014Part009

theorem surrogateDiagonalTailChunk000Sub001Block014Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block014Part009CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block014Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block014Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block014Part009CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block014Part009SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block014Part009] using hcert

def TailChunk000Sub001Block014Part010SupportExplicit : Finset ℕ :=
  ([8859] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block014Part010 : ℚ :=
  (1362140289425 : ℚ) / 1519085640465137664

def SurrogateDiagonalTailChunk000Sub001Block014Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8859
    = surrogateDiagTailX0RatChunk000Sub001Block014Part010

theorem surrogateDiagonalTailChunk000Sub001Block014Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block014Part010CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block014Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block014Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block014Part010CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block014Part010SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block014Part010] using hcert

def TailChunk000Sub001Block014Part011SupportExplicit : Finset ℕ :=
  ([8861] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block014Part011 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block014Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8861
    = surrogateDiagTailX0RatChunk000Sub001Block014Part011

theorem surrogateDiagonalTailChunk000Sub001Block014Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block014Part011CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block014Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block014Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block014Part011CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block014Part011SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block014Part011] using hcert

def TailChunk000Sub001Block014Part012SupportExplicit : Finset ℕ :=
  ([8862] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block014Part012 : ℚ :=
  (1681 : ℚ) / 237081600

def SurrogateDiagonalTailChunk000Sub001Block014Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8862
    = surrogateDiagTailX0RatChunk000Sub001Block014Part012

theorem surrogateDiagonalTailChunk000Sub001Block014Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block014Part012CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block014Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block014Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block014Part012CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block014Part012SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block014Part012] using hcert

def TailChunk000Sub001Block014Part013SupportExplicit : Finset ℕ :=
  ([8863] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block014Part013 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block014Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8863
    = surrogateDiagTailX0RatChunk000Sub001Block014Part013

theorem surrogateDiagonalTailChunk000Sub001Block014Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block014Part013CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block014Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block014Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block014Part013CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block014Part013SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block014Part013] using hcert

def TailChunk000Sub001Block014Part014SupportExplicit : Finset ℕ :=
  ([8866] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block014Part014 : ℚ :=
  (6830392709 : ℚ) / 2799919872000000

def SurrogateDiagonalTailChunk000Sub001Block014Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8866
    = surrogateDiagTailX0RatChunk000Sub001Block014Part014

theorem surrogateDiagonalTailChunk000Sub001Block014Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block014Part014CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block014Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block014Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block014Part014CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block014Part014SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block014Part014] using hcert

def TailChunk000Sub001Block014Part015SupportExplicit : Finset ℕ :=
  ([8867] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block014Part015 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block014Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8867
    = surrogateDiagTailX0RatChunk000Sub001Block014Part015

theorem surrogateDiagonalTailChunk000Sub001Block014Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block014Part015CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block014Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block014Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block014Part015CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block014Part015SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block014Part015] using hcert

def TailChunk000Sub001Block014Part016SupportExplicit : Finset ℕ :=
  ([8870] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block014Part016 : ℚ :=
  (343917775125 : ℚ) / 131486285602134016

def SurrogateDiagonalTailChunk000Sub001Block014Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8870
    = surrogateDiagTailX0RatChunk000Sub001Block014Part016

theorem surrogateDiagonalTailChunk000Sub001Block014Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block014Part016CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block014Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block014Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block014Part016CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block014Part016SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block014Part016] using hcert

def TailChunk000Sub001Block014Part017SupportExplicit : Finset ℕ :=
  ([8871] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block014Part017 : ℚ :=
  (8542908025 : ℚ) / 47729247403252512

def SurrogateDiagonalTailChunk000Sub001Block014Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8871
    = surrogateDiagTailX0RatChunk000Sub001Block014Part017

theorem surrogateDiagonalTailChunk000Sub001Block014Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block014Part017CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block014Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block014Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block014Part017CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block014Part017SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block014Part017] using hcert

def TailChunk000Sub001Block014Part018SupportExplicit : Finset ℕ :=
  ([8873] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block014Part018 : ℚ :=
  (51539191525 : ℚ) / 4126095648952246656

def SurrogateDiagonalTailChunk000Sub001Block014Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8873
    = surrogateDiagTailX0RatChunk000Sub001Block014Part018

theorem surrogateDiagonalTailChunk000Sub001Block014Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block014Part018CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block014Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block014Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block014Part018CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block014Part018SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block014Part018] using hcert

def TailChunk000Sub001Block014Part019SupportExplicit : Finset ℕ :=
  ([8877] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block014Part019 : ℚ :=
  (21219480749 : ℚ) / 41277749707161600

def SurrogateDiagonalTailChunk000Sub001Block014Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8877
    = surrogateDiagTailX0RatChunk000Sub001Block014Part019

theorem surrogateDiagonalTailChunk000Sub001Block014Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block014Part019CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block014Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block014Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block014Part019CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block014Part019SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block014Part019] using hcert

def TailChunk000Sub001Block014Part020SupportExplicit : Finset ℕ :=
  ([8878] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block014Part020 : ℚ :=
  (1179799303975 : ℚ) / 796017282659647488

def SurrogateDiagonalTailChunk000Sub001Block014Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8878
    = surrogateDiagTailX0RatChunk000Sub001Block014Part020

theorem surrogateDiagonalTailChunk000Sub001Block014Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block014Part020CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block014Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block014Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block014Part020CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block014Part020SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block014Part020] using hcert

def TailChunk000Sub001Block014Part021SupportExplicit : Finset ℕ :=
  ([8879] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block014Part021 : ℚ :=
  (3136364525 : ℚ) / 169959484886197248

def SurrogateDiagonalTailChunk000Sub001Block014Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8879
    = surrogateDiagTailX0RatChunk000Sub001Block014Part021

theorem surrogateDiagonalTailChunk000Sub001Block014Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block014Part021CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block014Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block014Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block014Part021CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block014Part021SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block014Part021] using hcert

def TailChunk000Sub001Block014Part022SupportExplicit : Finset ℕ :=
  ([8881] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block014Part022 : ℚ :=
  (58224829525 : ℚ) / 14272686594391813248

def SurrogateDiagonalTailChunk000Sub001Block014Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8881
    = surrogateDiagTailX0RatChunk000Sub001Block014Part022

theorem surrogateDiagonalTailChunk000Sub001Block014Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block014Part022CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block014Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block014Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block014Part022CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block014Part022SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block014Part022] using hcert

def TailChunk000Sub001Block014Part023SupportExplicit : Finset ℕ :=
  ([8882] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block014Part023 : ℚ :=
  (493062025 : ℚ) / 388703750164992

def SurrogateDiagonalTailChunk000Sub001Block014Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8882
    = surrogateDiagTailX0RatChunk000Sub001Block014Part023

theorem surrogateDiagonalTailChunk000Sub001Block014Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block014Part023CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block014Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block014Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block014Part023CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block014Part023SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block014Part023] using hcert

def TailChunk000Sub001Block014Part024SupportExplicit : Finset ℕ :=
  ([8885] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block014Part024 : ℚ :=
  (296210783225 : ℚ) / 3184261121351614464

def SurrogateDiagonalTailChunk000Sub001Block014Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8885
    = surrogateDiagTailX0RatChunk000Sub001Block014Part024

theorem surrogateDiagonalTailChunk000Sub001Block014Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block014Part024CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block014Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block014Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block014Part024CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block014Part024SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block014Part024] using hcert

def surrogateDiagonalTailChunk000Sub001Block014HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block014Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block014Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block014Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block014Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block014Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block014Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block014Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block014Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block014Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block014Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block014Head : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block014Part000
    + surrogateDiagTailX0RatChunk000Sub001Block014Part001
    + surrogateDiagTailX0RatChunk000Sub001Block014Part002
    + surrogateDiagTailX0RatChunk000Sub001Block014Part003
    + surrogateDiagTailX0RatChunk000Sub001Block014Part004
    + surrogateDiagTailX0RatChunk000Sub001Block014Part005
    + surrogateDiagTailX0RatChunk000Sub001Block014Part006
    + surrogateDiagTailX0RatChunk000Sub001Block014Part007
    + surrogateDiagTailX0RatChunk000Sub001Block014Part008
    + surrogateDiagTailX0RatChunk000Sub001Block014Part009

def surrogateDiagonalTailChunk000Sub001Block014MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block014Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block014Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block014Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block014Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block014Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block014Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block014Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block014Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block014Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block014Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block014Mid : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block014Part010
    + surrogateDiagTailX0RatChunk000Sub001Block014Part011
    + surrogateDiagTailX0RatChunk000Sub001Block014Part012
    + surrogateDiagTailX0RatChunk000Sub001Block014Part013
    + surrogateDiagTailX0RatChunk000Sub001Block014Part014
    + surrogateDiagTailX0RatChunk000Sub001Block014Part015
    + surrogateDiagTailX0RatChunk000Sub001Block014Part016
    + surrogateDiagTailX0RatChunk000Sub001Block014Part017
    + surrogateDiagTailX0RatChunk000Sub001Block014Part018
    + surrogateDiagTailX0RatChunk000Sub001Block014Part019

def surrogateDiagonalTailChunk000Sub001Block014TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block014Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block014Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block014Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block014Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block014Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block014Tail : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block014Part020
    + surrogateDiagTailX0RatChunk000Sub001Block014Part021
    + surrogateDiagTailX0RatChunk000Sub001Block014Part022
    + surrogateDiagTailX0RatChunk000Sub001Block014Part023
    + surrogateDiagTailX0RatChunk000Sub001Block014Part024

def surrogateDiagonalTailChunk000Sub001Block014Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub001Block014HeadSum X0
    + surrogateDiagonalTailChunk000Sub001Block014MidSum X0
    + surrogateDiagonalTailChunk000Sub001Block014TailSum X0

def surrogateDiagTailX0RatChunk000Sub001Block014 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block014Part000
    + surrogateDiagTailX0RatChunk000Sub001Block014Part001
    + surrogateDiagTailX0RatChunk000Sub001Block014Part002
    + surrogateDiagTailX0RatChunk000Sub001Block014Part003
    + surrogateDiagTailX0RatChunk000Sub001Block014Part004
    + surrogateDiagTailX0RatChunk000Sub001Block014Part005
    + surrogateDiagTailX0RatChunk000Sub001Block014Part006
    + surrogateDiagTailX0RatChunk000Sub001Block014Part007
    + surrogateDiagTailX0RatChunk000Sub001Block014Part008
    + surrogateDiagTailX0RatChunk000Sub001Block014Part009
    + surrogateDiagTailX0RatChunk000Sub001Block014Part010
    + surrogateDiagTailX0RatChunk000Sub001Block014Part011
    + surrogateDiagTailX0RatChunk000Sub001Block014Part012
    + surrogateDiagTailX0RatChunk000Sub001Block014Part013
    + surrogateDiagTailX0RatChunk000Sub001Block014Part014
    + surrogateDiagTailX0RatChunk000Sub001Block014Part015
    + surrogateDiagTailX0RatChunk000Sub001Block014Part016
    + surrogateDiagTailX0RatChunk000Sub001Block014Part017
    + surrogateDiagTailX0RatChunk000Sub001Block014Part018
    + surrogateDiagTailX0RatChunk000Sub001Block014Part019
    + surrogateDiagTailX0RatChunk000Sub001Block014Part020
    + surrogateDiagTailX0RatChunk000Sub001Block014Part021
    + surrogateDiagTailX0RatChunk000Sub001Block014Part022
    + surrogateDiagTailX0RatChunk000Sub001Block014Part023
    + surrogateDiagTailX0RatChunk000Sub001Block014Part024

theorem surrogateDiagTailX0RatChunk000Sub001Block014_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk000Sub001Block014Head + surrogateDiagTailX0RatChunk000Sub001Block014Mid + surrogateDiagTailX0RatChunk000Sub001Block014Tail =
      surrogateDiagTailX0RatChunk000Sub001Block014 := by
  unfold surrogateDiagTailX0RatChunk000Sub001Block014Head surrogateDiagTailX0RatChunk000Sub001Block014Mid surrogateDiagTailX0RatChunk000Sub001Block014Tail surrogateDiagTailX0RatChunk000Sub001Block014
  ring

def SurrogateDiagonalTailChunk000Sub001Block014HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block014HeadSum X0 = surrogateDiagTailX0RatChunk000Sub001Block014Head

def SurrogateDiagonalTailChunk000Sub001Block014MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block014MidSum X0 = surrogateDiagTailX0RatChunk000Sub001Block014Mid

def SurrogateDiagonalTailChunk000Sub001Block014TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block014TailSum X0 = surrogateDiagTailX0RatChunk000Sub001Block014Tail

theorem surrogateDiagonalTailChunk000Sub001Block014_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk000Sub001Block014HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk000Sub001Block014MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk000Sub001Block014TailCertificateAt X0) :
    surrogateDiagonalTailChunk000Sub001Block014Sum X0 = surrogateDiagTailX0RatChunk000Sub001Block014 := by
  unfold SurrogateDiagonalTailChunk000Sub001Block014HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk000Sub001Block014MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk000Sub001Block014TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk000Sub001Block014Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk000Sub001Block014_eq_head_add_mid_add_tail

/-- Block 015 covers tail-support indices [5375,5400) and q from 8886 to 8923. -/

def TailChunk000Sub001Block015Part000SupportExplicit : Finset ℕ :=
  ([8886] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block015Part000 : ℚ :=
  (3288099 : ℚ) / 767656345600

def SurrogateDiagonalTailChunk000Sub001Block015Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8886
    = surrogateDiagTailX0RatChunk000Sub001Block015Part000

theorem surrogateDiagonalTailChunk000Sub001Block015Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block015Part000CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block015Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block015Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block015Part000CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block015Part000SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block015Part000] using hcert

def TailChunk000Sub001Block015Part001SupportExplicit : Finset ℕ :=
  ([8887] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block015Part001 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block015Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8887
    = surrogateDiagTailX0RatChunk000Sub001Block015Part001

theorem surrogateDiagonalTailChunk000Sub001Block015Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block015Part001CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block015Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block015Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block015Part001CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block015Part001SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block015Part001] using hcert

def TailChunk000Sub001Block015Part002SupportExplicit : Finset ℕ :=
  ([8889] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block015Part002 : ℚ :=
  (548542996325 : ℚ) / 1539774285701204544

def SurrogateDiagonalTailChunk000Sub001Block015Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8889
    = surrogateDiagTailX0RatChunk000Sub001Block015Part002

theorem surrogateDiagonalTailChunk000Sub001Block015Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block015Part002CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block015Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block015Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block015Part002CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block015Part002SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block015Part002] using hcert

def TailChunk000Sub001Block015Part003SupportExplicit : Finset ℕ :=
  ([8890] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block015Part003 : ℚ :=
  (894686612125 : ℚ) / 209099987184549888

def SurrogateDiagonalTailChunk000Sub001Block015Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8890
    = surrogateDiagTailX0RatChunk000Sub001Block015Part003

theorem surrogateDiagonalTailChunk000Sub001Block015Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block015Part003CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block015Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block015Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block015Part003CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block015Part003SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block015Part003] using hcert

def TailChunk000Sub001Block015Part004SupportExplicit : Finset ℕ :=
  ([8891] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block015Part004 : ℚ :=
  (5852775325 : ℚ) / 450635122230165504

def SurrogateDiagonalTailChunk000Sub001Block015Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8891
    = surrogateDiagTailX0RatChunk000Sub001Block015Part004

theorem surrogateDiagonalTailChunk000Sub001Block015Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block015Part004CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block015Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block015Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block015Part004CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block015Part004SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block015Part004] using hcert

def TailChunk000Sub001Block015Part005SupportExplicit : Finset ℕ :=
  ([8893] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block015Part005 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block015Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8893
    = surrogateDiagTailX0RatChunk000Sub001Block015Part005

theorem surrogateDiagonalTailChunk000Sub001Block015Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block015Part005CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block015Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block015Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block015Part005CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block015Part005SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block015Part005] using hcert

def TailChunk000Sub001Block015Part006SupportExplicit : Finset ℕ :=
  ([8894] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block015Part006 : ℚ :=
  (308997015625 : ℚ) / 244255696465428882

def SurrogateDiagonalTailChunk000Sub001Block015Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8894
    = surrogateDiagTailX0RatChunk000Sub001Block015Part006

theorem surrogateDiagonalTailChunk000Sub001Block015Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block015Part006CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block015Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block015Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block015Part006CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block015Part006SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block015Part006] using hcert

def TailChunk000Sub001Block015Part007SupportExplicit : Finset ℕ :=
  ([8895] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block015Part007 : ℚ :=
  (322062165075 : ℚ) / 419326567420788736

def SurrogateDiagonalTailChunk000Sub001Block015Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8895
    = surrogateDiagTailX0RatChunk000Sub001Block015Part007

theorem surrogateDiagonalTailChunk000Sub001Block015Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block015Part007CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block015Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block015Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block015Part007CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block015Part007SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block015Part007] using hcert

def TailChunk000Sub001Block015Part008SupportExplicit : Finset ℕ :=
  ([8897] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block015Part008 : ℚ :=
  (2434857101 : ℚ) / 33599038464000000

def SurrogateDiagonalTailChunk000Sub001Block015Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8897
    = surrogateDiagTailX0RatChunk000Sub001Block015Part008

theorem surrogateDiagonalTailChunk000Sub001Block015Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block015Part008CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block015Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block015Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block015Part008CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block015Part008SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block015Part008] using hcert

def TailChunk000Sub001Block015Part009SupportExplicit : Finset ℕ :=
  ([8898] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block015Part009 : ℚ :=
  (27474875 : ℚ) / 6431785483968

def SurrogateDiagonalTailChunk000Sub001Block015Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8898
    = surrogateDiagTailX0RatChunk000Sub001Block015Part009

theorem surrogateDiagonalTailChunk000Sub001Block015Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block015Part009CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block015Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block015Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block015Part009CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block015Part009SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block015Part009] using hcert

def TailChunk000Sub001Block015Part010SupportExplicit : Finset ℕ :=
  ([8899] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block015Part010 : ℚ :=
  (990824353 : ℚ) / 42631664877649920

def SurrogateDiagonalTailChunk000Sub001Block015Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8899
    = surrogateDiagTailX0RatChunk000Sub001Block015Part010

theorem surrogateDiagonalTailChunk000Sub001Block015Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block015Part010CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block015Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block015Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block015Part010CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block015Part010SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block015Part010] using hcert

def TailChunk000Sub001Block015Part011SupportExplicit : Finset ℕ :=
  ([8902] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block015Part011 : ℚ :=
  (19811401 : ℚ) / 15688697362050

def SurrogateDiagonalTailChunk000Sub001Block015Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8902
    = surrogateDiagTailX0RatChunk000Sub001Block015Part011

theorem surrogateDiagonalTailChunk000Sub001Block015Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block015Part011CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block015Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block015Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block015Part011CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block015Part011SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block015Part011] using hcert

def TailChunk000Sub001Block015Part012SupportExplicit : Finset ℕ :=
  ([8903] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block015Part012 : ℚ :=
  (2430601975 : ℚ) / 320845091667416064

def SurrogateDiagonalTailChunk000Sub001Block015Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8903
    = surrogateDiagTailX0RatChunk000Sub001Block015Part012

theorem surrogateDiagonalTailChunk000Sub001Block015Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block015Part012CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block015Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block015Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block015Part012CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block015Part012SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block015Part012] using hcert

def TailChunk000Sub001Block015Part013SupportExplicit : Finset ℕ :=
  ([8905] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block015Part013 : ℚ :=
  (692119322575 : ℚ) / 4540957548324323328

def SurrogateDiagonalTailChunk000Sub001Block015Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8905
    = surrogateDiagTailX0RatChunk000Sub001Block015Part013

theorem surrogateDiagonalTailChunk000Sub001Block015Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block015Part013CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block015Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block015Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block015Part013CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block015Part013SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block015Part013] using hcert

def TailChunk000Sub001Block015Part014SupportExplicit : Finset ℕ :=
  ([8906] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block015Part014 : ℚ :=
  (24137486009 : ℚ) / 17417741539737600

def SurrogateDiagonalTailChunk000Sub001Block015Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8906
    = surrogateDiagTailX0RatChunk000Sub001Block015Part014

theorem surrogateDiagonalTailChunk000Sub001Block015Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block015Part014CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block015Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block015Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block015Part014CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block015Part014SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block015Part014] using hcert

def TailChunk000Sub001Block015Part015SupportExplicit : Finset ℕ :=
  ([8907] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block015Part015 : ℚ :=
  (550766301275 : ℚ) / 1552288472266850304

def SurrogateDiagonalTailChunk000Sub001Block015Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8907
    = surrogateDiagTailX0RatChunk000Sub001Block015Part015

theorem surrogateDiagonalTailChunk000Sub001Block015Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block015Part015CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block015Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block015Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block015Part015CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block015Part015SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block015Part015] using hcert

def TailChunk000Sub001Block015Part016SupportExplicit : Finset ℕ :=
  ([8909] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block015Part016 : ℚ :=
  (2571339157 : ℚ) / 573012189522000000

def SurrogateDiagonalTailChunk000Sub001Block015Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8909
    = surrogateDiagTailX0RatChunk000Sub001Block015Part016

theorem surrogateDiagonalTailChunk000Sub001Block015Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block015Part016CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block015Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block015Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block015Part016CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block015Part016SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block015Part016] using hcert

def TailChunk000Sub001Block015Part017SupportExplicit : Finset ℕ :=
  ([8911] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block015Part017 : ℚ :=
  (1034087575 : ℚ) / 13336819127419392

def SurrogateDiagonalTailChunk000Sub001Block015Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8911
    = surrogateDiagTailX0RatChunk000Sub001Block015Part017

theorem surrogateDiagonalTailChunk000Sub001Block015Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block015Part017CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block015Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block015Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block015Part017CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block015Part017SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block015Part017] using hcert

def TailChunk000Sub001Block015Part018SupportExplicit : Finset ℕ :=
  ([8913] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block015Part018 : ℚ :=
  (2207725453 : ℚ) / 12451814154457920

def SurrogateDiagonalTailChunk000Sub001Block015Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8913
    = surrogateDiagTailX0RatChunk000Sub001Block015Part018

theorem surrogateDiagonalTailChunk000Sub001Block015Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block015Part018CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block015Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block015Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block015Part018CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block015Part018SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block015Part018] using hcert

def TailChunk000Sub001Block015Part019SupportExplicit : Finset ℕ :=
  ([8914] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block015Part019 : ℚ :=
  (310388265625 : ℚ) / 246460653796864512

def SurrogateDiagonalTailChunk000Sub001Block015Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8914
    = surrogateDiagTailX0RatChunk000Sub001Block015Part019

theorem surrogateDiagonalTailChunk000Sub001Block015Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block015Part019CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block015Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block015Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block015Part019CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block015Part019SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block015Part019] using hcert

def TailChunk000Sub001Block015Part020SupportExplicit : Finset ℕ :=
  ([8915] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block015Part020 : ℚ :=
  (74552839025 : ℚ) / 806877557208873216

def SurrogateDiagonalTailChunk000Sub001Block015Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8915
    = surrogateDiagTailX0RatChunk000Sub001Block015Part020

theorem surrogateDiagonalTailChunk000Sub001Block015Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block015Part020CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block015Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block015Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block015Part020CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block015Part020SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block015Part020] using hcert

def TailChunk000Sub001Block015Part021SupportExplicit : Finset ℕ :=
  ([8917] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block015Part021 : ℚ :=
  (38460341 : ℚ) / 6192974769684480

def SurrogateDiagonalTailChunk000Sub001Block015Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8917
    = surrogateDiagTailX0RatChunk000Sub001Block015Part021

theorem surrogateDiagonalTailChunk000Sub001Block015Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block015Part021CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block015Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block015Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block015Part021CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block015Part021SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block015Part021] using hcert

def TailChunk000Sub001Block015Part022SupportExplicit : Finset ℕ :=
  ([8921] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block015Part022 : ℚ :=
  (995673487 : ℚ) / 43055330344200000

def SurrogateDiagonalTailChunk000Sub001Block015Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8921
    = surrogateDiagTailX0RatChunk000Sub001Block015Part022

theorem surrogateDiagonalTailChunk000Sub001Block015Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block015Part022CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block015Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block015Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block015Part022CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block015Part022SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block015Part022] using hcert

def TailChunk000Sub001Block015Part023SupportExplicit : Finset ℕ :=
  ([8922] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block015Part023 : ℚ :=
  (82869825 : ℚ) / 19504518297664

def SurrogateDiagonalTailChunk000Sub001Block015Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8922
    = surrogateDiagTailX0RatChunk000Sub001Block015Part023

theorem surrogateDiagonalTailChunk000Sub001Block015Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block015Part023CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block015Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block015Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block015Part023CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block015Part023SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block015Part023] using hcert

def TailChunk000Sub001Block015Part024SupportExplicit : Finset ℕ :=
  ([8923] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block015Part024 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block015Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8923
    = surrogateDiagTailX0RatChunk000Sub001Block015Part024

theorem surrogateDiagonalTailChunk000Sub001Block015Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block015Part024CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block015Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block015Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block015Part024CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block015Part024SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block015Part024] using hcert

def surrogateDiagonalTailChunk000Sub001Block015HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block015Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block015Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block015Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block015Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block015Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block015Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block015Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block015Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block015Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block015Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block015Head : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block015Part000
    + surrogateDiagTailX0RatChunk000Sub001Block015Part001
    + surrogateDiagTailX0RatChunk000Sub001Block015Part002
    + surrogateDiagTailX0RatChunk000Sub001Block015Part003
    + surrogateDiagTailX0RatChunk000Sub001Block015Part004
    + surrogateDiagTailX0RatChunk000Sub001Block015Part005
    + surrogateDiagTailX0RatChunk000Sub001Block015Part006
    + surrogateDiagTailX0RatChunk000Sub001Block015Part007
    + surrogateDiagTailX0RatChunk000Sub001Block015Part008
    + surrogateDiagTailX0RatChunk000Sub001Block015Part009

def surrogateDiagonalTailChunk000Sub001Block015MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block015Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block015Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block015Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block015Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block015Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block015Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block015Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block015Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block015Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block015Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block015Mid : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block015Part010
    + surrogateDiagTailX0RatChunk000Sub001Block015Part011
    + surrogateDiagTailX0RatChunk000Sub001Block015Part012
    + surrogateDiagTailX0RatChunk000Sub001Block015Part013
    + surrogateDiagTailX0RatChunk000Sub001Block015Part014
    + surrogateDiagTailX0RatChunk000Sub001Block015Part015
    + surrogateDiagTailX0RatChunk000Sub001Block015Part016
    + surrogateDiagTailX0RatChunk000Sub001Block015Part017
    + surrogateDiagTailX0RatChunk000Sub001Block015Part018
    + surrogateDiagTailX0RatChunk000Sub001Block015Part019

def surrogateDiagonalTailChunk000Sub001Block015TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block015Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block015Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block015Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block015Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block015Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block015Tail : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block015Part020
    + surrogateDiagTailX0RatChunk000Sub001Block015Part021
    + surrogateDiagTailX0RatChunk000Sub001Block015Part022
    + surrogateDiagTailX0RatChunk000Sub001Block015Part023
    + surrogateDiagTailX0RatChunk000Sub001Block015Part024

def surrogateDiagonalTailChunk000Sub001Block015Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub001Block015HeadSum X0
    + surrogateDiagonalTailChunk000Sub001Block015MidSum X0
    + surrogateDiagonalTailChunk000Sub001Block015TailSum X0

def surrogateDiagTailX0RatChunk000Sub001Block015 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block015Part000
    + surrogateDiagTailX0RatChunk000Sub001Block015Part001
    + surrogateDiagTailX0RatChunk000Sub001Block015Part002
    + surrogateDiagTailX0RatChunk000Sub001Block015Part003
    + surrogateDiagTailX0RatChunk000Sub001Block015Part004
    + surrogateDiagTailX0RatChunk000Sub001Block015Part005
    + surrogateDiagTailX0RatChunk000Sub001Block015Part006
    + surrogateDiagTailX0RatChunk000Sub001Block015Part007
    + surrogateDiagTailX0RatChunk000Sub001Block015Part008
    + surrogateDiagTailX0RatChunk000Sub001Block015Part009
    + surrogateDiagTailX0RatChunk000Sub001Block015Part010
    + surrogateDiagTailX0RatChunk000Sub001Block015Part011
    + surrogateDiagTailX0RatChunk000Sub001Block015Part012
    + surrogateDiagTailX0RatChunk000Sub001Block015Part013
    + surrogateDiagTailX0RatChunk000Sub001Block015Part014
    + surrogateDiagTailX0RatChunk000Sub001Block015Part015
    + surrogateDiagTailX0RatChunk000Sub001Block015Part016
    + surrogateDiagTailX0RatChunk000Sub001Block015Part017
    + surrogateDiagTailX0RatChunk000Sub001Block015Part018
    + surrogateDiagTailX0RatChunk000Sub001Block015Part019
    + surrogateDiagTailX0RatChunk000Sub001Block015Part020
    + surrogateDiagTailX0RatChunk000Sub001Block015Part021
    + surrogateDiagTailX0RatChunk000Sub001Block015Part022
    + surrogateDiagTailX0RatChunk000Sub001Block015Part023
    + surrogateDiagTailX0RatChunk000Sub001Block015Part024

theorem surrogateDiagTailX0RatChunk000Sub001Block015_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk000Sub001Block015Head + surrogateDiagTailX0RatChunk000Sub001Block015Mid + surrogateDiagTailX0RatChunk000Sub001Block015Tail =
      surrogateDiagTailX0RatChunk000Sub001Block015 := by
  unfold surrogateDiagTailX0RatChunk000Sub001Block015Head surrogateDiagTailX0RatChunk000Sub001Block015Mid surrogateDiagTailX0RatChunk000Sub001Block015Tail surrogateDiagTailX0RatChunk000Sub001Block015
  ring

def SurrogateDiagonalTailChunk000Sub001Block015HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block015HeadSum X0 = surrogateDiagTailX0RatChunk000Sub001Block015Head

def SurrogateDiagonalTailChunk000Sub001Block015MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block015MidSum X0 = surrogateDiagTailX0RatChunk000Sub001Block015Mid

def SurrogateDiagonalTailChunk000Sub001Block015TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block015TailSum X0 = surrogateDiagTailX0RatChunk000Sub001Block015Tail

theorem surrogateDiagonalTailChunk000Sub001Block015_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk000Sub001Block015HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk000Sub001Block015MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk000Sub001Block015TailCertificateAt X0) :
    surrogateDiagonalTailChunk000Sub001Block015Sum X0 = surrogateDiagTailX0RatChunk000Sub001Block015 := by
  unfold SurrogateDiagonalTailChunk000Sub001Block015HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk000Sub001Block015MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk000Sub001Block015TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk000Sub001Block015Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk000Sub001Block015_eq_head_add_mid_add_tail

/-- Block 016 covers tail-support indices [5400,5425) and q from 8926 to 8969. -/

def TailChunk000Sub001Block016Part000SupportExplicit : Finset ℕ :=
  ([8926] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block016Part000 : ℚ :=
  (311224515625 : ℚ) / 247790773488258642

def SurrogateDiagonalTailChunk000Sub001Block016Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8926
    = surrogateDiagTailX0RatChunk000Sub001Block016Part000

theorem surrogateDiagonalTailChunk000Sub001Block016Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block016Part000CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block016Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block016Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block016Part000CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block016Part000SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block016Part000] using hcert

def TailChunk000Sub001Block016Part001SupportExplicit : Finset ℕ :=
  ([8927] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block016Part001 : ℚ :=
  (26116975 : ℚ) / 6421467814035456

def SurrogateDiagonalTailChunk000Sub001Block016Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8927
    = surrogateDiagTailX0RatChunk000Sub001Block016Part001

theorem surrogateDiagonalTailChunk000Sub001Block016Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block016Part001CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block016Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block016Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block016Part001CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block016Part001SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block016Part001] using hcert

def TailChunk000Sub001Block016Part002SupportExplicit : Finset ℕ :=
  ([8929] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block016Part002 : ℚ :=
  (1245735015625 : ℚ) / 3971765452967903232

def SurrogateDiagonalTailChunk000Sub001Block016Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8929
    = surrogateDiagTailX0RatChunk000Sub001Block016Part002

theorem surrogateDiagonalTailChunk000Sub001Block016Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block016Part002CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block016Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block016Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block016Part002CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block016Part002SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block016Part002] using hcert

def TailChunk000Sub001Block016Part003SupportExplicit : Finset ℕ :=
  ([8930] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block016Part003 : ℚ :=
  (807593738375 : ℚ) / 150438216364867584

def SurrogateDiagonalTailChunk000Sub001Block016Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8930
    = surrogateDiagTailX0RatChunk000Sub001Block016Part003

theorem surrogateDiagonalTailChunk000Sub001Block016Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block016Part003CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block016Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block016Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block016Part003CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block016Part003SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block016Part003] using hcert

def TailChunk000Sub001Block016Part004SupportExplicit : Finset ℕ :=
  ([8931] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block016Part004 : ℚ :=
  (68898759725 : ℚ) / 62274279703707648

def SurrogateDiagonalTailChunk000Sub001Block016Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8931
    = surrogateDiagTailX0RatChunk000Sub001Block016Part004

theorem surrogateDiagonalTailChunk000Sub001Block016Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block016Part004CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block016Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block016Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block016Part004CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block016Part004SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block016Part004] using hcert

def TailChunk000Sub001Block016Part005SupportExplicit : Finset ℕ :=
  ([8933] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block016Part005 : ℚ :=
  (1246851390625 : ℚ) / 3978888097139088672

def SurrogateDiagonalTailChunk000Sub001Block016Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8933
    = surrogateDiagTailX0RatChunk000Sub001Block016Part005

theorem surrogateDiagonalTailChunk000Sub001Block016Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block016Part005CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block016Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block016Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block016Part005CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block016Part005SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block016Part005] using hcert

def TailChunk000Sub001Block016Part006SupportExplicit : Finset ℕ :=
  ([8934] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block016Part006 : ℚ :=
  (692315268425 : ℚ) / 98068282789330944

def SurrogateDiagonalTailChunk000Sub001Block016Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8934
    = surrogateDiagTailX0RatChunk000Sub001Block016Part006

theorem surrogateDiagonalTailChunk000Sub001Block016Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block016Part006CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block016Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block016Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block016Part006CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block016Part006SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block016Part006] using hcert

def TailChunk000Sub001Block016Part007SupportExplicit : Finset ℕ :=
  ([8935] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block016Part007 : ℚ :=
  (1196776339275 : ℚ) / 2171057809348335616

def SurrogateDiagonalTailChunk000Sub001Block016Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8935
    = surrogateDiagTailX0RatChunk000Sub001Block016Part007

theorem surrogateDiagonalTailChunk000Sub001Block016Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block016Part007CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block016Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block016Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block016Part007CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block016Part007SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block016Part007] using hcert

def TailChunk000Sub001Block016Part008SupportExplicit : Finset ℕ :=
  ([8938] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block016Part008 : ℚ :=
  (95098449961 : ℚ) / 34835483079475200

def SurrogateDiagonalTailChunk000Sub001Block016Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8938
    = surrogateDiagTailX0RatChunk000Sub001Block016Part008

theorem surrogateDiagonalTailChunk000Sub001Block016Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block016Part008CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block016Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block016Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block016Part008CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block016Part008SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block016Part008] using hcert

def TailChunk000Sub001Block016Part009SupportExplicit : Finset ℕ :=
  ([8939] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block016Part009 : ℚ :=
  (220620075875 : ℚ) / 477267710110811136

def SurrogateDiagonalTailChunk000Sub001Block016Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8939
    = surrogateDiagTailX0RatChunk000Sub001Block016Part009

theorem surrogateDiagonalTailChunk000Sub001Block016Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block016Part009CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block016Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block016Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block016Part009CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block016Part009SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block016Part009] using hcert

def TailChunk000Sub001Block016Part010SupportExplicit : Finset ℕ :=
  ([8941] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block016Part010 : ℚ :=
  (1998537025 : ℚ) / 6389059393327392

def SurrogateDiagonalTailChunk000Sub001Block016Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8941
    = surrogateDiagTailX0RatChunk000Sub001Block016Part010

theorem surrogateDiagonalTailChunk000Sub001Block016Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block016Part010CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block016Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block016Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block016Part010CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block016Part010SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block016Part010] using hcert

def TailChunk000Sub001Block016Part011SupportExplicit : Finset ℕ :=
  ([8942] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block016Part011 : ℚ :=
  (295185561325 : ℚ) / 193042068920205312

def SurrogateDiagonalTailChunk000Sub001Block016Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8942
    = surrogateDiagTailX0RatChunk000Sub001Block016Part011

theorem surrogateDiagonalTailChunk000Sub001Block016Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block016Part011CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block016Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block016Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block016Part011CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block016Part011SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block016Part011] using hcert

def TailChunk000Sub001Block016Part012SupportExplicit : Finset ℕ :=
  ([8943] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block016Part012 : ℚ :=
  (1078209937 : ℚ) / 944972956800000

def SurrogateDiagonalTailChunk000Sub001Block016Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8943
    = surrogateDiagTailX0RatChunk000Sub001Block016Part012

theorem surrogateDiagonalTailChunk000Sub001Block016Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block016Part012CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block016Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block016Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block016Part012CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block016Part012SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block016Part012] using hcert

def TailChunk000Sub001Block016Part013SupportExplicit : Finset ℕ :=
  ([8945] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block016Part013 : ℚ :=
  (3598371768925 : ℚ) / 6542396818767249408

def SurrogateDiagonalTailChunk000Sub001Block016Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8945
    = surrogateDiagTailX0RatChunk000Sub001Block016Part013

theorem surrogateDiagonalTailChunk000Sub001Block016Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block016Part013CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block016Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block016Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block016Part013CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block016Part013SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block016Part013] using hcert

def TailChunk000Sub001Block016Part014SupportExplicit : Finset ℕ :=
  ([8947] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block016Part014 : ℚ :=
  (779073477375 : ℚ) / 2212550714985171968

def SurrogateDiagonalTailChunk000Sub001Block016Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8947
    = surrogateDiagTailX0RatChunk000Sub001Block016Part014

theorem surrogateDiagonalTailChunk000Sub001Block016Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block016Part014CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block016Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block016Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block016Part014CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block016Part014SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block016Part014] using hcert

def TailChunk000Sub001Block016Part015SupportExplicit : Finset ℕ :=
  ([8949] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block016Part015 : ℚ :=
  (2566853734675 : ℚ) / 2487340580582227968

def SurrogateDiagonalTailChunk000Sub001Block016Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8949
    = surrogateDiagTailX0RatChunk000Sub001Block016Part015

theorem surrogateDiagonalTailChunk000Sub001Block016Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block016Part015CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block016Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block016Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block016Part015CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block016Part015SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block016Part015] using hcert

def TailChunk000Sub001Block016Part016SupportExplicit : Finset ℕ :=
  ([8951] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block016Part016 : ℚ :=
  (80120401 : ℚ) / 256707751534050

def SurrogateDiagonalTailChunk000Sub001Block016Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8951
    = surrogateDiagTailX0RatChunk000Sub001Block016Part016

theorem surrogateDiagonalTailChunk000Sub001Block016Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block016Part016CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block016Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block016Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block016Part016CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block016Part016SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block016Part016] using hcert

def TailChunk000Sub001Block016Part017SupportExplicit : Finset ℕ :=
  ([8953] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block016Part017 : ℚ :=
  (221311890575 : ℚ) / 480267026636567616

def SurrogateDiagonalTailChunk000Sub001Block016Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8953
    = surrogateDiagTailX0RatChunk000Sub001Block016Part017

theorem surrogateDiagonalTailChunk000Sub001Block016Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block016Part017CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block016Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block016Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block016Part017CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block016Part017SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block016Part017] using hcert

def TailChunk000Sub001Block016Part018SupportExplicit : Finset ℕ :=
  ([8958] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block016Part018 : ℚ :=
  (974694729925 : ℚ) / 198254080171296768

def SurrogateDiagonalTailChunk000Sub001Block016Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8958
    = surrogateDiagTailX0RatChunk000Sub001Block016Part018

theorem surrogateDiagonalTailChunk000Sub001Block016Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block016Part018CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block016Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block016Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block016Part018CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block016Part018SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block016Part018] using hcert

def TailChunk000Sub001Block016Part019SupportExplicit : Finset ℕ :=
  ([8961] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block016Part019 : ℚ :=
  (1312862054675 : ℚ) / 1330912972842614784

def SurrogateDiagonalTailChunk000Sub001Block016Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8961
    = surrogateDiagTailX0RatChunk000Sub001Block016Part019

theorem surrogateDiagonalTailChunk000Sub001Block016Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block016Part019CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block016Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block016Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block016Part019CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block016Part019SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block016Part019] using hcert

def TailChunk000Sub001Block016Part020SupportExplicit : Finset ℕ :=
  ([8962] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block016Part020 : ℚ :=
  (501984025 : ℚ) / 402901520351232

def SurrogateDiagonalTailChunk000Sub001Block016Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8962
    = surrogateDiagTailX0RatChunk000Sub001Block016Part020

theorem surrogateDiagonalTailChunk000Sub001Block016Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block016Part020CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block016Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block016Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block016Part020CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block016Part020SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block016Part020] using hcert

def TailChunk000Sub001Block016Part021SupportExplicit : Finset ℕ :=
  ([8963] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block016Part021 : ℚ :=
  (1255240140625 : ℚ) / 4032613743159546642

def SurrogateDiagonalTailChunk000Sub001Block016Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8963
    = surrogateDiagTailX0RatChunk000Sub001Block016Part021

theorem surrogateDiagonalTailChunk000Sub001Block016Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block016Part021CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block016Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block016Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block016Part021CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block016Part021SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block016Part021] using hcert

def TailChunk000Sub001Block016Part022SupportExplicit : Finset ℕ :=
  ([8965] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block016Part022 : ℚ :=
  (10447465859 : ℚ) / 14696219424153600

def SurrogateDiagonalTailChunk000Sub001Block016Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8965
    = surrogateDiagTailX0RatChunk000Sub001Block016Part022

theorem surrogateDiagonalTailChunk000Sub001Block016Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block016Part022CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block016Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block016Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block016Part022CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block016Part022SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block016Part022] using hcert

def TailChunk000Sub001Block016Part023SupportExplicit : Finset ℕ :=
  ([8966] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block016Part023 : ℚ :=
  (314020140625 : ℚ) / 252263418300751122

def SurrogateDiagonalTailChunk000Sub001Block016Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8966
    = surrogateDiagTailX0RatChunk000Sub001Block016Part023

theorem surrogateDiagonalTailChunk000Sub001Block016Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block016Part023CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block016Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block016Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block016Part023CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block016Part023SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block016Part023] using hcert

def TailChunk000Sub001Block016Part024SupportExplicit : Finset ℕ :=
  ([8969] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block016Part024 : ℚ :=
  (1256921265625 : ℚ) / 4043423826436035072

def SurrogateDiagonalTailChunk000Sub001Block016Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8969
    = surrogateDiagTailX0RatChunk000Sub001Block016Part024

theorem surrogateDiagonalTailChunk000Sub001Block016Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block016Part024CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block016Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block016Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block016Part024CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block016Part024SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block016Part024] using hcert

def surrogateDiagonalTailChunk000Sub001Block016HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block016Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block016Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block016Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block016Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block016Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block016Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block016Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block016Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block016Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block016Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block016Head : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block016Part000
    + surrogateDiagTailX0RatChunk000Sub001Block016Part001
    + surrogateDiagTailX0RatChunk000Sub001Block016Part002
    + surrogateDiagTailX0RatChunk000Sub001Block016Part003
    + surrogateDiagTailX0RatChunk000Sub001Block016Part004
    + surrogateDiagTailX0RatChunk000Sub001Block016Part005
    + surrogateDiagTailX0RatChunk000Sub001Block016Part006
    + surrogateDiagTailX0RatChunk000Sub001Block016Part007
    + surrogateDiagTailX0RatChunk000Sub001Block016Part008
    + surrogateDiagTailX0RatChunk000Sub001Block016Part009

def surrogateDiagonalTailChunk000Sub001Block016MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block016Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block016Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block016Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block016Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block016Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block016Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block016Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block016Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block016Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block016Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block016Mid : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block016Part010
    + surrogateDiagTailX0RatChunk000Sub001Block016Part011
    + surrogateDiagTailX0RatChunk000Sub001Block016Part012
    + surrogateDiagTailX0RatChunk000Sub001Block016Part013
    + surrogateDiagTailX0RatChunk000Sub001Block016Part014
    + surrogateDiagTailX0RatChunk000Sub001Block016Part015
    + surrogateDiagTailX0RatChunk000Sub001Block016Part016
    + surrogateDiagTailX0RatChunk000Sub001Block016Part017
    + surrogateDiagTailX0RatChunk000Sub001Block016Part018
    + surrogateDiagTailX0RatChunk000Sub001Block016Part019

def surrogateDiagonalTailChunk000Sub001Block016TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block016Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block016Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block016Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block016Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block016Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block016Tail : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block016Part020
    + surrogateDiagTailX0RatChunk000Sub001Block016Part021
    + surrogateDiagTailX0RatChunk000Sub001Block016Part022
    + surrogateDiagTailX0RatChunk000Sub001Block016Part023
    + surrogateDiagTailX0RatChunk000Sub001Block016Part024

def surrogateDiagonalTailChunk000Sub001Block016Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub001Block016HeadSum X0
    + surrogateDiagonalTailChunk000Sub001Block016MidSum X0
    + surrogateDiagonalTailChunk000Sub001Block016TailSum X0

def surrogateDiagTailX0RatChunk000Sub001Block016 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block016Part000
    + surrogateDiagTailX0RatChunk000Sub001Block016Part001
    + surrogateDiagTailX0RatChunk000Sub001Block016Part002
    + surrogateDiagTailX0RatChunk000Sub001Block016Part003
    + surrogateDiagTailX0RatChunk000Sub001Block016Part004
    + surrogateDiagTailX0RatChunk000Sub001Block016Part005
    + surrogateDiagTailX0RatChunk000Sub001Block016Part006
    + surrogateDiagTailX0RatChunk000Sub001Block016Part007
    + surrogateDiagTailX0RatChunk000Sub001Block016Part008
    + surrogateDiagTailX0RatChunk000Sub001Block016Part009
    + surrogateDiagTailX0RatChunk000Sub001Block016Part010
    + surrogateDiagTailX0RatChunk000Sub001Block016Part011
    + surrogateDiagTailX0RatChunk000Sub001Block016Part012
    + surrogateDiagTailX0RatChunk000Sub001Block016Part013
    + surrogateDiagTailX0RatChunk000Sub001Block016Part014
    + surrogateDiagTailX0RatChunk000Sub001Block016Part015
    + surrogateDiagTailX0RatChunk000Sub001Block016Part016
    + surrogateDiagTailX0RatChunk000Sub001Block016Part017
    + surrogateDiagTailX0RatChunk000Sub001Block016Part018
    + surrogateDiagTailX0RatChunk000Sub001Block016Part019
    + surrogateDiagTailX0RatChunk000Sub001Block016Part020
    + surrogateDiagTailX0RatChunk000Sub001Block016Part021
    + surrogateDiagTailX0RatChunk000Sub001Block016Part022
    + surrogateDiagTailX0RatChunk000Sub001Block016Part023
    + surrogateDiagTailX0RatChunk000Sub001Block016Part024

theorem surrogateDiagTailX0RatChunk000Sub001Block016_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk000Sub001Block016Head + surrogateDiagTailX0RatChunk000Sub001Block016Mid + surrogateDiagTailX0RatChunk000Sub001Block016Tail =
      surrogateDiagTailX0RatChunk000Sub001Block016 := by
  unfold surrogateDiagTailX0RatChunk000Sub001Block016Head surrogateDiagTailX0RatChunk000Sub001Block016Mid surrogateDiagTailX0RatChunk000Sub001Block016Tail surrogateDiagTailX0RatChunk000Sub001Block016
  ring

def SurrogateDiagonalTailChunk000Sub001Block016HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block016HeadSum X0 = surrogateDiagTailX0RatChunk000Sub001Block016Head

def SurrogateDiagonalTailChunk000Sub001Block016MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block016MidSum X0 = surrogateDiagTailX0RatChunk000Sub001Block016Mid

def SurrogateDiagonalTailChunk000Sub001Block016TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block016TailSum X0 = surrogateDiagTailX0RatChunk000Sub001Block016Tail

theorem surrogateDiagonalTailChunk000Sub001Block016_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk000Sub001Block016HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk000Sub001Block016MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk000Sub001Block016TailCertificateAt X0) :
    surrogateDiagonalTailChunk000Sub001Block016Sum X0 = surrogateDiagTailX0RatChunk000Sub001Block016 := by
  unfold SurrogateDiagonalTailChunk000Sub001Block016HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk000Sub001Block016MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk000Sub001Block016TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk000Sub001Block016Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk000Sub001Block016_eq_head_add_mid_add_tail

/-- Block 017 covers tail-support indices [5425,5450) and q from 8970 to 9011. -/

def TailChunk000Sub001Block017Part000SupportExplicit : Finset ℕ :=
  ([8970] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block017Part000 : ℚ :=
  (604214059975 : ℚ) / 49751080166227968

def SurrogateDiagonalTailChunk000Sub001Block017Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8970
    = surrogateDiagTailX0RatChunk000Sub001Block017Part000

theorem surrogateDiagonalTailChunk000Sub001Block017Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block017Part000CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block017Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block017Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block017Part000CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block017Part000SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block017Part000] using hcert

def TailChunk000Sub001Block017Part001SupportExplicit : Finset ℕ :=
  ([8971] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block017Part001 : ℚ :=
  (2011971025 : ℚ) / 6475251220095762

def SurrogateDiagonalTailChunk000Sub001Block017Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8971
    = surrogateDiagTailX0RatChunk000Sub001Block017Part001

theorem surrogateDiagonalTailChunk000Sub001Block017Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block017Part001CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block017Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block017Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block017Part001CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block017Part001SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block017Part001] using hcert

def TailChunk000Sub001Block017Part002SupportExplicit : Finset ℕ :=
  ([8974] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block017Part002 : ℚ :=
  (478794323 : ℚ) / 241640228782080

def SurrogateDiagonalTailChunk000Sub001Block017Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8974
    = surrogateDiagTailX0RatChunk000Sub001Block017Part002

theorem surrogateDiagonalTailChunk000Sub001Block017Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block017Part002CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block017Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block017Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block017Part002CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block017Part002SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block017Part002] using hcert

def TailChunk000Sub001Block017Part003SupportExplicit : Finset ℕ :=
  ([8977] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block017Part003 : ℚ :=
  (7752940525 : ℚ) / 23344929787387008

def SurrogateDiagonalTailChunk000Sub001Block017Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8977
    = surrogateDiagTailX0RatChunk000Sub001Block017Part003

theorem surrogateDiagonalTailChunk000Sub001Block017Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block017Part003CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block017Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block017Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block017Part003CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block017Part003SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block017Part003] using hcert

def TailChunk000Sub001Block017Part004SupportExplicit : Finset ℕ :=
  ([8979] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block017Part004 : ℚ :=
  (85602689077 : ℚ) / 110097329238835200

def SurrogateDiagonalTailChunk000Sub001Block017Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8979
    = surrogateDiagTailX0RatChunk000Sub001Block017Part004

theorem surrogateDiagonalTailChunk000Sub001Block017Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block017Part004CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block017Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block017Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block017Part004CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block017Part004SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block017Part004] using hcert

def TailChunk000Sub001Block017Part005SupportExplicit : Finset ℕ :=
  ([8981] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block017Part005 : ℚ :=
  (222698770475 : ℚ) / 486308047104668736

def SurrogateDiagonalTailChunk000Sub001Block017Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8981
    = surrogateDiagTailX0RatChunk000Sub001Block017Part005

theorem surrogateDiagonalTailChunk000Sub001Block017Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block017Part005CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block017Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block017Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block017Part005CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block017Part005SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block017Part005] using hcert

def TailChunk000Sub001Block017Part006SupportExplicit : Finset ℕ :=
  ([8983] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block017Part006 : ℚ :=
  (178714424371 : ℚ) / 470119426140211200

def SurrogateDiagonalTailChunk000Sub001Block017Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8983
    = surrogateDiagTailX0RatChunk000Sub001Block017Part006

theorem surrogateDiagonalTailChunk000Sub001Block017Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block017Part006CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block017Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block017Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block017Part006CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block017Part006SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block017Part006] using hcert

def TailChunk000Sub001Block017Part007SupportExplicit : Finset ℕ :=
  ([8985] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block017Part007 : ℚ :=
  (40026363475 : ℚ) / 25187681858985984

def SurrogateDiagonalTailChunk000Sub001Block017Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8985
    = surrogateDiagTailX0RatChunk000Sub001Block017Part007

theorem surrogateDiagonalTailChunk000Sub001Block017Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block017Part007CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block017Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block017Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block017Part007CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block017Part007SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block017Part007] using hcert

def TailChunk000Sub001Block017Part008SupportExplicit : Finset ℕ :=
  ([8986] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block017Part008 : ℚ :=
  (315422640625 : ℚ) / 254522311025908512

def SurrogateDiagonalTailChunk000Sub001Block017Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8986
    = surrogateDiagTailX0RatChunk000Sub001Block017Part008

theorem surrogateDiagonalTailChunk000Sub001Block017Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block017Part008CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block017Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block017Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block017Part008CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block017Part008SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block017Part008] using hcert

def TailChunk000Sub001Block017Part009SupportExplicit : Finset ℕ :=
  ([8987] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block017Part009 : ℚ :=
  (158064487381 : ℚ) / 326718729975859200

def SurrogateDiagonalTailChunk000Sub001Block017Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8987
    = surrogateDiagTailX0RatChunk000Sub001Block017Part009

theorem surrogateDiagonalTailChunk000Sub001Block017Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block017Part009CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block017Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block017Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block017Part009CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block017Part009SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block017Part009] using hcert

def TailChunk000Sub001Block017Part010SupportExplicit : Finset ℕ :=
  ([8989] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block017Part010 : ℚ :=
  (13063540329 : ℚ) / 39987686604800000

def SurrogateDiagonalTailChunk000Sub001Block017Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8989
    = surrogateDiagTailX0RatChunk000Sub001Block017Part010

theorem surrogateDiagonalTailChunk000Sub001Block017Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block017Part010CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block017Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block017Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block017Part010CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block017Part010SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block017Part010] using hcert

def TailChunk000Sub001Block017Part011SupportExplicit : Finset ℕ :=
  ([8990] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block017Part011 : ℚ :=
  (38062874131 : ℚ) / 12748055917363200

def SurrogateDiagonalTailChunk000Sub001Block017Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8990
    = surrogateDiagTailX0RatChunk000Sub001Block017Part011

theorem surrogateDiagonalTailChunk000Sub001Block017Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block017Part011CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block017Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block017Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block017Part011CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block017Part011SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block017Part011] using hcert

def TailChunk000Sub001Block017Part012SupportExplicit : Finset ℕ :=
  ([8994] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block017Part012 : ℚ :=
  (1718625 : ℚ) / 411065628736

def SurrogateDiagonalTailChunk000Sub001Block017Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8994
    = surrogateDiagTailX0RatChunk000Sub001Block017Part012

theorem surrogateDiagonalTailChunk000Sub001Block017Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block017Part012CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block017Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block017Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block017Part012CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block017Part012SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block017Part012] using hcert

def TailChunk000Sub001Block017Part013SupportExplicit : Finset ℕ :=
  ([8995] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block017Part013 : ℚ :=
  (316709839225 : ℚ) / 395903350836559872

def SurrogateDiagonalTailChunk000Sub001Block017Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8995
    = surrogateDiagTailX0RatChunk000Sub001Block017Part013

theorem surrogateDiagonalTailChunk000Sub001Block017Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block017Part013CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block017Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block017Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block017Part013CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block017Part013SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block017Part013] using hcert

def TailChunk000Sub001Block017Part014SupportExplicit : Finset ℕ :=
  ([8997] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block017Part014 : ℚ :=
  (702456378175 : ℚ) / 808003727471968032

def SurrogateDiagonalTailChunk000Sub001Block017Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8997
    = surrogateDiagTailX0RatChunk000Sub001Block017Part014

theorem surrogateDiagonalTailChunk000Sub001Block017Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block017Part014CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block017Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block017Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block017Part014CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block017Part014SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block017Part014] using hcert

def TailChunk000Sub001Block017Part015SupportExplicit : Finset ℕ :=
  ([8998] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block017Part015 : ℚ :=
  (9265555187 : ℚ) / 5543161069731840

def SurrogateDiagonalTailChunk000Sub001Block017Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8998
    = surrogateDiagTailX0RatChunk000Sub001Block017Part015

theorem surrogateDiagonalTailChunk000Sub001Block017Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block017Part015CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block017Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block017Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block017Part015CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block017Part015SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block017Part015] using hcert

def TailChunk000Sub001Block017Part016SupportExplicit : Finset ℕ :=
  ([8999] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block017Part016 : ℚ :=
  (1265343765625 : ℚ) / 4097800611062974002

def SurrogateDiagonalTailChunk000Sub001Block017Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8999
    = surrogateDiagTailX0RatChunk000Sub001Block017Part016

theorem surrogateDiagonalTailChunk000Sub001Block017Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block017Part016CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block017Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block017Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block017Part016CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block017Part016SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block017Part016] using hcert

def TailChunk000Sub001Block017Part017SupportExplicit : Finset ℕ :=
  ([9001] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block017Part017 : ℚ :=
  (81018001 : ℚ) / 262492488000000

def SurrogateDiagonalTailChunk000Sub001Block017Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9001
    = surrogateDiagTailX0RatChunk000Sub001Block017Part017

theorem surrogateDiagonalTailChunk000Sub001Block017Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block017Part017CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block017Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block017Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block017Part017CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block017Part017SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block017Part017] using hcert

def TailChunk000Sub001Block017Part018SupportExplicit : Finset ℕ :=
  ([9002] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block017Part018 : ℚ :=
  (277444823125 : ℚ) / 137629642370149152

def SurrogateDiagonalTailChunk000Sub001Block017Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9002
    = surrogateDiagTailX0RatChunk000Sub001Block017Part018

theorem surrogateDiagonalTailChunk000Sub001Block017Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block017Part018CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block017Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block017Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block017Part018CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block017Part018SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block017Part018] using hcert

def TailChunk000Sub001Block017Part019SupportExplicit : Finset ℕ :=
  ([9003] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block017Part019 : ℚ :=
  (56271497249 : ℚ) / 64812960000000000

def SurrogateDiagonalTailChunk000Sub001Block017Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9003
    = surrogateDiagTailX0RatChunk000Sub001Block017Part019

theorem surrogateDiagonalTailChunk000Sub001Block017Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block017Part019CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block017Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block017Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block017Part019CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block017Part019SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block017Part019] using hcert

def TailChunk000Sub001Block017Part020SupportExplicit : Finset ℕ :=
  ([9005] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block017Part020 : ℚ :=
  (145872692197 : ℚ) / 268792307712000000

def SurrogateDiagonalTailChunk000Sub001Block017Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9005
    = surrogateDiagTailX0RatChunk000Sub001Block017Part020

theorem surrogateDiagonalTailChunk000Sub001Block017Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block017Part020CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block017Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block017Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block017Part020CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block017Part020SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block017Part020] using hcert

def TailChunk000Sub001Block017Part021SupportExplicit : Finset ℕ :=
  ([9006] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block017Part021 : ℚ :=
  (796130127175 : ℚ) / 155458786286389248

def SurrogateDiagonalTailChunk000Sub001Block017Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9006
    = surrogateDiagTailX0RatChunk000Sub001Block017Part021

theorem surrogateDiagonalTailChunk000Sub001Block017Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block017Part021CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block017Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block017Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block017Part021CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block017Part021SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block017Part021] using hcert

def TailChunk000Sub001Block017Part022SupportExplicit : Finset ℕ :=
  ([9007] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block017Part022 : ℚ :=
  (1267594515625 : ℚ) / 4112393254048782162

def SurrogateDiagonalTailChunk000Sub001Block017Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9007
    = surrogateDiagTailX0RatChunk000Sub001Block017Part022

theorem surrogateDiagonalTailChunk000Sub001Block017Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block017Part022CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block017Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block017Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block017Part022CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block017Part022SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block017Part022] using hcert

def TailChunk000Sub001Block017Part023SupportExplicit : Finset ℕ :=
  ([9010] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block017Part023 : ℚ :=
  (272541606375 : ℚ) / 51122122772185088

def SurrogateDiagonalTailChunk000Sub001Block017Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9010
    = surrogateDiagTailX0RatChunk000Sub001Block017Part023

theorem surrogateDiagonalTailChunk000Sub001Block017Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block017Part023CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block017Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block017Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block017Part023CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block017Part023SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block017Part023] using hcert

def TailChunk000Sub001Block017Part024SupportExplicit : Finset ℕ :=
  ([9011] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block017Part024 : ℚ :=
  (2029953025 : ℚ) / 6591526677737202

def SurrogateDiagonalTailChunk000Sub001Block017Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9011
    = surrogateDiagTailX0RatChunk000Sub001Block017Part024

theorem surrogateDiagonalTailChunk000Sub001Block017Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block017Part024CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block017Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block017Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block017Part024CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block017Part024SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block017Part024] using hcert

def surrogateDiagonalTailChunk000Sub001Block017HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block017Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block017Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block017Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block017Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block017Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block017Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block017Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block017Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block017Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block017Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block017Head : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block017Part000
    + surrogateDiagTailX0RatChunk000Sub001Block017Part001
    + surrogateDiagTailX0RatChunk000Sub001Block017Part002
    + surrogateDiagTailX0RatChunk000Sub001Block017Part003
    + surrogateDiagTailX0RatChunk000Sub001Block017Part004
    + surrogateDiagTailX0RatChunk000Sub001Block017Part005
    + surrogateDiagTailX0RatChunk000Sub001Block017Part006
    + surrogateDiagTailX0RatChunk000Sub001Block017Part007
    + surrogateDiagTailX0RatChunk000Sub001Block017Part008
    + surrogateDiagTailX0RatChunk000Sub001Block017Part009

def surrogateDiagonalTailChunk000Sub001Block017MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block017Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block017Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block017Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block017Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block017Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block017Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block017Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block017Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block017Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block017Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block017Mid : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block017Part010
    + surrogateDiagTailX0RatChunk000Sub001Block017Part011
    + surrogateDiagTailX0RatChunk000Sub001Block017Part012
    + surrogateDiagTailX0RatChunk000Sub001Block017Part013
    + surrogateDiagTailX0RatChunk000Sub001Block017Part014
    + surrogateDiagTailX0RatChunk000Sub001Block017Part015
    + surrogateDiagTailX0RatChunk000Sub001Block017Part016
    + surrogateDiagTailX0RatChunk000Sub001Block017Part017
    + surrogateDiagTailX0RatChunk000Sub001Block017Part018
    + surrogateDiagTailX0RatChunk000Sub001Block017Part019

def surrogateDiagonalTailChunk000Sub001Block017TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block017Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block017Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block017Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block017Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block017Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block017Tail : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block017Part020
    + surrogateDiagTailX0RatChunk000Sub001Block017Part021
    + surrogateDiagTailX0RatChunk000Sub001Block017Part022
    + surrogateDiagTailX0RatChunk000Sub001Block017Part023
    + surrogateDiagTailX0RatChunk000Sub001Block017Part024

def surrogateDiagonalTailChunk000Sub001Block017Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub001Block017HeadSum X0
    + surrogateDiagonalTailChunk000Sub001Block017MidSum X0
    + surrogateDiagonalTailChunk000Sub001Block017TailSum X0

def surrogateDiagTailX0RatChunk000Sub001Block017 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block017Part000
    + surrogateDiagTailX0RatChunk000Sub001Block017Part001
    + surrogateDiagTailX0RatChunk000Sub001Block017Part002
    + surrogateDiagTailX0RatChunk000Sub001Block017Part003
    + surrogateDiagTailX0RatChunk000Sub001Block017Part004
    + surrogateDiagTailX0RatChunk000Sub001Block017Part005
    + surrogateDiagTailX0RatChunk000Sub001Block017Part006
    + surrogateDiagTailX0RatChunk000Sub001Block017Part007
    + surrogateDiagTailX0RatChunk000Sub001Block017Part008
    + surrogateDiagTailX0RatChunk000Sub001Block017Part009
    + surrogateDiagTailX0RatChunk000Sub001Block017Part010
    + surrogateDiagTailX0RatChunk000Sub001Block017Part011
    + surrogateDiagTailX0RatChunk000Sub001Block017Part012
    + surrogateDiagTailX0RatChunk000Sub001Block017Part013
    + surrogateDiagTailX0RatChunk000Sub001Block017Part014
    + surrogateDiagTailX0RatChunk000Sub001Block017Part015
    + surrogateDiagTailX0RatChunk000Sub001Block017Part016
    + surrogateDiagTailX0RatChunk000Sub001Block017Part017
    + surrogateDiagTailX0RatChunk000Sub001Block017Part018
    + surrogateDiagTailX0RatChunk000Sub001Block017Part019
    + surrogateDiagTailX0RatChunk000Sub001Block017Part020
    + surrogateDiagTailX0RatChunk000Sub001Block017Part021
    + surrogateDiagTailX0RatChunk000Sub001Block017Part022
    + surrogateDiagTailX0RatChunk000Sub001Block017Part023
    + surrogateDiagTailX0RatChunk000Sub001Block017Part024

theorem surrogateDiagTailX0RatChunk000Sub001Block017_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk000Sub001Block017Head + surrogateDiagTailX0RatChunk000Sub001Block017Mid + surrogateDiagTailX0RatChunk000Sub001Block017Tail =
      surrogateDiagTailX0RatChunk000Sub001Block017 := by
  unfold surrogateDiagTailX0RatChunk000Sub001Block017Head surrogateDiagTailX0RatChunk000Sub001Block017Mid surrogateDiagTailX0RatChunk000Sub001Block017Tail surrogateDiagTailX0RatChunk000Sub001Block017
  ring

def SurrogateDiagonalTailChunk000Sub001Block017HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block017HeadSum X0 = surrogateDiagTailX0RatChunk000Sub001Block017Head

def SurrogateDiagonalTailChunk000Sub001Block017MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block017MidSum X0 = surrogateDiagTailX0RatChunk000Sub001Block017Mid

def SurrogateDiagonalTailChunk000Sub001Block017TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block017TailSum X0 = surrogateDiagTailX0RatChunk000Sub001Block017Tail

theorem surrogateDiagonalTailChunk000Sub001Block017_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk000Sub001Block017HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk000Sub001Block017MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk000Sub001Block017TailCertificateAt X0) :
    surrogateDiagonalTailChunk000Sub001Block017Sum X0 = surrogateDiagTailX0RatChunk000Sub001Block017 := by
  unfold SurrogateDiagonalTailChunk000Sub001Block017HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk000Sub001Block017MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk000Sub001Block017TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk000Sub001Block017Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk000Sub001Block017_eq_head_add_mid_add_tail

/-- Block 018 covers tail-support indices [5450,5475) and q from 9013 to 9051. -/

def TailChunk000Sub001Block018Part000SupportExplicit : Finset ℕ :=
  ([9013] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block018Part000 : ℚ :=
  (1269283890625 : ℚ) / 4123363286648738592

def SurrogateDiagonalTailChunk000Sub001Block018Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9013
    = surrogateDiagTailX0RatChunk000Sub001Block018Part000

theorem surrogateDiagonalTailChunk000Sub001Block018Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block018Part000CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block018Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block018Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block018Part000CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block018Part000SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block018Part000] using hcert

def TailChunk000Sub001Block018Part001SupportExplicit : Finset ℕ :=
  ([9014] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block018Part001 : ℚ :=
  (2538623298775 : ℚ) / 1030840821662184648

def SurrogateDiagonalTailChunk000Sub001Block018Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9014
    = surrogateDiagTailX0RatChunk000Sub001Block018Part001

theorem surrogateDiagonalTailChunk000Sub001Block018Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block018Part001CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block018Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block018Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block018Part001CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block018Part001SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block018Part001] using hcert

def TailChunk000Sub001Block018Part002SupportExplicit : Finset ℕ :=
  ([9015] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block018Part002 : ℚ :=
  (4656221519 : ℚ) / 2949709824000000

def SurrogateDiagonalTailChunk000Sub001Block018Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9015
    = surrogateDiagTailX0RatChunk000Sub001Block018Part002

theorem surrogateDiagonalTailChunk000Sub001Block018Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block018Part002CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block018Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block018Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block018Part002CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block018Part002SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block018Part002] using hcert

def TailChunk000Sub001Block018Part003SupportExplicit : Finset ℕ :=
  ([9017] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block018Part003 : ℚ :=
  (97657583 : ℚ) / 300241459784700

def SurrogateDiagonalTailChunk000Sub001Block018Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9017
    = surrogateDiagTailX0RatChunk000Sub001Block018Part003

theorem surrogateDiagonalTailChunk000Sub001Block018Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block018Part003CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block018Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block018Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block018Part003CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block018Part003SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block018Part003] using hcert

def TailChunk000Sub001Block018Part004SupportExplicit : Finset ℕ :=
  ([9019] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block018Part004 : ℚ :=
  (2090837723 : ℚ) / 283880626660377600

def SurrogateDiagonalTailChunk000Sub001Block018Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9019
    = surrogateDiagTailX0RatChunk000Sub001Block018Part004

theorem surrogateDiagonalTailChunk000Sub001Block018Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block018Part004CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block018Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block018Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block018Part004CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block018Part004SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block018Part004] using hcert

def TailChunk000Sub001Block018Part005SupportExplicit : Finset ℕ :=
  ([9021] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block018Part005 : ℚ :=
  (2979370583 : ℚ) / 13762166154854400

def SurrogateDiagonalTailChunk000Sub001Block018Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9021
    = surrogateDiagTailX0RatChunk000Sub001Block018Part005

theorem surrogateDiagonalTailChunk000Sub001Block018Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block018Part005CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block018Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block018Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block018Part005CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block018Part005SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block018Part005] using hcert

def TailChunk000Sub001Block018Part006SupportExplicit : Finset ℕ :=
  ([9022] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block018Part006 : ℚ :=
  (1186170222775 : ℚ) / 743115360160401408

def SurrogateDiagonalTailChunk000Sub001Block018Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9022
    = surrogateDiagTailX0RatChunk000Sub001Block018Part006

theorem surrogateDiagonalTailChunk000Sub001Block018Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block018Part006CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block018Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block018Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block018Part006CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block018Part006SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block018Part006] using hcert

def TailChunk000Sub001Block018Part007SupportExplicit : Finset ℕ :=
  ([9023] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block018Part007 : ℚ :=
  (416361591925 : ℚ) / 8918571789927088128

def SurrogateDiagonalTailChunk000Sub001Block018Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9023
    = surrogateDiagTailX0RatChunk000Sub001Block018Part007

theorem surrogateDiagonalTailChunk000Sub001Block018Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block018Part007CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block018Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block018Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block018Part007CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block018Part007SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block018Part007] using hcert

def TailChunk000Sub001Block018Part008SupportExplicit : Finset ℕ :=
  ([9026] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block018Part008 : ℚ :=
  (318237015625 : ℚ) / 259085573706350592

def SurrogateDiagonalTailChunk000Sub001Block018Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9026
    = surrogateDiagTailX0RatChunk000Sub001Block018Part008

theorem surrogateDiagonalTailChunk000Sub001Block018Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block018Part008CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block018Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block018Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block018Part008CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block018Part008SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block018Part008] using hcert

def TailChunk000Sub001Block018Part009SupportExplicit : Finset ℕ :=
  ([9029] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block018Part009 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block018Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9029
    = surrogateDiagTailX0RatChunk000Sub001Block018Part009

theorem surrogateDiagonalTailChunk000Sub001Block018Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block018Part009CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block018Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block018Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block018Part009CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block018Part009SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block018Part009] using hcert

def TailChunk000Sub001Block018Part010SupportExplicit : Finset ℕ :=
  ([9030] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block018Part010 : ℚ :=
  (591880201375 : ℚ) / 41303701172256768

def SurrogateDiagonalTailChunk000Sub001Block018Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9030
    = surrogateDiagTailX0RatChunk000Sub001Block018Part010

theorem surrogateDiagonalTailChunk000Sub001Block018Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block018Part010CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block018Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block018Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block018Part010CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block018Part010SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block018Part010] using hcert

def TailChunk000Sub001Block018Part011SupportExplicit : Finset ℕ :=
  ([9031] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block018Part011 : ℚ :=
  (1020098977 : ℚ) / 45221218435200000

def SurrogateDiagonalTailChunk000Sub001Block018Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9031
    = surrogateDiagTailX0RatChunk000Sub001Block018Part011

theorem surrogateDiagonalTailChunk000Sub001Block018Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block018Part011CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block018Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block018Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block018Part011CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block018Part011SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block018Part011] using hcert

def TailChunk000Sub001Block018Part012SupportExplicit : Finset ℕ :=
  ([9033] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block018Part012 : ℚ :=
  (323932207 : ℚ) / 1876613236397760

def SurrogateDiagonalTailChunk000Sub001Block018Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9033
    = surrogateDiagTailX0RatChunk000Sub001Block018Part012

theorem surrogateDiagonalTailChunk000Sub001Block018Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block018Part012CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block018Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block018Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block018Part012CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block018Part012SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block018Part012] using hcert

def TailChunk000Sub001Block018Part013SupportExplicit : Finset ℕ :=
  ([9034] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block018Part013 : ℚ :=
  (318801390625 : ℚ) / 260005539330684192

def SurrogateDiagonalTailChunk000Sub001Block018Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9034
    = surrogateDiagTailX0RatChunk000Sub001Block018Part013

theorem surrogateDiagonalTailChunk000Sub001Block018Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block018Part013CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block018Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block018Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block018Part013CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block018Part013SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block018Part013] using hcert

def TailChunk000Sub001Block018Part014SupportExplicit : Finset ℕ :=
  ([9035] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block018Part014 : ℚ :=
  (693212093275 : ℚ) / 4814022923675762688

def SurrogateDiagonalTailChunk000Sub001Block018Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9035
    = surrogateDiagTailX0RatChunk000Sub001Block018Part014

theorem surrogateDiagonalTailChunk000Sub001Block018Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block018Part014CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block018Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block018Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block018Part014CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block018Part014SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block018Part014] using hcert

def TailChunk000Sub001Block018Part015SupportExplicit : Finset ℕ :=
  ([9037] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block018Part015 : ℚ :=
  (16705992733 : ℚ) / 358963832186755200

def SurrogateDiagonalTailChunk000Sub001Block018Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9037
    = surrogateDiagTailX0RatChunk000Sub001Block018Part015

theorem surrogateDiagonalTailChunk000Sub001Block018Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block018Part015CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block018Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block018Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block018Part015CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block018Part015SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block018Part015] using hcert

def TailChunk000Sub001Block018Part016SupportExplicit : Finset ℕ :=
  ([9038] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block018Part016 : ℚ :=
  (319083765625 : ℚ) / 260466439796995122

def SurrogateDiagonalTailChunk000Sub001Block018Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9038
    = surrogateDiagTailX0RatChunk000Sub001Block018Part016

theorem surrogateDiagonalTailChunk000Sub001Block018Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block018Part016CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block018Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block018Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block018Part016CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block018Part016SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block018Part016] using hcert

def TailChunk000Sub001Block018Part017SupportExplicit : Finset ℕ :=
  ([9039] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block018Part017 : ℚ :=
  (4447767001 : ℚ) / 10707077972997120

def SurrogateDiagonalTailChunk000Sub001Block018Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9039
    = surrogateDiagTailX0RatChunk000Sub001Block018Part017

theorem surrogateDiagonalTailChunk000Sub001Block018Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block018Part017CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block018Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block018Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block018Part017CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block018Part017SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block018Part017] using hcert

def TailChunk000Sub001Block018Part018SupportExplicit : Finset ℕ :=
  ([9041] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block018Part018 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block018Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9041
    = surrogateDiagTailX0RatChunk000Sub001Block018Part018

theorem surrogateDiagonalTailChunk000Sub001Block018Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block018Part018CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block018Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block018Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block018Part018CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block018Part018SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block018Part018] using hcert

def TailChunk000Sub001Block018Part019SupportExplicit : Finset ℕ :=
  ([9042] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block018Part019 : ℚ :=
  (178372913 : ℚ) / 27373634912256

def SurrogateDiagonalTailChunk000Sub001Block018Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9042
    = surrogateDiagTailX0RatChunk000Sub001Block018Part019

theorem surrogateDiagonalTailChunk000Sub001Block018Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block018Part019CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block018Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block018Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block018Part019CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block018Part019SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block018Part019] using hcert

def TailChunk000Sub001Block018Part020SupportExplicit : Finset ℕ :=
  ([9043] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block018Part020 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block018Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9043
    = surrogateDiagTailX0RatChunk000Sub001Block018Part020

theorem surrogateDiagonalTailChunk000Sub001Block018Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block018Part020CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block018Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block018Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block018Part020CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block018Part020SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block018Part020] using hcert

def TailChunk000Sub001Block018Part021SupportExplicit : Finset ℕ :=
  ([9046] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block018Part021 : ℚ :=
  (319648890625 : ℚ) / 261390078748647282

def SurrogateDiagonalTailChunk000Sub001Block018Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9046
    = surrogateDiagTailX0RatChunk000Sub001Block018Part021

theorem surrogateDiagonalTailChunk000Sub001Block018Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block018Part021CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block018Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block018Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block018Part021CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block018Part021SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block018Part021] using hcert

def TailChunk000Sub001Block018Part022SupportExplicit : Finset ℕ :=
  ([9047] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block018Part022 : ℚ :=
  (58755122875 : ℚ) / 15380742109709518848

def SurrogateDiagonalTailChunk000Sub001Block018Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9047
    = surrogateDiagTailX0RatChunk000Sub001Block018Part022

theorem surrogateDiagonalTailChunk000Sub001Block018Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block018Part022CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block018Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block018Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block018Part022CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block018Part022SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block018Part022] using hcert

def TailChunk000Sub001Block018Part023SupportExplicit : Finset ℕ :=
  ([9049] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block018Part023 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block018Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9049
    = surrogateDiagTailX0RatChunk000Sub001Block018Part023

theorem surrogateDiagonalTailChunk000Sub001Block018Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block018Part023CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block018Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block018Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block018Part023CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block018Part023SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block018Part023] using hcert

def TailChunk000Sub001Block018Part024SupportExplicit : Finset ℕ :=
  ([9051] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block018Part024 : ℚ :=
  (266214211 : ℚ) / 437694049305600

def SurrogateDiagonalTailChunk000Sub001Block018Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9051
    = surrogateDiagTailX0RatChunk000Sub001Block018Part024

theorem surrogateDiagonalTailChunk000Sub001Block018Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block018Part024CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block018Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block018Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block018Part024CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block018Part024SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block018Part024] using hcert

def surrogateDiagonalTailChunk000Sub001Block018HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block018Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block018Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block018Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block018Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block018Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block018Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block018Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block018Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block018Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block018Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block018Head : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block018Part000
    + surrogateDiagTailX0RatChunk000Sub001Block018Part001
    + surrogateDiagTailX0RatChunk000Sub001Block018Part002
    + surrogateDiagTailX0RatChunk000Sub001Block018Part003
    + surrogateDiagTailX0RatChunk000Sub001Block018Part004
    + surrogateDiagTailX0RatChunk000Sub001Block018Part005
    + surrogateDiagTailX0RatChunk000Sub001Block018Part006
    + surrogateDiagTailX0RatChunk000Sub001Block018Part007
    + surrogateDiagTailX0RatChunk000Sub001Block018Part008
    + surrogateDiagTailX0RatChunk000Sub001Block018Part009

def surrogateDiagonalTailChunk000Sub001Block018MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block018Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block018Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block018Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block018Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block018Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block018Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block018Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block018Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block018Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block018Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block018Mid : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block018Part010
    + surrogateDiagTailX0RatChunk000Sub001Block018Part011
    + surrogateDiagTailX0RatChunk000Sub001Block018Part012
    + surrogateDiagTailX0RatChunk000Sub001Block018Part013
    + surrogateDiagTailX0RatChunk000Sub001Block018Part014
    + surrogateDiagTailX0RatChunk000Sub001Block018Part015
    + surrogateDiagTailX0RatChunk000Sub001Block018Part016
    + surrogateDiagTailX0RatChunk000Sub001Block018Part017
    + surrogateDiagTailX0RatChunk000Sub001Block018Part018
    + surrogateDiagTailX0RatChunk000Sub001Block018Part019

def surrogateDiagonalTailChunk000Sub001Block018TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block018Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block018Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block018Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block018Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block018Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block018Tail : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block018Part020
    + surrogateDiagTailX0RatChunk000Sub001Block018Part021
    + surrogateDiagTailX0RatChunk000Sub001Block018Part022
    + surrogateDiagTailX0RatChunk000Sub001Block018Part023
    + surrogateDiagTailX0RatChunk000Sub001Block018Part024

def surrogateDiagonalTailChunk000Sub001Block018Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub001Block018HeadSum X0
    + surrogateDiagonalTailChunk000Sub001Block018MidSum X0
    + surrogateDiagonalTailChunk000Sub001Block018TailSum X0

def surrogateDiagTailX0RatChunk000Sub001Block018 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block018Part000
    + surrogateDiagTailX0RatChunk000Sub001Block018Part001
    + surrogateDiagTailX0RatChunk000Sub001Block018Part002
    + surrogateDiagTailX0RatChunk000Sub001Block018Part003
    + surrogateDiagTailX0RatChunk000Sub001Block018Part004
    + surrogateDiagTailX0RatChunk000Sub001Block018Part005
    + surrogateDiagTailX0RatChunk000Sub001Block018Part006
    + surrogateDiagTailX0RatChunk000Sub001Block018Part007
    + surrogateDiagTailX0RatChunk000Sub001Block018Part008
    + surrogateDiagTailX0RatChunk000Sub001Block018Part009
    + surrogateDiagTailX0RatChunk000Sub001Block018Part010
    + surrogateDiagTailX0RatChunk000Sub001Block018Part011
    + surrogateDiagTailX0RatChunk000Sub001Block018Part012
    + surrogateDiagTailX0RatChunk000Sub001Block018Part013
    + surrogateDiagTailX0RatChunk000Sub001Block018Part014
    + surrogateDiagTailX0RatChunk000Sub001Block018Part015
    + surrogateDiagTailX0RatChunk000Sub001Block018Part016
    + surrogateDiagTailX0RatChunk000Sub001Block018Part017
    + surrogateDiagTailX0RatChunk000Sub001Block018Part018
    + surrogateDiagTailX0RatChunk000Sub001Block018Part019
    + surrogateDiagTailX0RatChunk000Sub001Block018Part020
    + surrogateDiagTailX0RatChunk000Sub001Block018Part021
    + surrogateDiagTailX0RatChunk000Sub001Block018Part022
    + surrogateDiagTailX0RatChunk000Sub001Block018Part023
    + surrogateDiagTailX0RatChunk000Sub001Block018Part024

theorem surrogateDiagTailX0RatChunk000Sub001Block018_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk000Sub001Block018Head + surrogateDiagTailX0RatChunk000Sub001Block018Mid + surrogateDiagTailX0RatChunk000Sub001Block018Tail =
      surrogateDiagTailX0RatChunk000Sub001Block018 := by
  unfold surrogateDiagTailX0RatChunk000Sub001Block018Head surrogateDiagTailX0RatChunk000Sub001Block018Mid surrogateDiagTailX0RatChunk000Sub001Block018Tail surrogateDiagTailX0RatChunk000Sub001Block018
  ring

def SurrogateDiagonalTailChunk000Sub001Block018HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block018HeadSum X0 = surrogateDiagTailX0RatChunk000Sub001Block018Head

def SurrogateDiagonalTailChunk000Sub001Block018MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block018MidSum X0 = surrogateDiagTailX0RatChunk000Sub001Block018Mid

def SurrogateDiagonalTailChunk000Sub001Block018TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block018TailSum X0 = surrogateDiagTailX0RatChunk000Sub001Block018Tail

theorem surrogateDiagonalTailChunk000Sub001Block018_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk000Sub001Block018HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk000Sub001Block018MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk000Sub001Block018TailCertificateAt X0) :
    surrogateDiagonalTailChunk000Sub001Block018Sum X0 = surrogateDiagTailX0RatChunk000Sub001Block018 := by
  unfold SurrogateDiagonalTailChunk000Sub001Block018HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk000Sub001Block018MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk000Sub001Block018TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk000Sub001Block018Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk000Sub001Block018_eq_head_add_mid_add_tail

/-- Block 019 covers tail-support indices [5475,5500) and q from 9053 to 9093. -/

def TailChunk000Sub001Block019Part000SupportExplicit : Finset ℕ :=
  ([9053] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block019Part000 : ℚ :=
  (1025020039 : ℚ) / 45664017762957120

def SurrogateDiagonalTailChunk000Sub001Block019Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9053
    = surrogateDiagTailX0RatChunk000Sub001Block019Part000

theorem surrogateDiagonalTailChunk000Sub001Block019Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block019Part000CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block019Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block019Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block019Part000CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block019Part000SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block019Part000] using hcert

def TailChunk000Sub001Block019Part001SupportExplicit : Finset ℕ :=
  ([9055] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block019Part001 : ℚ :=
  (16427247169 : ℚ) / 274815431071795200

def SurrogateDiagonalTailChunk000Sub001Block019Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9055
    = surrogateDiagTailX0RatChunk000Sub001Block019Part001

theorem surrogateDiagonalTailChunk000Sub001Block019Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block019Part001CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block019Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block019Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block019Part001CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block019Part001SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block019Part001] using hcert

def TailChunk000Sub001Block019Part002SupportExplicit : Finset ℕ :=
  ([9057] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block019Part002 : ℚ :=
  (569468807525 : ℚ) / 1659563168043875904

def SurrogateDiagonalTailChunk000Sub001Block019Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9057
    = surrogateDiagTailX0RatChunk000Sub001Block019Part002

theorem surrogateDiagonalTailChunk000Sub001Block019Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block019Part002CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block019Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block019Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block019Part002CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block019Part002SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block019Part002] using hcert

def TailChunk000Sub001Block019Part003SupportExplicit : Finset ℕ :=
  ([9058] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block019Part003 : ℚ :=
  (280906999375 : ℚ) / 141091854251664672

def SurrogateDiagonalTailChunk000Sub001Block019Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9058
    = surrogateDiagTailX0RatChunk000Sub001Block019Part003

theorem surrogateDiagonalTailChunk000Sub001Block019Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block019Part003CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block019Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block019Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block019Part003CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block019Part003SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block019Part003] using hcert

def TailChunk000Sub001Block019Part004SupportExplicit : Finset ℕ :=
  ([9059] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block019Part004 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block019Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9059
    = surrogateDiagTailX0RatChunk000Sub001Block019Part004

theorem surrogateDiagonalTailChunk000Sub001Block019Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block019Part004CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block019Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block019Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block019Part004CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block019Part004SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block019Part004] using hcert

def TailChunk000Sub001Block019Part005SupportExplicit : Finset ℕ :=
  ([9061] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block019Part005 : ℚ :=
  (5064684317 : ℚ) / 115987309815398400

def SurrogateDiagonalTailChunk000Sub001Block019Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9061
    = surrogateDiagTailX0RatChunk000Sub001Block019Part005

theorem surrogateDiagonalTailChunk000Sub001Block019Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block019Part005CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block019Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block019Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block019Part005CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block019Part005SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block019Part005] using hcert

def TailChunk000Sub001Block019Part006SupportExplicit : Finset ℕ :=
  ([9062] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block019Part006 : ℚ :=
  (102231913725 : ℚ) / 72037829914699264

def SurrogateDiagonalTailChunk000Sub001Block019Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9062
    = surrogateDiagTailX0RatChunk000Sub001Block019Part006

theorem surrogateDiagonalTailChunk000Sub001Block019Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block019Part006CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block019Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block019Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block019Part006CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block019Part006SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block019Part006] using hcert

def TailChunk000Sub001Block019Part007SupportExplicit : Finset ℕ :=
  ([9066] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block019Part007 : ℚ :=
  (39933581287 : ℚ) / 8319833249923200

def SurrogateDiagonalTailChunk000Sub001Block019Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9066
    = surrogateDiagTailX0RatChunk000Sub001Block019Part007

theorem surrogateDiagonalTailChunk000Sub001Block019Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block019Part007CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block019Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block019Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block019Part007CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block019Part007SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block019Part007] using hcert

def TailChunk000Sub001Block019Part008SupportExplicit : Finset ℕ :=
  ([9067] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block019Part008 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block019Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9067
    = surrogateDiagTailX0RatChunk000Sub001Block019Part008

theorem surrogateDiagonalTailChunk000Sub001Block019Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block019Part008CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block019Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block019Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block019Part008CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block019Part008SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block019Part008] using hcert

def TailChunk000Sub001Block019Part009SupportExplicit : Finset ℕ :=
  ([9069] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block019Part009 : ℚ :=
  (570978505325 : ℚ) / 1668378889261161024

def SurrogateDiagonalTailChunk000Sub001Block019Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9069
    = surrogateDiagTailX0RatChunk000Sub001Block019Part009

theorem surrogateDiagonalTailChunk000Sub001Block019Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block019Part009CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block019Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block019Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block019Part009CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block019Part009SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block019Part009] using hcert

def TailChunk000Sub001Block019Part010SupportExplicit : Finset ℕ :=
  ([9070] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block019Part010 : ℚ :=
  (513750104375 : ℚ) / 215650077838009344

def SurrogateDiagonalTailChunk000Sub001Block019Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9070
    = surrogateDiagTailX0RatChunk000Sub001Block019Part010

theorem surrogateDiagonalTailChunk000Sub001Block019Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block019Part010CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block019Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block019Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block019Part010CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block019Part010SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block019Part010] using hcert

def TailChunk000Sub001Block019Part011SupportExplicit : Finset ℕ :=
  ([9071] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block019Part011 : ℚ :=
  (36964641425 : ℚ) / 7607344867043180544

def SurrogateDiagonalTailChunk000Sub001Block019Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9071
    = surrogateDiagTailX0RatChunk000Sub001Block019Part011

theorem surrogateDiagonalTailChunk000Sub001Block019Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block019Part011CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block019Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block019Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block019Part011CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block019Part011SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block019Part011] using hcert

def TailChunk000Sub001Block019Part012SupportExplicit : Finset ℕ :=
  ([9073] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block019Part012 : ℚ :=
  (6505721 : ℚ) / 1245446055403200

def SurrogateDiagonalTailChunk000Sub001Block019Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9073
    = surrogateDiagTailX0RatChunk000Sub001Block019Part012

theorem surrogateDiagonalTailChunk000Sub001Block019Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block019Part012CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block019Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block019Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block019Part012CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block019Part012SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block019Part012] using hcert

def TailChunk000Sub001Block019Part013SupportExplicit : Finset ℕ :=
  ([9074] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block019Part013 : ℚ :=
  (1192313545225 : ℚ) / 760446768763404288

def SurrogateDiagonalTailChunk000Sub001Block019Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9074
    = surrogateDiagTailX0RatChunk000Sub001Block019Part013

theorem surrogateDiagonalTailChunk000Sub001Block019Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block019Part013CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block019Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block019Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block019Part013CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block019Part013SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block019Part013] using hcert

def TailChunk000Sub001Block019Part014SupportExplicit : Finset ℕ :=
  ([9077] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block019Part014 : ℚ :=
  (17630358625 : ℚ) / 2427314833705402368

def SurrogateDiagonalTailChunk000Sub001Block019Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9077
    = surrogateDiagTailX0RatChunk000Sub001Block019Part014

theorem surrogateDiagonalTailChunk000Sub001Block019Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block019Part014CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block019Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block019Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block019Part014CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block019Part014SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block019Part014] using hcert

def TailChunk000Sub001Block019Part015SupportExplicit : Finset ℕ :=
  ([9078] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block019Part015 : ℚ :=
  (161117925 : ℚ) / 31441308090368

def SurrogateDiagonalTailChunk000Sub001Block019Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9078
    = surrogateDiagTailX0RatChunk000Sub001Block019Part015

theorem surrogateDiagonalTailChunk000Sub001Block019Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block019Part015CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block019Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block019Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block019Part015CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block019Part015SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block019Part015] using hcert

def TailChunk000Sub001Block019Part016SupportExplicit : Finset ℕ :=
  ([9079] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block019Part016 : ℚ :=
  (421526490325 : ℚ) / 9142224179377471488

def SurrogateDiagonalTailChunk000Sub001Block019Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9079
    = surrogateDiagTailX0RatChunk000Sub001Block019Part016

theorem surrogateDiagonalTailChunk000Sub001Block019Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block019Part016CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block019Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block019Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block019Part016CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block019Part016SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block019Part016] using hcert

def TailChunk000Sub001Block019Part017SupportExplicit : Finset ℕ :=
  ([9082] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block019Part017 : ℚ :=
  (1220149478425 : ℚ) / 842218365626967168

def SurrogateDiagonalTailChunk000Sub001Block019Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9082
    = surrogateDiagTailX0RatChunk000Sub001Block019Part017

theorem surrogateDiagonalTailChunk000Sub001Block019Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block019Part017CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block019Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block019Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block019Part017CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block019Part017SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block019Part017] using hcert

def TailChunk000Sub001Block019Part018SupportExplicit : Finset ℕ :=
  ([9083] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block019Part018 : ℚ :=
  (265764779 : ℚ) / 39265579904071680

def SurrogateDiagonalTailChunk000Sub001Block019Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9083
    = surrogateDiagTailX0RatChunk000Sub001Block019Part018

theorem surrogateDiagonalTailChunk000Sub001Block019Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block019Part018CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block019Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block019Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block019Part018CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block019Part018SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block019Part018] using hcert

def TailChunk000Sub001Block019Part019SupportExplicit : Finset ℕ :=
  ([9085] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block019Part019 : ℚ :=
  (492987596875 : ℚ) / 5550549221201707008

def SurrogateDiagonalTailChunk000Sub001Block019Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9085
    = surrogateDiagTailX0RatChunk000Sub001Block019Part019

theorem surrogateDiagonalTailChunk000Sub001Block019Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block019Part019CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block019Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block019Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block019Part019CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block019Part019SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block019Part019] using hcert

def TailChunk000Sub001Block019Part020SupportExplicit : Finset ℕ :=
  ([9086] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block019Part020 : ℚ :=
  (40795149109 : ℚ) / 14669112051763200

def SurrogateDiagonalTailChunk000Sub001Block019Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9086
    = surrogateDiagTailX0RatChunk000Sub001Block019Part020

theorem surrogateDiagonalTailChunk000Sub001Block019Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block019Part020CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block019Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block019Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block019Part020CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block019Part020SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block019Part020] using hcert

def TailChunk000Sub001Block019Part021SupportExplicit : Finset ℕ :=
  ([9087] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block019Part021 : ℚ :=
  (633220261975 : ℚ) / 2403387318560882688

def SurrogateDiagonalTailChunk000Sub001Block019Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9087
    = surrogateDiagTailX0RatChunk000Sub001Block019Part021

theorem surrogateDiagonalTailChunk000Sub001Block019Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block019Part021CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block019Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block019Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block019Part021CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block019Part021SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block019Part021] using hcert

def TailChunk000Sub001Block019Part022SupportExplicit : Finset ℕ :=
  ([9089] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block019Part022 : ℚ :=
  (433289611 : ℚ) / 103654333377331200

def SurrogateDiagonalTailChunk000Sub001Block019Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9089
    = surrogateDiagTailX0RatChunk000Sub001Block019Part022

theorem surrogateDiagonalTailChunk000Sub001Block019Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block019Part022CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block019Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block019Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block019Part022CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block019Part022SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block019Part022] using hcert

def TailChunk000Sub001Block019Part023SupportExplicit : Finset ℕ :=
  ([9091] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block019Part023 : ℚ :=
  (2066157025 : ℚ) / 6828768390191922

def SurrogateDiagonalTailChunk000Sub001Block019Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9091
    = surrogateDiagTailX0RatChunk000Sub001Block019Part023

theorem surrogateDiagonalTailChunk000Sub001Block019Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block019Part023CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block019Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block019Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block019Part023CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block019Part023SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block019Part023] using hcert

def TailChunk000Sub001Block019Part024SupportExplicit : Finset ℕ :=
  ([9093] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block019Part024 : ℚ :=
  (2325222574975 : ℚ) / 1805871442839994368

def SurrogateDiagonalTailChunk000Sub001Block019Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9093
    = surrogateDiagTailX0RatChunk000Sub001Block019Part024

theorem surrogateDiagonalTailChunk000Sub001Block019Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block019Part024CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block019Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block019Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block019Part024CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block019Part024SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block019Part024] using hcert

def surrogateDiagonalTailChunk000Sub001Block019HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block019Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block019Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block019Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block019Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block019Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block019Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block019Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block019Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block019Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block019Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block019Head : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block019Part000
    + surrogateDiagTailX0RatChunk000Sub001Block019Part001
    + surrogateDiagTailX0RatChunk000Sub001Block019Part002
    + surrogateDiagTailX0RatChunk000Sub001Block019Part003
    + surrogateDiagTailX0RatChunk000Sub001Block019Part004
    + surrogateDiagTailX0RatChunk000Sub001Block019Part005
    + surrogateDiagTailX0RatChunk000Sub001Block019Part006
    + surrogateDiagTailX0RatChunk000Sub001Block019Part007
    + surrogateDiagTailX0RatChunk000Sub001Block019Part008
    + surrogateDiagTailX0RatChunk000Sub001Block019Part009

def surrogateDiagonalTailChunk000Sub001Block019MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block019Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block019Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block019Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block019Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block019Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block019Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block019Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block019Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block019Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block019Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block019Mid : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block019Part010
    + surrogateDiagTailX0RatChunk000Sub001Block019Part011
    + surrogateDiagTailX0RatChunk000Sub001Block019Part012
    + surrogateDiagTailX0RatChunk000Sub001Block019Part013
    + surrogateDiagTailX0RatChunk000Sub001Block019Part014
    + surrogateDiagTailX0RatChunk000Sub001Block019Part015
    + surrogateDiagTailX0RatChunk000Sub001Block019Part016
    + surrogateDiagTailX0RatChunk000Sub001Block019Part017
    + surrogateDiagTailX0RatChunk000Sub001Block019Part018
    + surrogateDiagTailX0RatChunk000Sub001Block019Part019

def surrogateDiagonalTailChunk000Sub001Block019TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block019Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block019Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block019Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block019Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block019Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block019Tail : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block019Part020
    + surrogateDiagTailX0RatChunk000Sub001Block019Part021
    + surrogateDiagTailX0RatChunk000Sub001Block019Part022
    + surrogateDiagTailX0RatChunk000Sub001Block019Part023
    + surrogateDiagTailX0RatChunk000Sub001Block019Part024

def surrogateDiagonalTailChunk000Sub001Block019Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub001Block019HeadSum X0
    + surrogateDiagonalTailChunk000Sub001Block019MidSum X0
    + surrogateDiagonalTailChunk000Sub001Block019TailSum X0

def surrogateDiagTailX0RatChunk000Sub001Block019 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block019Part000
    + surrogateDiagTailX0RatChunk000Sub001Block019Part001
    + surrogateDiagTailX0RatChunk000Sub001Block019Part002
    + surrogateDiagTailX0RatChunk000Sub001Block019Part003
    + surrogateDiagTailX0RatChunk000Sub001Block019Part004
    + surrogateDiagTailX0RatChunk000Sub001Block019Part005
    + surrogateDiagTailX0RatChunk000Sub001Block019Part006
    + surrogateDiagTailX0RatChunk000Sub001Block019Part007
    + surrogateDiagTailX0RatChunk000Sub001Block019Part008
    + surrogateDiagTailX0RatChunk000Sub001Block019Part009
    + surrogateDiagTailX0RatChunk000Sub001Block019Part010
    + surrogateDiagTailX0RatChunk000Sub001Block019Part011
    + surrogateDiagTailX0RatChunk000Sub001Block019Part012
    + surrogateDiagTailX0RatChunk000Sub001Block019Part013
    + surrogateDiagTailX0RatChunk000Sub001Block019Part014
    + surrogateDiagTailX0RatChunk000Sub001Block019Part015
    + surrogateDiagTailX0RatChunk000Sub001Block019Part016
    + surrogateDiagTailX0RatChunk000Sub001Block019Part017
    + surrogateDiagTailX0RatChunk000Sub001Block019Part018
    + surrogateDiagTailX0RatChunk000Sub001Block019Part019
    + surrogateDiagTailX0RatChunk000Sub001Block019Part020
    + surrogateDiagTailX0RatChunk000Sub001Block019Part021
    + surrogateDiagTailX0RatChunk000Sub001Block019Part022
    + surrogateDiagTailX0RatChunk000Sub001Block019Part023
    + surrogateDiagTailX0RatChunk000Sub001Block019Part024

theorem surrogateDiagTailX0RatChunk000Sub001Block019_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk000Sub001Block019Head + surrogateDiagTailX0RatChunk000Sub001Block019Mid + surrogateDiagTailX0RatChunk000Sub001Block019Tail =
      surrogateDiagTailX0RatChunk000Sub001Block019 := by
  unfold surrogateDiagTailX0RatChunk000Sub001Block019Head surrogateDiagTailX0RatChunk000Sub001Block019Mid surrogateDiagTailX0RatChunk000Sub001Block019Tail surrogateDiagTailX0RatChunk000Sub001Block019
  ring

def SurrogateDiagonalTailChunk000Sub001Block019HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block019HeadSum X0 = surrogateDiagTailX0RatChunk000Sub001Block019Head

def SurrogateDiagonalTailChunk000Sub001Block019MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block019MidSum X0 = surrogateDiagTailX0RatChunk000Sub001Block019Mid

def SurrogateDiagonalTailChunk000Sub001Block019TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block019TailSum X0 = surrogateDiagTailX0RatChunk000Sub001Block019Tail

theorem surrogateDiagonalTailChunk000Sub001Block019_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk000Sub001Block019HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk000Sub001Block019MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk000Sub001Block019TailCertificateAt X0) :
    surrogateDiagonalTailChunk000Sub001Block019Sum X0 = surrogateDiagTailX0RatChunk000Sub001Block019 := by
  unfold SurrogateDiagonalTailChunk000Sub001Block019HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk000Sub001Block019MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk000Sub001Block019TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk000Sub001Block019Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk000Sub001Block019_eq_head_add_mid_add_tail

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0TailPilot25

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

open scoped BigOperators

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

/- Generated direct-term certificate blocks for tail chunk 001, subchunk 000, blocks [10,20). -/

/-- Block 010 covers tail-support indices [10250,10275) and q from 16907 to 16945. -/

def TailChunk001Sub000Block010Part000SupportExplicit : Finset ℕ :=
  ([16907] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block010Part000 : ℚ :=
  (25356453 : ℚ) / 4368345451724800

def SurrogateDiagonalTailChunk001Sub000Block010Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16907
    = surrogateDiagTailX0RatChunk001Sub000Block010Part000

theorem surrogateDiagonalTailChunk001Sub000Block010Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block010Part000CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block010Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block010Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block010Part000CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block010Part000SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block010Part000] using hcert

def TailChunk001Sub000Block010Part001SupportExplicit : Finset ℕ :=
  ([16909] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block010Part001 : ℚ :=
  (153910145875 : ℚ) / 181591799616011501568

def SurrogateDiagonalTailChunk001Sub000Block010Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16909
    = surrogateDiagTailX0RatChunk001Sub000Block010Part001

theorem surrogateDiagonalTailChunk001Sub000Block010Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block010Part001CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block010Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block010Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block010Part001CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block010Part001SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block010Part001] using hcert

def TailChunk001Sub000Block010Part002SupportExplicit : Finset ℕ :=
  ([16910] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block010Part002 : ℚ :=
  (598503765775 : ℚ) / 4029837493464465408

def SurrogateDiagonalTailChunk001Sub000Block010Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16910
    = surrogateDiagTailX0RatChunk001Sub000Block010Part002

theorem surrogateDiagonalTailChunk001Sub000Block010Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block010Part002CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block010Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block010Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block010Part002CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block010Part002SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block010Part002] using hcert

def TailChunk001Sub000Block010Part003SupportExplicit : Finset ℕ :=
  ([16913] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block010Part003 : ℚ :=
  (2839996399 : ℚ) / 987265573632000000

def SurrogateDiagonalTailChunk001Sub000Block010Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16913
    = surrogateDiagTailX0RatChunk001Sub000Block010Part003

theorem surrogateDiagonalTailChunk001Sub000Block010Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block010Part003CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block010Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block010Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block010Part003CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block010Part003SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block010Part003] using hcert

def TailChunk001Sub000Block010Part004SupportExplicit : Finset ℕ :=
  ([16914] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block010Part004 : ℚ :=
  (496533407525 : ℚ) / 1261481253469053504

def SurrogateDiagonalTailChunk001Sub000Block010Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16914
    = surrogateDiagTailX0RatChunk001Sub000Block010Part004

theorem surrogateDiagonalTailChunk001Sub000Block010Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block010Part004CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block010Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block010Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block010Part004CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block010Part004SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block010Part004] using hcert

def TailChunk001Sub000Block010Part005SupportExplicit : Finset ℕ :=
  ([16915] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block010Part005 : ℚ :=
  (137671289375 : ℚ) / 5861581808675586048

def SurrogateDiagonalTailChunk001Sub000Block010Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16915
    = surrogateDiagTailX0RatChunk001Sub000Block010Part005

theorem surrogateDiagonalTailChunk001Sub000Block010Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block010Part005CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block010Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block010Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block010Part005CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block010Part005SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block010Part005] using hcert

def TailChunk001Sub000Block010Part006SupportExplicit : Finset ℕ :=
  ([16917] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block010Part006 : ℚ :=
  (993657648275 : ℚ) / 20212364989823751744

def SurrogateDiagonalTailChunk001Sub000Block010Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16917
    = surrogateDiagTailX0RatChunk001Sub000Block010Part006

theorem surrogateDiagonalTailChunk001Sub000Block010Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block010Part006CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block010Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block010Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block010Part006CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block010Part006SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block010Part006] using hcert

def TailChunk001Sub000Block010Part007SupportExplicit : Finset ℕ :=
  ([16918] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block010Part007 : ℚ :=
  (896359153 : ℚ) / 34796192944619520

def SurrogateDiagonalTailChunk001Sub000Block010Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16918
    = surrogateDiagTailX0RatChunk001Sub000Block010Part007

theorem surrogateDiagonalTailChunk001Sub000Block010Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block010Part007CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block010Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block010Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block010Part007CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block010Part007SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block010Part007] using hcert

def TailChunk001Sub000Block010Part008SupportExplicit : Finset ℕ :=
  ([16919] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block010Part008 : ℚ :=
  (365680440875 : ℚ) / 55206419926530392064

def SurrogateDiagonalTailChunk001Sub000Block010Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16919
    = surrogateDiagTailX0RatChunk001Sub000Block010Part008

theorem surrogateDiagonalTailChunk001Sub000Block010Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block010Part008CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block010Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block010Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block010Part008CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block010Part008SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block010Part008] using hcert

def TailChunk001Sub000Block010Part009SupportExplicit : Finset ℕ :=
  ([16921] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block010Part009 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block010Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16921
    = surrogateDiagTailX0RatChunk001Sub000Block010Part009

theorem surrogateDiagonalTailChunk001Sub000Block010Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block010Part009CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block010Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block010Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block010Part009CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block010Part009SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block010Part009] using hcert

def TailChunk001Sub000Block010Part010SupportExplicit : Finset ℕ :=
  ([16922] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block010Part010 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block010Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16922
    = surrogateDiagTailX0RatChunk001Sub000Block010Part010

theorem surrogateDiagonalTailChunk001Sub000Block010Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block010Part010CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block010Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block010Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block010Part010CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block010Part010SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block010Part010] using hcert

def TailChunk001Sub000Block010Part011SupportExplicit : Finset ℕ :=
  ([16923] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block010Part011 : ℚ :=
  (3977450093 : ℚ) / 80964241783234560

def SurrogateDiagonalTailChunk001Sub000Block010Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16923
    = surrogateDiagTailX0RatChunk001Sub000Block010Part011

theorem surrogateDiagonalTailChunk001Sub000Block010Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block010Part011CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block010Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block010Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block010Part011CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block010Part011SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block010Part011] using hcert

def TailChunk001Sub000Block010Part012SupportExplicit : Finset ℕ :=
  ([16926] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block010Part012 : ℚ :=
  (7300878083 : ℚ) / 6967096615895040

def SurrogateDiagonalTailChunk001Sub000Block010Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16926
    = surrogateDiagTailX0RatChunk001Sub000Block010Part012

theorem surrogateDiagonalTailChunk001Sub000Block010Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block010Part012CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block010Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block010Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block010Part012CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block010Part012SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block010Part012] using hcert

def TailChunk001Sub000Block010Part013SupportExplicit : Finset ℕ :=
  ([16927] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block010Part013 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block010Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16927
    = surrogateDiagTailX0RatChunk001Sub000Block010Part013

theorem surrogateDiagonalTailChunk001Sub000Block010Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block010Part013CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block010Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block010Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block010Part013CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block010Part013SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block010Part013] using hcert

def TailChunk001Sub000Block010Part014SupportExplicit : Finset ℕ :=
  ([16930] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block010Part014 : ℚ :=
  (268911229475 : ℚ) / 2623241433776799744

def SurrogateDiagonalTailChunk001Sub000Block010Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16930
    = surrogateDiagTailX0RatChunk001Sub000Block010Part014

theorem surrogateDiagonalTailChunk001Sub000Block010Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block010Part014CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block010Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block010Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block010Part014CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block010Part014SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block010Part014] using hcert

def TailChunk001Sub000Block010Part015SupportExplicit : Finset ℕ :=
  ([16931] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block010Part015 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block010Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16931
    = surrogateDiagTailX0RatChunk001Sub000Block010Part015

theorem surrogateDiagonalTailChunk001Sub000Block010Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block010Part015CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block010Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block010Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block010Part015CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block010Part015SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block010Part015] using hcert

def TailChunk001Sub000Block010Part016SupportExplicit : Finset ℕ :=
  ([16933] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block010Part016 : ℚ :=
  (3785568799 : ℚ) / 417254742805708800

def SurrogateDiagonalTailChunk001Sub000Block010Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16933
    = surrogateDiagTailX0RatChunk001Sub000Block010Part016

theorem surrogateDiagonalTailChunk001Sub000Block010Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block010Part016CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block010Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block010Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block010Part016CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block010Part016SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block010Part016] using hcert

def TailChunk001Sub000Block010Part017SupportExplicit : Finset ℕ :=
  ([16934] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block010Part017 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block010Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16934
    = surrogateDiagTailX0RatChunk001Sub000Block010Part017

theorem surrogateDiagonalTailChunk001Sub000Block010Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block010Part017CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block010Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block010Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block010Part017CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block010Part017SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block010Part017] using hcert

def TailChunk001Sub000Block010Part018SupportExplicit : Finset ℕ :=
  ([16935] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block010Part018 : ℚ :=
  (517491157075 : ℚ) / 4145369179301609472

def SurrogateDiagonalTailChunk001Sub000Block010Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16935
    = surrogateDiagTailX0RatChunk001Sub000Block010Part018

theorem surrogateDiagonalTailChunk001Sub000Block010Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block010Part018CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block010Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block010Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block010Part018CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block010Part018SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block010Part018] using hcert

def TailChunk001Sub000Block010Part019SupportExplicit : Finset ℕ :=
  ([16937] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block010Part019 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block010Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16937
    = surrogateDiagTailX0RatChunk001Sub000Block010Part019

theorem surrogateDiagonalTailChunk001Sub000Block010Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block010Part019CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block010Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block010Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block010Part019CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block010Part019SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block010Part019] using hcert

def TailChunk001Sub000Block010Part020SupportExplicit : Finset ℕ :=
  ([16939] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block010Part020 : ℚ :=
  (213649838825 : ℚ) / 74501631660749497344

def SurrogateDiagonalTailChunk001Sub000Block010Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16939
    = surrogateDiagTailX0RatChunk001Sub000Block010Part020

theorem surrogateDiagonalTailChunk001Sub000Block010Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block010Part020CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block010Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block010Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block010Part020CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block010Part020SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block010Part020] using hcert

def TailChunk001Sub000Block010Part021SupportExplicit : Finset ℕ :=
  ([16941] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block010Part021 : ℚ :=
  (996478648175 : ℚ) / 20327330160378575424

def SurrogateDiagonalTailChunk001Sub000Block010Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16941
    = surrogateDiagTailX0RatChunk001Sub000Block010Part021

theorem surrogateDiagonalTailChunk001Sub000Block010Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block010Part021CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block010Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block010Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block010Part021CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block010Part021SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block010Part021] using hcert

def TailChunk001Sub000Block010Part022SupportExplicit : Finset ℕ :=
  ([16942] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block010Part022 : ℚ :=
  (72935682775 : ℚ) / 11482813359448639488

def SurrogateDiagonalTailChunk001Sub000Block010Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16942
    = surrogateDiagTailX0RatChunk001Sub000Block010Part022

theorem surrogateDiagonalTailChunk001Sub000Block010Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block010Part022CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block010Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block010Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block010Part022CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block010Part022SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block010Part022] using hcert

def TailChunk001Sub000Block010Part023SupportExplicit : Finset ℕ :=
  ([16943] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block010Part023 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block010Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16943
    = surrogateDiagTailX0RatChunk001Sub000Block010Part023

theorem surrogateDiagonalTailChunk001Sub000Block010Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block010Part023CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block010Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block010Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block010Part023CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block010Part023SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block010Part023] using hcert

def TailChunk001Sub000Block010Part024SupportExplicit : Finset ℕ :=
  ([16945] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block010Part024 : ℚ :=
  (1435781144725 : ℚ) / 84341327202821111808

def SurrogateDiagonalTailChunk001Sub000Block010Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16945
    = surrogateDiagTailX0RatChunk001Sub000Block010Part024

theorem surrogateDiagonalTailChunk001Sub000Block010Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block010Part024CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block010Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block010Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block010Part024CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block010Part024SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block010Part024] using hcert

def surrogateDiagonalTailChunk001Sub000Block010HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block010Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block010Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block010Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block010Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block010Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block010Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block010Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block010Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block010Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block010Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block010Head : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block010Part000
    + surrogateDiagTailX0RatChunk001Sub000Block010Part001
    + surrogateDiagTailX0RatChunk001Sub000Block010Part002
    + surrogateDiagTailX0RatChunk001Sub000Block010Part003
    + surrogateDiagTailX0RatChunk001Sub000Block010Part004
    + surrogateDiagTailX0RatChunk001Sub000Block010Part005
    + surrogateDiagTailX0RatChunk001Sub000Block010Part006
    + surrogateDiagTailX0RatChunk001Sub000Block010Part007
    + surrogateDiagTailX0RatChunk001Sub000Block010Part008
    + surrogateDiagTailX0RatChunk001Sub000Block010Part009

def surrogateDiagonalTailChunk001Sub000Block010MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block010Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block010Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block010Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block010Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block010Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block010Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block010Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block010Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block010Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block010Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block010Mid : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block010Part010
    + surrogateDiagTailX0RatChunk001Sub000Block010Part011
    + surrogateDiagTailX0RatChunk001Sub000Block010Part012
    + surrogateDiagTailX0RatChunk001Sub000Block010Part013
    + surrogateDiagTailX0RatChunk001Sub000Block010Part014
    + surrogateDiagTailX0RatChunk001Sub000Block010Part015
    + surrogateDiagTailX0RatChunk001Sub000Block010Part016
    + surrogateDiagTailX0RatChunk001Sub000Block010Part017
    + surrogateDiagTailX0RatChunk001Sub000Block010Part018
    + surrogateDiagTailX0RatChunk001Sub000Block010Part019

def surrogateDiagonalTailChunk001Sub000Block010TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block010Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block010Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block010Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block010Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block010Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block010Tail : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block010Part020
    + surrogateDiagTailX0RatChunk001Sub000Block010Part021
    + surrogateDiagTailX0RatChunk001Sub000Block010Part022
    + surrogateDiagTailX0RatChunk001Sub000Block010Part023
    + surrogateDiagTailX0RatChunk001Sub000Block010Part024

def surrogateDiagonalTailChunk001Sub000Block010Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk001Sub000Block010HeadSum X0
    + surrogateDiagonalTailChunk001Sub000Block010MidSum X0
    + surrogateDiagonalTailChunk001Sub000Block010TailSum X0

def surrogateDiagTailX0RatChunk001Sub000Block010 : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block010Part000
    + surrogateDiagTailX0RatChunk001Sub000Block010Part001
    + surrogateDiagTailX0RatChunk001Sub000Block010Part002
    + surrogateDiagTailX0RatChunk001Sub000Block010Part003
    + surrogateDiagTailX0RatChunk001Sub000Block010Part004
    + surrogateDiagTailX0RatChunk001Sub000Block010Part005
    + surrogateDiagTailX0RatChunk001Sub000Block010Part006
    + surrogateDiagTailX0RatChunk001Sub000Block010Part007
    + surrogateDiagTailX0RatChunk001Sub000Block010Part008
    + surrogateDiagTailX0RatChunk001Sub000Block010Part009
    + surrogateDiagTailX0RatChunk001Sub000Block010Part010
    + surrogateDiagTailX0RatChunk001Sub000Block010Part011
    + surrogateDiagTailX0RatChunk001Sub000Block010Part012
    + surrogateDiagTailX0RatChunk001Sub000Block010Part013
    + surrogateDiagTailX0RatChunk001Sub000Block010Part014
    + surrogateDiagTailX0RatChunk001Sub000Block010Part015
    + surrogateDiagTailX0RatChunk001Sub000Block010Part016
    + surrogateDiagTailX0RatChunk001Sub000Block010Part017
    + surrogateDiagTailX0RatChunk001Sub000Block010Part018
    + surrogateDiagTailX0RatChunk001Sub000Block010Part019
    + surrogateDiagTailX0RatChunk001Sub000Block010Part020
    + surrogateDiagTailX0RatChunk001Sub000Block010Part021
    + surrogateDiagTailX0RatChunk001Sub000Block010Part022
    + surrogateDiagTailX0RatChunk001Sub000Block010Part023
    + surrogateDiagTailX0RatChunk001Sub000Block010Part024

theorem surrogateDiagTailX0RatChunk001Sub000Block010_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk001Sub000Block010Head + surrogateDiagTailX0RatChunk001Sub000Block010Mid + surrogateDiagTailX0RatChunk001Sub000Block010Tail =
      surrogateDiagTailX0RatChunk001Sub000Block010 := by
  unfold surrogateDiagTailX0RatChunk001Sub000Block010Head surrogateDiagTailX0RatChunk001Sub000Block010Mid surrogateDiagTailX0RatChunk001Sub000Block010Tail surrogateDiagTailX0RatChunk001Sub000Block010
  ring

def SurrogateDiagonalTailChunk001Sub000Block010HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block010HeadSum X0 = surrogateDiagTailX0RatChunk001Sub000Block010Head

def SurrogateDiagonalTailChunk001Sub000Block010MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block010MidSum X0 = surrogateDiagTailX0RatChunk001Sub000Block010Mid

def SurrogateDiagonalTailChunk001Sub000Block010TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block010TailSum X0 = surrogateDiagTailX0RatChunk001Sub000Block010Tail

theorem surrogateDiagonalTailChunk001Sub000Block010_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk001Sub000Block010HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk001Sub000Block010MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk001Sub000Block010TailCertificateAt X0) :
    surrogateDiagonalTailChunk001Sub000Block010Sum X0 = surrogateDiagTailX0RatChunk001Sub000Block010 := by
  unfold SurrogateDiagonalTailChunk001Sub000Block010HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk001Sub000Block010MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk001Sub000Block010TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk001Sub000Block010Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk001Sub000Block010_eq_head_add_mid_add_tail

/-- Block 011 covers tail-support indices [10275,10300) and q from 16946 to 16989. -/

def TailChunk001Sub000Block011Part000SupportExplicit : Finset ℕ :=
  ([16946] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block011Part000 : ℚ :=
  (2168836325 : ℚ) / 298670723052650496

def SurrogateDiagonalTailChunk001Sub000Block011Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16946
    = surrogateDiagTailX0RatChunk001Sub000Block011Part000

theorem surrogateDiagonalTailChunk001Sub000Block011Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block011Part000CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block011Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block011Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block011Part000CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block011Part000SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block011Part000] using hcert

def TailChunk001Sub000Block011Part001SupportExplicit : Finset ℕ :=
  ([16949] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block011Part001 : ℚ :=
  (314755621525 : ℚ) / 161266493588250820608

def SurrogateDiagonalTailChunk001Sub000Block011Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16949
    = surrogateDiagTailX0RatChunk001Sub000Block011Part001

theorem surrogateDiagonalTailChunk001Sub000Block011Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block011Part001CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block011Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block011Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block011Part001CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block011Part001SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block011Part001] using hcert

def TailChunk001Sub000Block011Part002SupportExplicit : Finset ℕ :=
  ([16951] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block011Part002 : ℚ :=
  (13454668637 : ℚ) / 2222917372783641600

def SurrogateDiagonalTailChunk001Sub000Block011Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16951
    = surrogateDiagTailX0RatChunk001Sub000Block011Part002

theorem surrogateDiagonalTailChunk001Sub000Block011Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block011Part002CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block011Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block011Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block011Part002CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block011Part002SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block011Part002] using hcert

def TailChunk001Sub000Block011Part003SupportExplicit : Finset ℕ :=
  ([16953] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block011Part003 : ℚ :=
  (1596625037 : ℚ) / 32615994094440000

def SurrogateDiagonalTailChunk001Sub000Block011Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16953
    = surrogateDiagTailX0RatChunk001Sub000Block011Part003

theorem surrogateDiagonalTailChunk001Sub000Block011Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block011Part003CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block011Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block011Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block011Part003CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block011Part003SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block011Part003] using hcert

def TailChunk001Sub000Block011Part004SupportExplicit : Finset ℕ :=
  ([16955] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block011Part004 : ℚ :=
  (5756056109 : ℚ) / 676325253542307840

def SurrogateDiagonalTailChunk001Sub000Block011Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16955
    = surrogateDiagTailX0RatChunk001Sub000Block011Part004

theorem surrogateDiagonalTailChunk001Sub000Block011Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block011Part004CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block011Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block011Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block011Part004CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block011Part004SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block011Part004] using hcert

def TailChunk001Sub000Block011Part005SupportExplicit : Finset ℕ :=
  ([16957] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block011Part005 : ℚ :=
  (7071285103 : ℚ) / 7200164850957187200

def SurrogateDiagonalTailChunk001Sub000Block011Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16957
    = surrogateDiagTailX0RatChunk001Sub000Block011Part005

theorem surrogateDiagonalTailChunk001Sub000Block011Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block011Part005CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block011Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block011Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block011Part005CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block011Part005SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block011Part005] using hcert

def TailChunk001Sub000Block011Part006SupportExplicit : Finset ℕ :=
  ([16958] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block011Part006 : ℚ :=
  (9657349243 : ℚ) / 26117745896678400

def SurrogateDiagonalTailChunk001Sub000Block011Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16958
    = surrogateDiagTailX0RatChunk001Sub000Block011Part006

theorem surrogateDiagonalTailChunk001Sub000Block011Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block011Part006CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block011Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block011Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block011Part006CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block011Part006SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block011Part006] using hcert

def TailChunk001Sub000Block011Part007SupportExplicit : Finset ℕ :=
  ([16959] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block011Part007 : ℚ :=
  (249649255775 : ℚ) / 5103468837523650816

def SurrogateDiagonalTailChunk001Sub000Block011Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16959
    = surrogateDiagTailX0RatChunk001Sub000Block011Part007

theorem surrogateDiagonalTailChunk001Sub000Block011Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block011Part007CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block011Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block011Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block011Part007CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block011Part007SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block011Part007] using hcert

def TailChunk001Sub000Block011Part008SupportExplicit : Finset ℕ :=
  ([16961] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block011Part008 : ℚ :=
  (367494328175 : ℚ) / 55756874367035118144

def SurrogateDiagonalTailChunk001Sub000Block011Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16961
    = surrogateDiagTailX0RatChunk001Sub000Block011Part008

theorem surrogateDiagonalTailChunk001Sub000Block011Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block011Part008CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block011Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block011Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block011Part008CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block011Part008SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block011Part008] using hcert

def TailChunk001Sub000Block011Part009SupportExplicit : Finset ℕ :=
  ([16962] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block011Part009 : ℚ :=
  (87424788241 : ℚ) / 68733220631347200

def SurrogateDiagonalTailChunk001Sub000Block011Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16962
    = surrogateDiagTailX0RatChunk001Sub000Block011Part009

theorem surrogateDiagonalTailChunk001Sub000Block011Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block011Part009CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block011Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block011Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block011Part009CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block011Part009SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block011Part009] using hcert

def TailChunk001Sub000Block011Part010SupportExplicit : Finset ℕ :=
  ([16963] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block011Part010 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block011Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16963
    = surrogateDiagTailX0RatChunk001Sub000Block011Part010

theorem surrogateDiagonalTailChunk001Sub000Block011Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block011Part010CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block011Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block011Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block011Part010CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block011Part010SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block011Part010] using hcert

def TailChunk001Sub000Block011Part011SupportExplicit : Finset ℕ :=
  ([16966] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block011Part011 : ℚ :=
  (4113217609375 : ℚ) / 10079155849265676288

def SurrogateDiagonalTailChunk001Sub000Block011Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16966
    = surrogateDiagTailX0RatChunk001Sub000Block011Part011

theorem surrogateDiagonalTailChunk001Sub000Block011Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block011Part011CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block011Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block011Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block011Part011CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block011Part011SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block011Part011] using hcert

def TailChunk001Sub000Block011Part012SupportExplicit : Finset ℕ :=
  ([16969] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block011Part012 : ℚ :=
  (246096093 : ℚ) / 513683456757188480

def SurrogateDiagonalTailChunk001Sub000Block011Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16969
    = surrogateDiagTailX0RatChunk001Sub000Block011Part012

theorem surrogateDiagonalTailChunk001Sub000Block011Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block011Part012CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block011Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block011Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block011Part012CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block011Part012SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block011Part012] using hcert

def TailChunk001Sub000Block011Part013SupportExplicit : Finset ℕ :=
  ([16970] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block011Part013 : ℚ :=
  (1079240555775 : ℚ) / 1765423735222829056

def SurrogateDiagonalTailChunk001Sub000Block011Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16970
    = surrogateDiagTailX0RatChunk001Sub000Block011Part013

theorem surrogateDiagonalTailChunk001Sub000Block011Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block011Part013CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block011Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block011Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block011Part013CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block011Part013SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block011Part013] using hcert

def TailChunk001Sub000Block011Part014SupportExplicit : Finset ℕ :=
  ([16971] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block011Part014 : ℚ :=
  (71429323075 : ℚ) / 1462266105303392256

def SurrogateDiagonalTailChunk001Sub000Block011Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16971
    = surrogateDiagTailX0RatChunk001Sub000Block011Part014

theorem surrogateDiagonalTailChunk001Sub000Block011Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block011Part014CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block011Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block011Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block011Part014CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block011Part014SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block011Part014] using hcert

def TailChunk001Sub000Block011Part015SupportExplicit : Finset ℕ :=
  ([16973] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block011Part015 : ℚ :=
  (17951196823 : ℚ) / 5654892392023939200

def SurrogateDiagonalTailChunk001Sub000Block011Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16973
    = surrogateDiagTailX0RatChunk001Sub000Block011Part015

theorem surrogateDiagonalTailChunk001Sub000Block011Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block011Part015CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block011Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block011Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block011Part015CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block011Part015SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block011Part015] using hcert

def TailChunk001Sub000Block011Part016SupportExplicit : Finset ℕ :=
  ([16977] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block011Part016 : ℚ :=
  (1000717648025 : ℚ) / 20500696600762181184

def SurrogateDiagonalTailChunk001Sub000Block011Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16977
    = surrogateDiagTailX0RatChunk001Sub000Block011Part016

theorem surrogateDiagonalTailChunk001Sub000Block011Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block011Part016CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block011Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block011Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block011Part016CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block011Part016SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block011Part016] using hcert

def TailChunk001Sub000Block011Part017SupportExplicit : Finset ℕ :=
  ([16978] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block011Part017 : ℚ :=
  (167347219525 : ℚ) / 390419035556032512

def SurrogateDiagonalTailChunk001Sub000Block011Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16978
    = surrogateDiagTailX0RatChunk001Sub000Block011Part017

theorem surrogateDiagonalTailChunk001Sub000Block011Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block011Part017CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block011Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block011Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block011Part017CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block011Part017SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block011Part017] using hcert

def TailChunk001Sub000Block011Part018SupportExplicit : Finset ℕ :=
  ([16979] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block011Part018 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block011Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16979
    = surrogateDiagTailX0RatChunk001Sub000Block011Part018

theorem surrogateDiagonalTailChunk001Sub000Block011Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block011Part018CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block011Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block011Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block011Part018CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block011Part018SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block011Part018] using hcert

def TailChunk001Sub000Block011Part019SupportExplicit : Finset ℕ :=
  ([16981] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block011Part019 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block011Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16981
    = surrogateDiagTailX0RatChunk001Sub000Block011Part019

theorem surrogateDiagonalTailChunk001Sub000Block011Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block011Part019CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block011Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block011Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block011Part019CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block011Part019SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block011Part019] using hcert

def TailChunk001Sub000Block011Part020SupportExplicit : Finset ℕ :=
  ([16982] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block011Part020 : ℚ :=
  (199054093475 : ℚ) / 388481046197584896

def SurrogateDiagonalTailChunk001Sub000Block011Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16982
    = surrogateDiagTailX0RatChunk001Sub000Block011Part020

theorem surrogateDiagonalTailChunk001Sub000Block011Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block011Part020CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block011Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block011Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block011Part020CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block011Part020SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block011Part020] using hcert

def TailChunk001Sub000Block011Part021SupportExplicit : Finset ℕ :=
  ([16985] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block011Part021 : ℚ :=
  (8547193625 : ℚ) / 768017584102099968

def SurrogateDiagonalTailChunk001Sub000Block011Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16985
    = surrogateDiagTailX0RatChunk001Sub000Block011Part021

theorem surrogateDiagonalTailChunk001Sub000Block011Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block011Part021CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block011Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block011Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block011Part021CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block011Part021SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block011Part021] using hcert

def TailChunk001Sub000Block011Part022SupportExplicit : Finset ℕ :=
  ([16986] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block011Part022 : ℚ :=
  (385694996975 : ℚ) / 335840040142553088

def SurrogateDiagonalTailChunk001Sub000Block011Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16986
    = surrogateDiagTailX0RatChunk001Sub000Block011Part022

theorem surrogateDiagonalTailChunk001Sub000Block011Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block011Part022CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block011Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block011Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block011Part022CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block011Part022SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block011Part022] using hcert

def TailChunk001Sub000Block011Part023SupportExplicit : Finset ℕ :=
  ([16987] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block011Part023 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block011Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16987
    = surrogateDiagTailX0RatChunk001Sub000Block011Part023

theorem surrogateDiagonalTailChunk001Sub000Block011Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block011Part023CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block011Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block011Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block011Part023CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block011Part023SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block011Part023] using hcert

def TailChunk001Sub000Block011Part024SupportExplicit : Finset ℕ :=
  ([16989] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block011Part024 : ℚ :=
  (1921517374675 : ℚ) / 22100255072573718528

def SurrogateDiagonalTailChunk001Sub000Block011Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16989
    = surrogateDiagTailX0RatChunk001Sub000Block011Part024

theorem surrogateDiagonalTailChunk001Sub000Block011Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block011Part024CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block011Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block011Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block011Part024CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block011Part024SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block011Part024] using hcert

def surrogateDiagonalTailChunk001Sub000Block011HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block011Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block011Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block011Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block011Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block011Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block011Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block011Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block011Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block011Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block011Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block011Head : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block011Part000
    + surrogateDiagTailX0RatChunk001Sub000Block011Part001
    + surrogateDiagTailX0RatChunk001Sub000Block011Part002
    + surrogateDiagTailX0RatChunk001Sub000Block011Part003
    + surrogateDiagTailX0RatChunk001Sub000Block011Part004
    + surrogateDiagTailX0RatChunk001Sub000Block011Part005
    + surrogateDiagTailX0RatChunk001Sub000Block011Part006
    + surrogateDiagTailX0RatChunk001Sub000Block011Part007
    + surrogateDiagTailX0RatChunk001Sub000Block011Part008
    + surrogateDiagTailX0RatChunk001Sub000Block011Part009

def surrogateDiagonalTailChunk001Sub000Block011MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block011Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block011Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block011Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block011Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block011Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block011Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block011Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block011Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block011Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block011Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block011Mid : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block011Part010
    + surrogateDiagTailX0RatChunk001Sub000Block011Part011
    + surrogateDiagTailX0RatChunk001Sub000Block011Part012
    + surrogateDiagTailX0RatChunk001Sub000Block011Part013
    + surrogateDiagTailX0RatChunk001Sub000Block011Part014
    + surrogateDiagTailX0RatChunk001Sub000Block011Part015
    + surrogateDiagTailX0RatChunk001Sub000Block011Part016
    + surrogateDiagTailX0RatChunk001Sub000Block011Part017
    + surrogateDiagTailX0RatChunk001Sub000Block011Part018
    + surrogateDiagTailX0RatChunk001Sub000Block011Part019

def surrogateDiagonalTailChunk001Sub000Block011TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block011Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block011Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block011Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block011Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block011Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block011Tail : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block011Part020
    + surrogateDiagTailX0RatChunk001Sub000Block011Part021
    + surrogateDiagTailX0RatChunk001Sub000Block011Part022
    + surrogateDiagTailX0RatChunk001Sub000Block011Part023
    + surrogateDiagTailX0RatChunk001Sub000Block011Part024

def surrogateDiagonalTailChunk001Sub000Block011Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk001Sub000Block011HeadSum X0
    + surrogateDiagonalTailChunk001Sub000Block011MidSum X0
    + surrogateDiagonalTailChunk001Sub000Block011TailSum X0

def surrogateDiagTailX0RatChunk001Sub000Block011 : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block011Part000
    + surrogateDiagTailX0RatChunk001Sub000Block011Part001
    + surrogateDiagTailX0RatChunk001Sub000Block011Part002
    + surrogateDiagTailX0RatChunk001Sub000Block011Part003
    + surrogateDiagTailX0RatChunk001Sub000Block011Part004
    + surrogateDiagTailX0RatChunk001Sub000Block011Part005
    + surrogateDiagTailX0RatChunk001Sub000Block011Part006
    + surrogateDiagTailX0RatChunk001Sub000Block011Part007
    + surrogateDiagTailX0RatChunk001Sub000Block011Part008
    + surrogateDiagTailX0RatChunk001Sub000Block011Part009
    + surrogateDiagTailX0RatChunk001Sub000Block011Part010
    + surrogateDiagTailX0RatChunk001Sub000Block011Part011
    + surrogateDiagTailX0RatChunk001Sub000Block011Part012
    + surrogateDiagTailX0RatChunk001Sub000Block011Part013
    + surrogateDiagTailX0RatChunk001Sub000Block011Part014
    + surrogateDiagTailX0RatChunk001Sub000Block011Part015
    + surrogateDiagTailX0RatChunk001Sub000Block011Part016
    + surrogateDiagTailX0RatChunk001Sub000Block011Part017
    + surrogateDiagTailX0RatChunk001Sub000Block011Part018
    + surrogateDiagTailX0RatChunk001Sub000Block011Part019
    + surrogateDiagTailX0RatChunk001Sub000Block011Part020
    + surrogateDiagTailX0RatChunk001Sub000Block011Part021
    + surrogateDiagTailX0RatChunk001Sub000Block011Part022
    + surrogateDiagTailX0RatChunk001Sub000Block011Part023
    + surrogateDiagTailX0RatChunk001Sub000Block011Part024

theorem surrogateDiagTailX0RatChunk001Sub000Block011_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk001Sub000Block011Head + surrogateDiagTailX0RatChunk001Sub000Block011Mid + surrogateDiagTailX0RatChunk001Sub000Block011Tail =
      surrogateDiagTailX0RatChunk001Sub000Block011 := by
  unfold surrogateDiagTailX0RatChunk001Sub000Block011Head surrogateDiagTailX0RatChunk001Sub000Block011Mid surrogateDiagTailX0RatChunk001Sub000Block011Tail surrogateDiagTailX0RatChunk001Sub000Block011
  ring

def SurrogateDiagonalTailChunk001Sub000Block011HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block011HeadSum X0 = surrogateDiagTailX0RatChunk001Sub000Block011Head

def SurrogateDiagonalTailChunk001Sub000Block011MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block011MidSum X0 = surrogateDiagTailX0RatChunk001Sub000Block011Mid

def SurrogateDiagonalTailChunk001Sub000Block011TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block011TailSum X0 = surrogateDiagTailX0RatChunk001Sub000Block011Tail

theorem surrogateDiagonalTailChunk001Sub000Block011_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk001Sub000Block011HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk001Sub000Block011MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk001Sub000Block011TailCertificateAt X0) :
    surrogateDiagonalTailChunk001Sub000Block011Sum X0 = surrogateDiagTailX0RatChunk001Sub000Block011 := by
  unfold SurrogateDiagonalTailChunk001Sub000Block011HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk001Sub000Block011MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk001Sub000Block011TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk001Sub000Block011Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk001Sub000Block011_eq_head_add_mid_add_tail

/-- Block 012 covers tail-support indices [10300,10325) and q from 16990 to 17029. -/

def TailChunk001Sub000Block012Part000SupportExplicit : Finset ℕ :=
  ([16990] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block012Part000 : ℚ :=
  (3245359355425 : ℚ) / 5321297842353358848

def SurrogateDiagonalTailChunk001Sub000Block012Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16990
    = surrogateDiagTailX0RatChunk001Sub000Block012Part000

theorem surrogateDiagonalTailChunk001Sub000Block012Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block012Part000CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block012Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block012Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block012Part000CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block012Part000SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block012Part000] using hcert

def TailChunk001Sub000Block012Part001SupportExplicit : Finset ℕ :=
  ([16991] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block012Part001 : ℚ :=
  (71651018275 : ℚ) / 25140464668761689088

def SurrogateDiagonalTailChunk001Sub000Block012Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16991
    = surrogateDiagTailX0RatChunk001Sub000Block012Part001

theorem surrogateDiagonalTailChunk001Sub000Block012Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block012Part001CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block012Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block012Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block012Part001CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block012Part001SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block012Part001] using hcert

def TailChunk001Sub000Block012Part002SupportExplicit : Finset ℕ :=
  ([16993] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block012Part002 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block012Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16993
    = surrogateDiagTailX0RatChunk001Sub000Block012Part002

theorem surrogateDiagonalTailChunk001Sub000Block012Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block012Part002CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block012Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block012Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block012Part002CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block012Part002SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block012Part002] using hcert

def TailChunk001Sub000Block012Part003SupportExplicit : Finset ℕ :=
  ([16994] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block012Part003 : ℚ :=
  (305184179675 : ℚ) / 798109268568686592

def SurrogateDiagonalTailChunk001Sub000Block012Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16994
    = surrogateDiagTailX0RatChunk001Sub000Block012Part003

theorem surrogateDiagonalTailChunk001Sub000Block012Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block012Part003CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block012Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block012Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block012Part003CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block012Part003SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block012Part003] using hcert

def TailChunk001Sub000Block012Part004SupportExplicit : Finset ℕ :=
  ([16995] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block012Part004 : ℚ :=
  (33778148933 : ℚ) / 221726442789273600

def SurrogateDiagonalTailChunk001Sub000Block012Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16995
    = surrogateDiagTailX0RatChunk001Sub000Block012Part004

theorem surrogateDiagonalTailChunk001Sub000Block012Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block012Part004CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block012Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block012Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block012Part004CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block012Part004SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block012Part004] using hcert

def TailChunk001Sub000Block012Part005SupportExplicit : Finset ℕ :=
  ([16997] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block012Part005 : ℚ :=
  (20405032025 : ℚ) / 14479773998730521184

def SurrogateDiagonalTailChunk001Sub000Block012Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16997
    = surrogateDiagTailX0RatChunk001Sub000Block012Part005

theorem surrogateDiagonalTailChunk001Sub000Block012Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block012Part005CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block012Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block012Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block012Part005CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block012Part005SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block012Part005] using hcert

def TailChunk001Sub000Block012Part006SupportExplicit : Finset ℕ :=
  ([16998] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block012Part006 : ℚ :=
  (1253672938925 : ℚ) / 1286737156175560704

def SurrogateDiagonalTailChunk001Sub000Block012Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16998
    = surrogateDiagTailX0RatChunk001Sub000Block012Part006

theorem surrogateDiagonalTailChunk001Sub000Block012Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block012Part006CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block012Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block012Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block012Part006CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block012Part006SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block012Part006] using hcert

def TailChunk001Sub000Block012Part007SupportExplicit : Finset ℕ :=
  ([16999] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block012Part007 : ℚ :=
  (3450316741 : ℚ) / 7816852959036211200

def SurrogateDiagonalTailChunk001Sub000Block012Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16999
    = surrogateDiagTailX0RatChunk001Sub000Block012Part007

theorem surrogateDiagonalTailChunk001Sub000Block012Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block012Part007CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block012Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block012Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block012Part007CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block012Part007SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block012Part007] using hcert

def TailChunk001Sub000Block012Part008SupportExplicit : Finset ℕ :=
  ([17002] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block012Part008 : ℚ :=
  (72267001 : ℚ) / 208844260500000

def SurrogateDiagonalTailChunk001Sub000Block012Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17002
    = surrogateDiagTailX0RatChunk001Sub000Block012Part008

theorem surrogateDiagonalTailChunk001Sub000Block012Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block012Part008CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block012Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block012Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block012Part008CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block012Part008SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block012Part008] using hcert

def TailChunk001Sub000Block012Part009SupportExplicit : Finset ℕ :=
  ([17005] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block012Part009 : ℚ :=
  (111947177975 : ℚ) / 8432315874706231296

def SurrogateDiagonalTailChunk001Sub000Block012Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17005
    = surrogateDiagTailX0RatChunk001Sub000Block012Part009

theorem surrogateDiagonalTailChunk001Sub000Block012Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block012Part009CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block012Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block012Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block012Part009CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block012Part009SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block012Part009] using hcert

def TailChunk001Sub000Block012Part010SupportExplicit : Finset ℕ :=
  ([17006] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block012Part010 : ℚ :=
  (3161749085 : ℚ) / 7105359352833024

def SurrogateDiagonalTailChunk001Sub000Block012Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17006
    = surrogateDiagTailX0RatChunk001Sub000Block012Part010

theorem surrogateDiagonalTailChunk001Sub000Block012Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block012Part010CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block012Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block012Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block012Part010CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block012Part010SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block012Part010] using hcert

def TailChunk001Sub000Block012Part011SupportExplicit : Finset ℕ :=
  ([17007] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block012Part011 : ℚ :=
  (251064255725 : ℚ) / 5161503436759378176

def SurrogateDiagonalTailChunk001Sub000Block012Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17007
    = surrogateDiagTailX0RatChunk001Sub000Block012Part011

theorem surrogateDiagonalTailChunk001Sub000Block012Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block012Part011CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block012Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block012Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block012Part011CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block012Part011SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block012Part011] using hcert

def TailChunk001Sub000Block012Part012SupportExplicit : Finset ℕ :=
  ([17009] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block012Part012 : ℚ :=
  (96042482875 : ℚ) / 194674372803431497728

def SurrogateDiagonalTailChunk001Sub000Block012Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17009
    = surrogateDiagTailX0RatChunk001Sub000Block012Part012

theorem surrogateDiagonalTailChunk001Sub000Block012Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block012Part012CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block012Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block012Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block012Part012CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block012Part012SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block012Part012] using hcert

def TailChunk001Sub000Block012Part013SupportExplicit : Finset ℕ :=
  ([17011] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block012Part013 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block012Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17011
    = surrogateDiagTailX0RatChunk001Sub000Block012Part013

theorem surrogateDiagonalTailChunk001Sub000Block012Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block012Part013CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block012Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block012Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block012Part013CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block012Part013SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block012Part013] using hcert

def TailChunk001Sub000Block012Part014SupportExplicit : Finset ℕ :=
  ([17013] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block012Part014 : ℚ :=
  (998793664025 : ℚ) / 18465185779430866944

def SurrogateDiagonalTailChunk001Sub000Block012Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17013
    = surrogateDiagTailX0RatChunk001Sub000Block012Part014

theorem surrogateDiagonalTailChunk001Sub000Block012Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block012Part014CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block012Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block012Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block012Part014CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block012Part014SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block012Part014] using hcert

def TailChunk001Sub000Block012Part015SupportExplicit : Finset ℕ :=
  ([17014] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block012Part015 : ℚ :=
  (87089735621 : ℚ) / 235059713070105600

def SurrogateDiagonalTailChunk001Sub000Block012Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17014
    = surrogateDiagTailX0RatChunk001Sub000Block012Part015

theorem surrogateDiagonalTailChunk001Sub000Block012Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block012Part015CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block012Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block012Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block012Part015CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block012Part015SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block012Part015] using hcert

def TailChunk001Sub000Block012Part016SupportExplicit : Finset ℕ :=
  ([17015] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block012Part016 : ℚ :=
  (4979199417 : ℚ) / 246968147614105600

def SurrogateDiagonalTailChunk001Sub000Block012Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17015
    = surrogateDiagTailX0RatChunk001Sub000Block012Part016

theorem surrogateDiagonalTailChunk001Sub000Block012Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block012Part016CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block012Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block012Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block012Part016CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block012Part016SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block012Part016] using hcert

def TailChunk001Sub000Block012Part017SupportExplicit : Finset ℕ :=
  ([17017] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block012Part017 : ℚ :=
  (10078339007 : ℚ) / 352311453564272640

def SurrogateDiagonalTailChunk001Sub000Block012Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17017
    = surrogateDiagTailX0RatChunk001Sub000Block012Part017

theorem surrogateDiagonalTailChunk001Sub000Block012Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block012Part017CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block012Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block012Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block012Part017CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block012Part017SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block012Part017] using hcert

def TailChunk001Sub000Block012Part018SupportExplicit : Finset ℕ :=
  ([17018] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block012Part018 : ℚ :=
  (14224411175 : ℚ) / 38827020499809696

def SurrogateDiagonalTailChunk001Sub000Block012Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17018
    = surrogateDiagTailX0RatChunk001Sub000Block012Part018

theorem surrogateDiagonalTailChunk001Sub000Block012Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block012Part018CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block012Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block012Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block012Part018CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block012Part018SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block012Part018] using hcert

def TailChunk001Sub000Block012Part019SupportExplicit : Finset ℕ :=
  ([17021] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block012Part019 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block012Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17021
    = surrogateDiagTailX0RatChunk001Sub000Block012Part019

theorem surrogateDiagonalTailChunk001Sub000Block012Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block012Part019CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block012Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block012Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block012Part019CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block012Part019SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block012Part019] using hcert

def TailChunk001Sub000Block012Part020SupportExplicit : Finset ℕ :=
  ([17022] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block012Part020 : ℚ :=
  (1257216005675 : ℚ) / 1294022274040587264

def SurrogateDiagonalTailChunk001Sub000Block012Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17022
    = surrogateDiagTailX0RatChunk001Sub000Block012Part020

theorem surrogateDiagonalTailChunk001Sub000Block012Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block012Part020CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block012Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block012Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block012Part020CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block012Part020SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block012Part020] using hcert

def TailChunk001Sub000Block012Part021SupportExplicit : Finset ℕ :=
  ([17023] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block012Part021 : ℚ :=
  (14398765475 : ℚ) / 12945577012367096832

def SurrogateDiagonalTailChunk001Sub000Block012Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17023
    = surrogateDiagTailX0RatChunk001Sub000Block012Part021

theorem surrogateDiagonalTailChunk001Sub000Block012Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block012Part021CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block012Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block012Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block012Part021CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block012Part021SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block012Part021] using hcert

def TailChunk001Sub000Block012Part022SupportExplicit : Finset ℕ :=
  ([17026] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block012Part022 : ℚ :=
  (1132362015625 : ℚ) / 3281658064605806592

def SurrogateDiagonalTailChunk001Sub000Block012Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17026
    = surrogateDiagTailX0RatChunk001Sub000Block012Part022

theorem surrogateDiagonalTailChunk001Sub000Block012Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block012Part022CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block012Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block012Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block012Part022CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block012Part022SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block012Part022] using hcert

def TailChunk001Sub000Block012Part023SupportExplicit : Finset ℕ :=
  ([17027] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block012Part023 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block012Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17027
    = surrogateDiagTailX0RatChunk001Sub000Block012Part023

theorem surrogateDiagonalTailChunk001Sub000Block012Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block012Part023CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block012Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block012Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block012Part023CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block012Part023SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block012Part023] using hcert

def TailChunk001Sub000Block012Part024SupportExplicit : Finset ℕ :=
  ([17029] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block012Part024 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block012Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17029
    = surrogateDiagTailX0RatChunk001Sub000Block012Part024

theorem surrogateDiagonalTailChunk001Sub000Block012Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block012Part024CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block012Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block012Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block012Part024CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block012Part024SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block012Part024] using hcert

def surrogateDiagonalTailChunk001Sub000Block012HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block012Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block012Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block012Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block012Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block012Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block012Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block012Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block012Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block012Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block012Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block012Head : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block012Part000
    + surrogateDiagTailX0RatChunk001Sub000Block012Part001
    + surrogateDiagTailX0RatChunk001Sub000Block012Part002
    + surrogateDiagTailX0RatChunk001Sub000Block012Part003
    + surrogateDiagTailX0RatChunk001Sub000Block012Part004
    + surrogateDiagTailX0RatChunk001Sub000Block012Part005
    + surrogateDiagTailX0RatChunk001Sub000Block012Part006
    + surrogateDiagTailX0RatChunk001Sub000Block012Part007
    + surrogateDiagTailX0RatChunk001Sub000Block012Part008
    + surrogateDiagTailX0RatChunk001Sub000Block012Part009

def surrogateDiagonalTailChunk001Sub000Block012MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block012Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block012Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block012Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block012Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block012Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block012Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block012Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block012Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block012Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block012Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block012Mid : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block012Part010
    + surrogateDiagTailX0RatChunk001Sub000Block012Part011
    + surrogateDiagTailX0RatChunk001Sub000Block012Part012
    + surrogateDiagTailX0RatChunk001Sub000Block012Part013
    + surrogateDiagTailX0RatChunk001Sub000Block012Part014
    + surrogateDiagTailX0RatChunk001Sub000Block012Part015
    + surrogateDiagTailX0RatChunk001Sub000Block012Part016
    + surrogateDiagTailX0RatChunk001Sub000Block012Part017
    + surrogateDiagTailX0RatChunk001Sub000Block012Part018
    + surrogateDiagTailX0RatChunk001Sub000Block012Part019

def surrogateDiagonalTailChunk001Sub000Block012TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block012Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block012Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block012Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block012Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block012Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block012Tail : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block012Part020
    + surrogateDiagTailX0RatChunk001Sub000Block012Part021
    + surrogateDiagTailX0RatChunk001Sub000Block012Part022
    + surrogateDiagTailX0RatChunk001Sub000Block012Part023
    + surrogateDiagTailX0RatChunk001Sub000Block012Part024

def surrogateDiagonalTailChunk001Sub000Block012Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk001Sub000Block012HeadSum X0
    + surrogateDiagonalTailChunk001Sub000Block012MidSum X0
    + surrogateDiagonalTailChunk001Sub000Block012TailSum X0

def surrogateDiagTailX0RatChunk001Sub000Block012 : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block012Part000
    + surrogateDiagTailX0RatChunk001Sub000Block012Part001
    + surrogateDiagTailX0RatChunk001Sub000Block012Part002
    + surrogateDiagTailX0RatChunk001Sub000Block012Part003
    + surrogateDiagTailX0RatChunk001Sub000Block012Part004
    + surrogateDiagTailX0RatChunk001Sub000Block012Part005
    + surrogateDiagTailX0RatChunk001Sub000Block012Part006
    + surrogateDiagTailX0RatChunk001Sub000Block012Part007
    + surrogateDiagTailX0RatChunk001Sub000Block012Part008
    + surrogateDiagTailX0RatChunk001Sub000Block012Part009
    + surrogateDiagTailX0RatChunk001Sub000Block012Part010
    + surrogateDiagTailX0RatChunk001Sub000Block012Part011
    + surrogateDiagTailX0RatChunk001Sub000Block012Part012
    + surrogateDiagTailX0RatChunk001Sub000Block012Part013
    + surrogateDiagTailX0RatChunk001Sub000Block012Part014
    + surrogateDiagTailX0RatChunk001Sub000Block012Part015
    + surrogateDiagTailX0RatChunk001Sub000Block012Part016
    + surrogateDiagTailX0RatChunk001Sub000Block012Part017
    + surrogateDiagTailX0RatChunk001Sub000Block012Part018
    + surrogateDiagTailX0RatChunk001Sub000Block012Part019
    + surrogateDiagTailX0RatChunk001Sub000Block012Part020
    + surrogateDiagTailX0RatChunk001Sub000Block012Part021
    + surrogateDiagTailX0RatChunk001Sub000Block012Part022
    + surrogateDiagTailX0RatChunk001Sub000Block012Part023
    + surrogateDiagTailX0RatChunk001Sub000Block012Part024

theorem surrogateDiagTailX0RatChunk001Sub000Block012_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk001Sub000Block012Head + surrogateDiagTailX0RatChunk001Sub000Block012Mid + surrogateDiagTailX0RatChunk001Sub000Block012Tail =
      surrogateDiagTailX0RatChunk001Sub000Block012 := by
  unfold surrogateDiagTailX0RatChunk001Sub000Block012Head surrogateDiagTailX0RatChunk001Sub000Block012Mid surrogateDiagTailX0RatChunk001Sub000Block012Tail surrogateDiagTailX0RatChunk001Sub000Block012
  ring

def SurrogateDiagonalTailChunk001Sub000Block012HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block012HeadSum X0 = surrogateDiagTailX0RatChunk001Sub000Block012Head

def SurrogateDiagonalTailChunk001Sub000Block012MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block012MidSum X0 = surrogateDiagTailX0RatChunk001Sub000Block012Mid

def SurrogateDiagonalTailChunk001Sub000Block012TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block012TailSum X0 = surrogateDiagTailX0RatChunk001Sub000Block012Tail

theorem surrogateDiagonalTailChunk001Sub000Block012_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk001Sub000Block012HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk001Sub000Block012MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk001Sub000Block012TailCertificateAt X0) :
    surrogateDiagonalTailChunk001Sub000Block012Sum X0 = surrogateDiagTailX0RatChunk001Sub000Block012 := by
  unfold SurrogateDiagonalTailChunk001Sub000Block012HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk001Sub000Block012MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk001Sub000Block012TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk001Sub000Block012Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk001Sub000Block012_eq_head_add_mid_add_tail

/-- Block 013 covers tail-support indices [10325,10350) and q from 17030 to 17071. -/

def TailChunk001Sub000Block013Part000SupportExplicit : Finset ℕ :=
  ([17030] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block013Part000 : ℚ :=
  (23080578701 : ℚ) / 30328798421975040

def SurrogateDiagonalTailChunk001Sub000Block013Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17030
    = surrogateDiagTailX0RatChunk001Sub000Block013Part000

theorem surrogateDiagonalTailChunk001Sub000Block013Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block013Part000CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block013Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block013Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block013Part000CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block013Part000SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block013Part000] using hcert

def TailChunk001Sub000Block013Part001SupportExplicit : Finset ℕ :=
  ([17031] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block013Part001 : ℚ :=
  (264439 : ℚ) / 11901557422080

def SurrogateDiagonalTailChunk001Sub000Block013Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17031
    = surrogateDiagTailX0RatChunk001Sub000Block013Part001

theorem surrogateDiagonalTailChunk001Sub000Block013Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block013Part001CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block013Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block013Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block013Part001CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block013Part001SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block013Part001] using hcert

def TailChunk001Sub000Block013Part002SupportExplicit : Finset ℕ :=
  ([17033] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block013Part002 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block013Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17033
    = surrogateDiagTailX0RatChunk001Sub000Block013Part002

theorem surrogateDiagonalTailChunk001Sub000Block013Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block013Part002CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block013Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block013Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block013Part002CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block013Part002SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block013Part002] using hcert

def TailChunk001Sub000Block013Part003SupportExplicit : Finset ℕ :=
  ([17034] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block013Part003 : ℚ :=
  (620996979075 : ℚ) / 663648121762349056

def SurrogateDiagonalTailChunk001Sub000Block013Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17034
    = surrogateDiagTailX0RatChunk001Sub000Block013Part003

theorem surrogateDiagonalTailChunk001Sub000Block013Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block013Part003CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block013Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block013Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block013Part003CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block013Part003SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block013Part003] using hcert

def TailChunk001Sub000Block013Part004SupportExplicit : Finset ℕ :=
  ([17035] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block013Part004 : ℚ :=
  (1451064582025 : ℚ) / 86148039537968498688

def SurrogateDiagonalTailChunk001Sub000Block013Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17035
    = surrogateDiagTailX0RatChunk001Sub000Block013Part004

theorem surrogateDiagonalTailChunk001Sub000Block013Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block013Part004CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block013Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block013Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block013Part004CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block013Part004SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block013Part004] using hcert

def TailChunk001Sub000Block013Part005SupportExplicit : Finset ℕ :=
  ([17038] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block013Part005 : ℚ :=
  (200369462375 : ℚ) / 393634953188868096

def SurrogateDiagonalTailChunk001Sub000Block013Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17038
    = surrogateDiagTailX0RatChunk001Sub000Block013Part005

theorem surrogateDiagonalTailChunk001Sub000Block013Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block013Part005CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block013Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block013Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block013Part005CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block013Part005SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block013Part005] using hcert

def TailChunk001Sub000Block013Part006SupportExplicit : Finset ℕ :=
  ([17039] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block013Part006 : ℚ :=
  (24073742629 : ℚ) / 5743421314988083200

def SurrogateDiagonalTailChunk001Sub000Block013Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17039
    = surrogateDiagTailX0RatChunk001Sub000Block013Part006

theorem surrogateDiagonalTailChunk001Sub000Block013Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block013Part006CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block013Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block013Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block013Part006CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block013Part006SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block013Part006] using hcert

def TailChunk001Sub000Block013Part007SupportExplicit : Finset ℕ :=
  ([17041] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block013Part007 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block013Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17041
    = surrogateDiagTailX0RatChunk001Sub000Block013Part007

theorem surrogateDiagonalTailChunk001Sub000Block013Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block013Part007CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block013Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block013Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block013Part007CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block013Part007SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block013Part007] using hcert

def TailChunk001Sub000Block013Part008SupportExplicit : Finset ℕ :=
  ([17042] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block013Part008 : ℚ :=
  (1815186025 : ℚ) / 5270420045394432

def SurrogateDiagonalTailChunk001Sub000Block013Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17042
    = surrogateDiagTailX0RatChunk001Sub000Block013Part008

theorem surrogateDiagonalTailChunk001Sub000Block013Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block013Part008CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block013Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block013Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block013Part008CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block013Part008SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block013Part008] using hcert

def TailChunk001Sub000Block013Part009SupportExplicit : Finset ℕ :=
  ([17043] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block013Part009 : ℚ :=
  (7693197125 : ℚ) / 309106853191876608

def SurrogateDiagonalTailChunk001Sub000Block013Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17043
    = surrogateDiagTailX0RatChunk001Sub000Block013Part009

theorem surrogateDiagonalTailChunk001Sub000Block013Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block013Part009CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block013Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block013Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block013Part009CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block013Part009SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block013Part009] using hcert

def TailChunk001Sub000Block013Part010SupportExplicit : Finset ℕ :=
  ([17045] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block013Part010 : ℚ :=
  (1631090381125 : ℚ) / 46282509908098449408

def SurrogateDiagonalTailChunk001Sub000Block013Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17045
    = surrogateDiagTailX0RatChunk001Sub000Block013Part010

theorem surrogateDiagonalTailChunk001Sub000Block013Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block013Part010CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block013Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block013Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block013Part010CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block013Part010SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block013Part010] using hcert

def TailChunk001Sub000Block013Part011SupportExplicit : Finset ℕ :=
  ([17047] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block013Part011 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block013Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17047
    = surrogateDiagTailX0RatChunk001Sub000Block013Part011

theorem surrogateDiagonalTailChunk001Sub000Block013Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block013Part011CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block013Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block013Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block013Part011CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block013Part011SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block013Part011] using hcert

def TailChunk001Sub000Block013Part012SupportExplicit : Finset ℕ :=
  ([17049] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block013Part012 : ℚ :=
  (1009222647725 : ℚ) / 20850753950834301504

def SurrogateDiagonalTailChunk001Sub000Block013Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17049
    = surrogateDiagTailX0RatChunk001Sub000Block013Part012

theorem surrogateDiagonalTailChunk001Sub000Block013Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block013Part012CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block013Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block013Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block013Part012CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block013Part012SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block013Part012] using hcert

def TailChunk001Sub000Block013Part013SupportExplicit : Finset ℕ :=
  ([17053] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block013Part013 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block013Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17053
    = surrogateDiagTailX0RatChunk001Sub000Block013Part013

theorem surrogateDiagonalTailChunk001Sub000Block013Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block013Part013CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block013Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block013Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block013Part013CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block013Part013SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block013Part013] using hcert

def TailChunk001Sub000Block013Part014SupportExplicit : Finset ℕ :=
  ([17054] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block013Part014 : ℚ :=
  (1136089515625 : ℚ) / 3303301243168615122

def SurrogateDiagonalTailChunk001Sub000Block013Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17054
    = surrogateDiagTailX0RatChunk001Sub000Block013Part014

theorem surrogateDiagonalTailChunk001Sub000Block013Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block013Part014CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block013Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block013Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block013Part014CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block013Part014SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block013Part014] using hcert

def TailChunk001Sub000Block013Part015SupportExplicit : Finset ℕ :=
  ([17057] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block013Part015 : ℚ :=
  (1251392819 : ℚ) / 1504382163648675840

def SurrogateDiagonalTailChunk001Sub000Block013Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17057
    = surrogateDiagTailX0RatChunk001Sub000Block013Part015

theorem surrogateDiagonalTailChunk001Sub000Block013Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block013Part015CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block013Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block013Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block013Part015CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block013Part015SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block013Part015] using hcert

def TailChunk001Sub000Block013Part016SupportExplicit : Finset ℕ :=
  ([17058] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block013Part016 : ℚ :=
  (315634995575 : ℚ) / 326251974633937296

def SurrogateDiagonalTailChunk001Sub000Block013Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17058
    = surrogateDiagTailX0RatChunk001Sub000Block013Part016

theorem surrogateDiagonalTailChunk001Sub000Block013Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block013Part016CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block013Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block013Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block013Part016CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block013Part016SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block013Part016] using hcert

def TailChunk001Sub000Block013Part017SupportExplicit : Finset ℕ :=
  ([17059] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block013Part017 : ℚ :=
  (371744228375 : ℚ) / 57057271618779177984

def SurrogateDiagonalTailChunk001Sub000Block013Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17059
    = surrogateDiagTailX0RatChunk001Sub000Block013Part017

theorem surrogateDiagonalTailChunk001Sub000Block013Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block013Part017CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block013Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block013Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block013Part017CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block013Part017SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block013Part017] using hcert

def TailChunk001Sub000Block013Part018SupportExplicit : Finset ℕ :=
  ([17062] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block013Part018 : ℚ :=
  (16390525075 : ℚ) / 41303701172256768

def SurrogateDiagonalTailChunk001Sub000Block013Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17062
    = surrogateDiagTailX0RatChunk001Sub000Block013Part018

theorem surrogateDiagonalTailChunk001Sub000Block013Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block013Part018CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block013Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block013Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block013Part018CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block013Part018SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block013Part018] using hcert

def TailChunk001Sub000Block013Part019SupportExplicit : Finset ℕ :=
  ([17063] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block013Part019 : ℚ :=
  (5762921 : ℚ) / 14052089856000000

def SurrogateDiagonalTailChunk001Sub000Block013Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17063
    = surrogateDiagTailX0RatChunk001Sub000Block013Part019

theorem surrogateDiagonalTailChunk001Sub000Block013Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block013Part019CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block013Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block013Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block013Part019CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block013Part019SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block013Part019] using hcert

def TailChunk001Sub000Block013Part020SupportExplicit : Finset ℕ :=
  ([17065] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block013Part020 : ℚ :=
  (242953253625 : ℚ) / 28918892672471105536

def SurrogateDiagonalTailChunk001Sub000Block013Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17065
    = surrogateDiagTailX0RatChunk001Sub000Block013Part020

theorem surrogateDiagonalTailChunk001Sub000Block013Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block013Part020CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block013Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block013Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block013Part020CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block013Part020SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block013Part020] using hcert

def TailChunk001Sub000Block013Part021SupportExplicit : Finset ℕ :=
  ([17066] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block013Part021 : ℚ :=
  (369199384025 : ℚ) / 616727691244634112

def SurrogateDiagonalTailChunk001Sub000Block013Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17066
    = surrogateDiagTailX0RatChunk001Sub000Block013Part021

theorem surrogateDiagonalTailChunk001Sub000Block013Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block013Part021CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block013Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block013Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block013Part021CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block013Part021SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block013Part021] using hcert

def TailChunk001Sub000Block013Part022SupportExplicit : Finset ℕ :=
  ([17067] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block013Part022 : ℚ :=
  (505677261325 : ℚ) / 10469482157559324672

def SurrogateDiagonalTailChunk001Sub000Block013Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17067
    = surrogateDiagTailX0RatChunk001Sub000Block013Part022

theorem surrogateDiagonalTailChunk001Sub000Block013Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block013Part022CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block013Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block013Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block013Part022CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block013Part022SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block013Part022] using hcert

def TailChunk001Sub000Block013Part023SupportExplicit : Finset ℕ :=
  ([17070] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block013Part023 : ℚ :=
  (939009986975 : ℚ) / 533028160640385024

def SurrogateDiagonalTailChunk001Sub000Block013Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17070
    = surrogateDiagTailX0RatChunk001Sub000Block013Part023

theorem surrogateDiagonalTailChunk001Sub000Block013Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block013Part023CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block013Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block013Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block013Part023CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block013Part023SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block013Part023] using hcert

def TailChunk001Sub000Block013Part024SupportExplicit : Finset ℕ :=
  ([17071] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block013Part024 : ℚ :=
  (140307979825 : ℚ) / 191339557023062181888

def SurrogateDiagonalTailChunk001Sub000Block013Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17071
    = surrogateDiagTailX0RatChunk001Sub000Block013Part024

theorem surrogateDiagonalTailChunk001Sub000Block013Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block013Part024CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block013Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block013Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block013Part024CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block013Part024SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block013Part024] using hcert

def surrogateDiagonalTailChunk001Sub000Block013HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block013Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block013Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block013Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block013Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block013Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block013Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block013Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block013Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block013Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block013Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block013Head : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block013Part000
    + surrogateDiagTailX0RatChunk001Sub000Block013Part001
    + surrogateDiagTailX0RatChunk001Sub000Block013Part002
    + surrogateDiagTailX0RatChunk001Sub000Block013Part003
    + surrogateDiagTailX0RatChunk001Sub000Block013Part004
    + surrogateDiagTailX0RatChunk001Sub000Block013Part005
    + surrogateDiagTailX0RatChunk001Sub000Block013Part006
    + surrogateDiagTailX0RatChunk001Sub000Block013Part007
    + surrogateDiagTailX0RatChunk001Sub000Block013Part008
    + surrogateDiagTailX0RatChunk001Sub000Block013Part009

def surrogateDiagonalTailChunk001Sub000Block013MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block013Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block013Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block013Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block013Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block013Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block013Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block013Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block013Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block013Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block013Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block013Mid : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block013Part010
    + surrogateDiagTailX0RatChunk001Sub000Block013Part011
    + surrogateDiagTailX0RatChunk001Sub000Block013Part012
    + surrogateDiagTailX0RatChunk001Sub000Block013Part013
    + surrogateDiagTailX0RatChunk001Sub000Block013Part014
    + surrogateDiagTailX0RatChunk001Sub000Block013Part015
    + surrogateDiagTailX0RatChunk001Sub000Block013Part016
    + surrogateDiagTailX0RatChunk001Sub000Block013Part017
    + surrogateDiagTailX0RatChunk001Sub000Block013Part018
    + surrogateDiagTailX0RatChunk001Sub000Block013Part019

def surrogateDiagonalTailChunk001Sub000Block013TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block013Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block013Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block013Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block013Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block013Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block013Tail : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block013Part020
    + surrogateDiagTailX0RatChunk001Sub000Block013Part021
    + surrogateDiagTailX0RatChunk001Sub000Block013Part022
    + surrogateDiagTailX0RatChunk001Sub000Block013Part023
    + surrogateDiagTailX0RatChunk001Sub000Block013Part024

def surrogateDiagonalTailChunk001Sub000Block013Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk001Sub000Block013HeadSum X0
    + surrogateDiagonalTailChunk001Sub000Block013MidSum X0
    + surrogateDiagonalTailChunk001Sub000Block013TailSum X0

def surrogateDiagTailX0RatChunk001Sub000Block013 : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block013Part000
    + surrogateDiagTailX0RatChunk001Sub000Block013Part001
    + surrogateDiagTailX0RatChunk001Sub000Block013Part002
    + surrogateDiagTailX0RatChunk001Sub000Block013Part003
    + surrogateDiagTailX0RatChunk001Sub000Block013Part004
    + surrogateDiagTailX0RatChunk001Sub000Block013Part005
    + surrogateDiagTailX0RatChunk001Sub000Block013Part006
    + surrogateDiagTailX0RatChunk001Sub000Block013Part007
    + surrogateDiagTailX0RatChunk001Sub000Block013Part008
    + surrogateDiagTailX0RatChunk001Sub000Block013Part009
    + surrogateDiagTailX0RatChunk001Sub000Block013Part010
    + surrogateDiagTailX0RatChunk001Sub000Block013Part011
    + surrogateDiagTailX0RatChunk001Sub000Block013Part012
    + surrogateDiagTailX0RatChunk001Sub000Block013Part013
    + surrogateDiagTailX0RatChunk001Sub000Block013Part014
    + surrogateDiagTailX0RatChunk001Sub000Block013Part015
    + surrogateDiagTailX0RatChunk001Sub000Block013Part016
    + surrogateDiagTailX0RatChunk001Sub000Block013Part017
    + surrogateDiagTailX0RatChunk001Sub000Block013Part018
    + surrogateDiagTailX0RatChunk001Sub000Block013Part019
    + surrogateDiagTailX0RatChunk001Sub000Block013Part020
    + surrogateDiagTailX0RatChunk001Sub000Block013Part021
    + surrogateDiagTailX0RatChunk001Sub000Block013Part022
    + surrogateDiagTailX0RatChunk001Sub000Block013Part023
    + surrogateDiagTailX0RatChunk001Sub000Block013Part024

theorem surrogateDiagTailX0RatChunk001Sub000Block013_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk001Sub000Block013Head + surrogateDiagTailX0RatChunk001Sub000Block013Mid + surrogateDiagTailX0RatChunk001Sub000Block013Tail =
      surrogateDiagTailX0RatChunk001Sub000Block013 := by
  unfold surrogateDiagTailX0RatChunk001Sub000Block013Head surrogateDiagTailX0RatChunk001Sub000Block013Mid surrogateDiagTailX0RatChunk001Sub000Block013Tail surrogateDiagTailX0RatChunk001Sub000Block013
  ring

def SurrogateDiagonalTailChunk001Sub000Block013HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block013HeadSum X0 = surrogateDiagTailX0RatChunk001Sub000Block013Head

def SurrogateDiagonalTailChunk001Sub000Block013MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block013MidSum X0 = surrogateDiagTailX0RatChunk001Sub000Block013Mid

def SurrogateDiagonalTailChunk001Sub000Block013TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block013TailSum X0 = surrogateDiagTailX0RatChunk001Sub000Block013Tail

theorem surrogateDiagonalTailChunk001Sub000Block013_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk001Sub000Block013HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk001Sub000Block013MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk001Sub000Block013TailCertificateAt X0) :
    surrogateDiagonalTailChunk001Sub000Block013Sum X0 = surrogateDiagTailX0RatChunk001Sub000Block013 := by
  unfold SurrogateDiagonalTailChunk001Sub000Block013HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk001Sub000Block013MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk001Sub000Block013TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk001Sub000Block013Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk001Sub000Block013_eq_head_add_mid_add_tail

/-- Block 014 covers tail-support indices [10350,10375) and q from 17074 to 17113. -/

def TailChunk001Sub000Block014Part000SupportExplicit : Finset ℕ :=
  ([17074] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block014Part000 : ℚ :=
  (1138755765625 : ℚ) / 3318826072477757952

def SurrogateDiagonalTailChunk001Sub000Block014Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17074
    = surrogateDiagTailX0RatChunk001Sub000Block014Part000

theorem surrogateDiagonalTailChunk001Sub000Block014Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block014Part000CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block014Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block014Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block014Part000CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block014Part000SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block014Part000] using hcert

def TailChunk001Sub000Block014Part001SupportExplicit : Finset ℕ :=
  ([17077] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block014Part001 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block014Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17077
    = surrogateDiagTailX0RatChunk001Sub000Block014Part001

theorem surrogateDiagonalTailChunk001Sub000Block014Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block014Part001CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block014Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block014Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block014Part001CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block014Part001SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block014Part001] using hcert

def TailChunk001Sub000Block014Part002SupportExplicit : Finset ℕ :=
  ([17078] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block014Part002 : ℚ :=
  (1139289390625 : ℚ) / 3321937593250926642

def SurrogateDiagonalTailChunk001Sub000Block014Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17078
    = surrogateDiagTailX0RatChunk001Sub000Block014Part002

theorem surrogateDiagonalTailChunk001Sub000Block014Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block014Part002CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block014Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block014Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block014Part002CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block014Part002SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block014Part002] using hcert

def TailChunk001Sub000Block014Part003SupportExplicit : Finset ℕ :=
  ([17079] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block014Part003 : ℚ :=
  (126597127825 : ℚ) / 2624740814420485248

def SurrogateDiagonalTailChunk001Sub000Block014Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17079
    = surrogateDiagTailX0RatChunk001Sub000Block014Part003

theorem surrogateDiagonalTailChunk001Sub000Block014Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block014Part003CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block014Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block014Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block014Part003CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block014Part003SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block014Part003] using hcert

def TailChunk001Sub000Block014Part004SupportExplicit : Finset ℕ :=
  ([17081] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block014Part004 : ℚ :=
  (10969637531 : ℚ) / 2613749839806873600

def SurrogateDiagonalTailChunk001Sub000Block014Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17081
    = surrogateDiagTailX0RatChunk001Sub000Block014Part004

theorem surrogateDiagonalTailChunk001Sub000Block014Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block014Part004CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block014Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block014Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block014Part004CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block014Part004SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block014Part004] using hcert

def TailChunk001Sub000Block014Part005SupportExplicit : Finset ℕ :=
  ([17083] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block014Part005 : ℚ :=
  (8065889367 : ℚ) / 1934338443535974400

def SurrogateDiagonalTailChunk001Sub000Block014Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17083
    = surrogateDiagTailX0RatChunk001Sub000Block014Part005

theorem surrogateDiagonalTailChunk001Sub000Block014Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block014Part005CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block014Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block014Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block014Part005CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block014Part005SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block014Part005] using hcert

def TailChunk001Sub000Block014Part006SupportExplicit : Finset ℕ :=
  ([17085] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block014Part006 : ℚ :=
  (28128403525 : ℚ) / 199004320664911872

def SurrogateDiagonalTailChunk001Sub000Block014Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17085
    = surrogateDiagTailX0RatChunk001Sub000Block014Part006

theorem surrogateDiagonalTailChunk001Sub000Block014Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block014Part006CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block014Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block014Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block014Part006CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block014Part006SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block014Part006] using hcert

def TailChunk001Sub000Block014Part007SupportExplicit : Finset ℕ :=
  ([17086] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block014Part007 : ℚ :=
  (1140357015625 : ℚ) / 3328167197904322962

def SurrogateDiagonalTailChunk001Sub000Block014Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17086
    = surrogateDiagTailX0RatChunk001Sub000Block014Part007

theorem surrogateDiagonalTailChunk001Sub000Block014Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block014Part007CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block014Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block014Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block014Part007CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block014Part007SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block014Part007] using hcert

def TailChunk001Sub000Block014Part008SupportExplicit : Finset ℕ :=
  ([17087] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block014Part008 : ℚ :=
  (14918519387 : ℚ) / 2297318243582361600

def SurrogateDiagonalTailChunk001Sub000Block014Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17087
    = surrogateDiagTailX0RatChunk001Sub000Block014Part008

theorem surrogateDiagonalTailChunk001Sub000Block014Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block014Part008CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block014Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block014Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block014Part008CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block014Part008SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block014Part008] using hcert

def TailChunk001Sub000Block014Part009SupportExplicit : Finset ℕ :=
  ([17089] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block014Part009 : ℚ :=
  (552337675 : ℚ) / 396328395690202206

def SurrogateDiagonalTailChunk001Sub000Block014Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17089
    = surrogateDiagTailX0RatChunk001Sub000Block014Part009

theorem surrogateDiagonalTailChunk001Sub000Block014Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block014Part009CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block014Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block014Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block014Part009CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block014Part009SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block014Part009] using hcert

def TailChunk001Sub000Block014Part010SupportExplicit : Finset ℕ :=
  ([17090] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block014Part010 : ℚ :=
  (156365848425 : ℚ) / 259417335818518528

def SurrogateDiagonalTailChunk001Sub000Block014Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17090
    = surrogateDiagTailX0RatChunk001Sub000Block014Part010

theorem surrogateDiagonalTailChunk001Sub000Block014Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block014Part010CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block014Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block014Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block014Part010CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block014Part010SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block014Part010] using hcert

def TailChunk001Sub000Block014Part011SupportExplicit : Finset ℕ :=
  ([17093] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block014Part011 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block014Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17093
    = surrogateDiagTailX0RatChunk001Sub000Block014Part011

theorem surrogateDiagonalTailChunk001Sub000Block014Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block014Part011CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block014Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block014Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block014Part011CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block014Part011SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block014Part011] using hcert

def TailChunk001Sub000Block014Part012SupportExplicit : Finset ℕ :=
  ([17094] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block014Part012 : ℚ :=
  (1466006977 : ℚ) / 725739230822400

def SurrogateDiagonalTailChunk001Sub000Block014Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17094
    = surrogateDiagTailX0RatChunk001Sub000Block014Part012

theorem surrogateDiagonalTailChunk001Sub000Block014Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block014Part012CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block014Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block014Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block014Part012CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block014Part012SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block014Part012] using hcert

def TailChunk001Sub000Block014Part013SupportExplicit : Finset ℕ :=
  ([17095] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block014Part013 : ℚ :=
  (322486922075 : ℚ) / 20848543443382173696

def SurrogateDiagonalTailChunk001Sub000Block014Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17095
    = surrogateDiagTailX0RatChunk001Sub000Block014Part013

theorem surrogateDiagonalTailChunk001Sub000Block014Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block014Part013CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block014Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block014Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block014Part013CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block014Part013SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block014Part013] using hcert

def TailChunk001Sub000Block014Part014SupportExplicit : Finset ℕ :=
  ([17097] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block014Part014 : ℚ :=
  (40272433031 : ℚ) / 742904772172185600

def SurrogateDiagonalTailChunk001Sub000Block014Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17097
    = surrogateDiagTailX0RatChunk001Sub000Block014Part014

theorem surrogateDiagonalTailChunk001Sub000Block014Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block014Part014CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block014Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block014Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block014Part014CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block014Part014SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block014Part014] using hcert

def TailChunk001Sub000Block014Part015SupportExplicit : Finset ℕ :=
  ([17098] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block014Part015 : ℚ :=
  (4428664615225 : ℚ) / 12237225287161339008

def SurrogateDiagonalTailChunk001Sub000Block014Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17098
    = surrogateDiagTailX0RatChunk001Sub000Block014Part015

theorem surrogateDiagonalTailChunk001Sub000Block014Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block014Part015CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block014Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block014Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block014Part015CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block014Part015SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block014Part015] using hcert

def TailChunk001Sub000Block014Part016SupportExplicit : Finset ℕ :=
  ([17099] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block014Part016 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block014Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17099
    = surrogateDiagTailX0RatChunk001Sub000Block014Part016

theorem surrogateDiagonalTailChunk001Sub000Block014Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block014Part016CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block014Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block014Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block014Part016CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block014Part016SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block014Part016] using hcert

def TailChunk001Sub000Block014Part017SupportExplicit : Finset ℕ :=
  ([17102] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block014Part017 : ℚ :=
  (4163677587925 : ℚ) / 10406906629194252288

def SurrogateDiagonalTailChunk001Sub000Block014Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17102
    = surrogateDiagTailX0RatChunk001Sub000Block014Part017

theorem surrogateDiagonalTailChunk001Sub000Block014Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block014Part017CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block014Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block014Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block014Part017CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block014Part017SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block014Part017] using hcert

def TailChunk001Sub000Block014Part018SupportExplicit : Finset ℕ :=
  ([17103] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block014Part018 : ℚ :=
  (406250009 : ℚ) / 8446489760160000

def SurrogateDiagonalTailChunk001Sub000Block014Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17103
    = surrogateDiagTailX0RatChunk001Sub000Block014Part018

theorem surrogateDiagonalTailChunk001Sub000Block014Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block014Part018CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block014Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block014Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block014Part018CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block014Part018SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block014Part018] using hcert

def TailChunk001Sub000Block014Part019SupportExplicit : Finset ℕ :=
  ([17105] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block014Part019 : ℚ :=
  (24339409 : ℚ) / 1477929126720000

def SurrogateDiagonalTailChunk001Sub000Block014Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17105
    = surrogateDiagTailX0RatChunk001Sub000Block014Part019

theorem surrogateDiagonalTailChunk001Sub000Block014Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block014Part019CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block014Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block014Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block014Part019CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block014Part019SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block014Part019] using hcert

def TailChunk001Sub000Block014Part020SupportExplicit : Finset ℕ :=
  ([17106] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block014Part020 : ℚ :=
  (6348280603 : ℚ) / 6598820125125000

def SurrogateDiagonalTailChunk001Sub000Block014Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17106
    = surrogateDiagTailX0RatChunk001Sub000Block014Part020

theorem surrogateDiagonalTailChunk001Sub000Block014Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block014Part020CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block014Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block014Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block014Part020CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block014Part020SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block014Part020] using hcert

def TailChunk001Sub000Block014Part021SupportExplicit : Finset ℕ :=
  ([17107] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block014Part021 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block014Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17107
    = surrogateDiagTailX0RatChunk001Sub000Block014Part021

theorem surrogateDiagonalTailChunk001Sub000Block014Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block014Part021CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block014Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block014Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block014Part021CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block014Part021SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block014Part021] using hcert

def TailChunk001Sub000Block014Part022SupportExplicit : Finset ℕ :=
  ([17110] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block014Part022 : ℚ :=
  (1534467358175 : ℚ) / 2226285861058904064

def SurrogateDiagonalTailChunk001Sub000Block014Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17110
    = surrogateDiagTailX0RatChunk001Sub000Block014Part022

theorem surrogateDiagonalTailChunk001Sub000Block014Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block014Part022CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block014Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block014Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block014Part022CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block014Part022SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block014Part022] using hcert

def TailChunk001Sub000Block014Part023SupportExplicit : Finset ℕ :=
  ([17111] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block014Part023 : ℚ :=
  (110911523 : ℚ) / 227643855667200000

def SurrogateDiagonalTailChunk001Sub000Block014Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17111
    = surrogateDiagTailX0RatChunk001Sub000Block014Part023

theorem surrogateDiagonalTailChunk001Sub000Block014Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block014Part023CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block014Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block014Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block014Part023CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block014Part023SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block014Part023] using hcert

def TailChunk001Sub000Block014Part024SupportExplicit : Finset ℕ :=
  ([17113] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block014Part024 : ℚ :=
  (702675625 : ℚ) / 1722005017326157824

def SurrogateDiagonalTailChunk001Sub000Block014Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17113
    = surrogateDiagTailX0RatChunk001Sub000Block014Part024

theorem surrogateDiagonalTailChunk001Sub000Block014Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block014Part024CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block014Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block014Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block014Part024CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block014Part024SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block014Part024] using hcert

def surrogateDiagonalTailChunk001Sub000Block014HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block014Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block014Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block014Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block014Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block014Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block014Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block014Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block014Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block014Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block014Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block014Head : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block014Part000
    + surrogateDiagTailX0RatChunk001Sub000Block014Part001
    + surrogateDiagTailX0RatChunk001Sub000Block014Part002
    + surrogateDiagTailX0RatChunk001Sub000Block014Part003
    + surrogateDiagTailX0RatChunk001Sub000Block014Part004
    + surrogateDiagTailX0RatChunk001Sub000Block014Part005
    + surrogateDiagTailX0RatChunk001Sub000Block014Part006
    + surrogateDiagTailX0RatChunk001Sub000Block014Part007
    + surrogateDiagTailX0RatChunk001Sub000Block014Part008
    + surrogateDiagTailX0RatChunk001Sub000Block014Part009

def surrogateDiagonalTailChunk001Sub000Block014MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block014Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block014Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block014Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block014Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block014Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block014Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block014Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block014Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block014Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block014Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block014Mid : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block014Part010
    + surrogateDiagTailX0RatChunk001Sub000Block014Part011
    + surrogateDiagTailX0RatChunk001Sub000Block014Part012
    + surrogateDiagTailX0RatChunk001Sub000Block014Part013
    + surrogateDiagTailX0RatChunk001Sub000Block014Part014
    + surrogateDiagTailX0RatChunk001Sub000Block014Part015
    + surrogateDiagTailX0RatChunk001Sub000Block014Part016
    + surrogateDiagTailX0RatChunk001Sub000Block014Part017
    + surrogateDiagTailX0RatChunk001Sub000Block014Part018
    + surrogateDiagTailX0RatChunk001Sub000Block014Part019

def surrogateDiagonalTailChunk001Sub000Block014TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block014Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block014Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block014Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block014Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block014Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block014Tail : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block014Part020
    + surrogateDiagTailX0RatChunk001Sub000Block014Part021
    + surrogateDiagTailX0RatChunk001Sub000Block014Part022
    + surrogateDiagTailX0RatChunk001Sub000Block014Part023
    + surrogateDiagTailX0RatChunk001Sub000Block014Part024

def surrogateDiagonalTailChunk001Sub000Block014Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk001Sub000Block014HeadSum X0
    + surrogateDiagonalTailChunk001Sub000Block014MidSum X0
    + surrogateDiagonalTailChunk001Sub000Block014TailSum X0

def surrogateDiagTailX0RatChunk001Sub000Block014 : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block014Part000
    + surrogateDiagTailX0RatChunk001Sub000Block014Part001
    + surrogateDiagTailX0RatChunk001Sub000Block014Part002
    + surrogateDiagTailX0RatChunk001Sub000Block014Part003
    + surrogateDiagTailX0RatChunk001Sub000Block014Part004
    + surrogateDiagTailX0RatChunk001Sub000Block014Part005
    + surrogateDiagTailX0RatChunk001Sub000Block014Part006
    + surrogateDiagTailX0RatChunk001Sub000Block014Part007
    + surrogateDiagTailX0RatChunk001Sub000Block014Part008
    + surrogateDiagTailX0RatChunk001Sub000Block014Part009
    + surrogateDiagTailX0RatChunk001Sub000Block014Part010
    + surrogateDiagTailX0RatChunk001Sub000Block014Part011
    + surrogateDiagTailX0RatChunk001Sub000Block014Part012
    + surrogateDiagTailX0RatChunk001Sub000Block014Part013
    + surrogateDiagTailX0RatChunk001Sub000Block014Part014
    + surrogateDiagTailX0RatChunk001Sub000Block014Part015
    + surrogateDiagTailX0RatChunk001Sub000Block014Part016
    + surrogateDiagTailX0RatChunk001Sub000Block014Part017
    + surrogateDiagTailX0RatChunk001Sub000Block014Part018
    + surrogateDiagTailX0RatChunk001Sub000Block014Part019
    + surrogateDiagTailX0RatChunk001Sub000Block014Part020
    + surrogateDiagTailX0RatChunk001Sub000Block014Part021
    + surrogateDiagTailX0RatChunk001Sub000Block014Part022
    + surrogateDiagTailX0RatChunk001Sub000Block014Part023
    + surrogateDiagTailX0RatChunk001Sub000Block014Part024

theorem surrogateDiagTailX0RatChunk001Sub000Block014_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk001Sub000Block014Head + surrogateDiagTailX0RatChunk001Sub000Block014Mid + surrogateDiagTailX0RatChunk001Sub000Block014Tail =
      surrogateDiagTailX0RatChunk001Sub000Block014 := by
  unfold surrogateDiagTailX0RatChunk001Sub000Block014Head surrogateDiagTailX0RatChunk001Sub000Block014Mid surrogateDiagTailX0RatChunk001Sub000Block014Tail surrogateDiagTailX0RatChunk001Sub000Block014
  ring

def SurrogateDiagonalTailChunk001Sub000Block014HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block014HeadSum X0 = surrogateDiagTailX0RatChunk001Sub000Block014Head

def SurrogateDiagonalTailChunk001Sub000Block014MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block014MidSum X0 = surrogateDiagTailX0RatChunk001Sub000Block014Mid

def SurrogateDiagonalTailChunk001Sub000Block014TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block014TailSum X0 = surrogateDiagTailX0RatChunk001Sub000Block014Tail

theorem surrogateDiagonalTailChunk001Sub000Block014_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk001Sub000Block014HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk001Sub000Block014MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk001Sub000Block014TailCertificateAt X0) :
    surrogateDiagonalTailChunk001Sub000Block014Sum X0 = surrogateDiagTailX0RatChunk001Sub000Block014 := by
  unfold SurrogateDiagonalTailChunk001Sub000Block014HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk001Sub000Block014MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk001Sub000Block014TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk001Sub000Block014Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk001Sub000Block014_eq_head_add_mid_add_tail

/-- Block 015 covers tail-support indices [10375,10400) and q from 17114 to 17153. -/

def TailChunk001Sub000Block015Part000SupportExplicit : Finset ℕ :=
  ([17114] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block015Part000 : ℚ :=
  (244158937175 : ℚ) / 664373461885632576

def SurrogateDiagonalTailChunk001Sub000Block015Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17114
    = surrogateDiagTailX0RatChunk001Sub000Block015Part000

theorem surrogateDiagonalTailChunk001Sub000Block015Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block015Part000CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block015Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block015Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block015Part000CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block015Part000SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block015Part000] using hcert

def TailChunk001Sub000Block015Part001SupportExplicit : Finset ℕ :=
  ([17115] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block015Part001 : ℚ :=
  (1673320629325 : ℚ) / 9142224179377471488

def SurrogateDiagonalTailChunk001Sub000Block015Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17115
    = surrogateDiagTailX0RatChunk001Sub000Block015Part001

theorem surrogateDiagonalTailChunk001Sub000Block015Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block015Part001CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block015Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block015Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block015Part001CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block015Part001SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block015Part001] using hcert

def TailChunk001Sub000Block015Part002SupportExplicit : Finset ℕ :=
  ([17117] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block015Part002 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block015Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17117
    = surrogateDiagTailX0RatChunk001Sub000Block015Part002

theorem surrogateDiagonalTailChunk001Sub000Block015Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block015Part002CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block015Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block015Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block015Part002CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block015Part002SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block015Part002] using hcert

def TailChunk001Sub000Block015Part003SupportExplicit : Finset ℕ :=
  ([17119] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block015Part003 : ℚ :=
  (26657033375 : ℚ) / 5240816367317286912

def SurrogateDiagonalTailChunk001Sub000Block015Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17119
    = surrogateDiagTailX0RatChunk001Sub000Block015Part003

theorem surrogateDiagonalTailChunk001Sub000Block015Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block015Part003CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block015Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block015Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block015Part003CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block015Part003SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block015Part003] using hcert

def TailChunk001Sub000Block015Part004SupportExplicit : Finset ℕ :=
  ([17121] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block015Part004 : ℚ :=
  (223317341825 : ℚ) / 3392546103711793152

def SurrogateDiagonalTailChunk001Sub000Block015Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17121
    = surrogateDiagTailX0RatChunk001Sub000Block015Part004

theorem surrogateDiagonalTailChunk001Sub000Block015Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block015Part004CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block015Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block015Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block015Part004CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block015Part004SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block015Part004] using hcert

def TailChunk001Sub000Block015Part005SupportExplicit : Finset ℕ :=
  ([17122] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block015Part005 : ℚ :=
  (374971447525 : ℚ) / 7226311592409257088

def SurrogateDiagonalTailChunk001Sub000Block015Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17122
    = surrogateDiagTailX0RatChunk001Sub000Block015Part005

theorem surrogateDiagonalTailChunk001Sub000Block015Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block015Part005CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block015Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block015Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block015Part005CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block015Part005SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block015Part005] using hcert

def TailChunk001Sub000Block015Part006SupportExplicit : Finset ℕ :=
  ([17123] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block015Part006 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block015Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17123
    = surrogateDiagTailX0RatChunk001Sub000Block015Part006

theorem surrogateDiagonalTailChunk001Sub000Block015Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block015Part006CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block015Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block015Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block015Part006CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block015Part006SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block015Part006] using hcert

def TailChunk001Sub000Block015Part007SupportExplicit : Finset ℕ :=
  ([17126] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block015Part007 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block015Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17126
    = surrogateDiagTailX0RatChunk001Sub000Block015Part007

theorem surrogateDiagonalTailChunk001Sub000Block015Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block015Part007CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block015Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block015Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block015Part007CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block015Part007SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block015Part007] using hcert

def TailChunk001Sub000Block015Part008SupportExplicit : Finset ℕ :=
  ([17129] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block015Part008 : ℚ :=
  (374794868375 : ℚ) / 57999957530122350144

def SurrogateDiagonalTailChunk001Sub000Block015Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17129
    = surrogateDiagTailX0RatChunk001Sub000Block015Part008

theorem surrogateDiagonalTailChunk001Sub000Block015Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block015Part008CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block015Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block015Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block015Part008CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block015Part008SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block015Part008] using hcert

def TailChunk001Sub000Block015Part009SupportExplicit : Finset ℕ :=
  ([17130] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block015Part009 : ℚ :=
  (13452753161 : ℚ) / 21623013786009600

def SurrogateDiagonalTailChunk001Sub000Block015Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17130
    = surrogateDiagTailX0RatChunk001Sub000Block015Part009

theorem surrogateDiagonalTailChunk001Sub000Block015Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block015Part009CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block015Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block015Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block015Part009CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block015Part009SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block015Part009] using hcert

def TailChunk001Sub000Block015Part010SupportExplicit : Finset ℕ :=
  ([17131] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block015Part010 : ℚ :=
  (22527044875 : ℚ) / 27334222431866025984

def SurrogateDiagonalTailChunk001Sub000Block015Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17131
    = surrogateDiagTailX0RatChunk001Sub000Block015Part010

theorem surrogateDiagonalTailChunk001Sub000Block015Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block015Part010CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block015Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block015Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block015Part010CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block015Part010SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block015Part010] using hcert

def TailChunk001Sub000Block015Part011SupportExplicit : Finset ℕ :=
  ([17133] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block015Part011 : ℚ :=
  (8153525179 : ℚ) / 170118390764377920

def SurrogateDiagonalTailChunk001Sub000Block015Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17133
    = surrogateDiagTailX0RatChunk001Sub000Block015Part011

theorem surrogateDiagonalTailChunk001Sub000Block015Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block015Part011CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block015Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block015Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block015Part011CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block015Part011SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block015Part011] using hcert

def TailChunk001Sub000Block015Part012SupportExplicit : Finset ℕ :=
  ([17134] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block015Part012 : ℚ :=
  (13745693425 : ℚ) / 607484826629831808

def SurrogateDiagonalTailChunk001Sub000Block015Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17134
    = surrogateDiagTailX0RatChunk001Sub000Block015Part012

theorem surrogateDiagonalTailChunk001Sub000Block015Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block015Part012CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block015Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block015Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block015Part012CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block015Part012SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block015Part012] using hcert

def TailChunk001Sub000Block015Part013SupportExplicit : Finset ℕ :=
  ([17135] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block015Part013 : ℚ :=
  (759835765925 : ℚ) / 35972814103170514944

def SurrogateDiagonalTailChunk001Sub000Block015Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17135
    = surrogateDiagTailX0RatChunk001Sub000Block015Part013

theorem surrogateDiagonalTailChunk001Sub000Block015Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block015Part013CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block015Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block015Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block015Part013CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block015Part013SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block015Part013] using hcert

def TailChunk001Sub000Block015Part014SupportExplicit : Finset ℕ :=
  ([17137] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block015Part014 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block015Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17137
    = surrogateDiagTailX0RatChunk001Sub000Block015Part014

theorem surrogateDiagonalTailChunk001Sub000Block015Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block015Part014CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block015Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block015Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block015Part014CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block015Part014SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block015Part014] using hcert

def TailChunk001Sub000Block015Part015SupportExplicit : Finset ℕ :=
  ([17138] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block015Part015 : ℚ :=
  (5374642807 : ℚ) / 89597435904000000

def SurrogateDiagonalTailChunk001Sub000Block015Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17138
    = surrogateDiagTailX0RatChunk001Sub000Block015Part015

theorem surrogateDiagonalTailChunk001Sub000Block015Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block015Part015CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block015Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block015Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block015Part015CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block015Part015SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block015Part015] using hcert

def TailChunk001Sub000Block015Part016SupportExplicit : Finset ℕ :=
  ([17139] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block015Part016 : ℚ :=
  (671672448675 : ℚ) / 12097120246991159296

def SurrogateDiagonalTailChunk001Sub000Block015Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17139
    = surrogateDiagTailX0RatChunk001Sub000Block015Part016

theorem surrogateDiagonalTailChunk001Sub000Block015Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block015Part016CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block015Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block015Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block015Part016CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block015Part016SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block015Part016] using hcert

def TailChunk001Sub000Block015Part017SupportExplicit : Finset ℕ :=
  ([17141] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block015Part017 : ℚ :=
  (426631141 : ℚ) / 796753494835200000

def SurrogateDiagonalTailChunk001Sub000Block015Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17141
    = surrogateDiagTailX0RatChunk001Sub000Block015Part017

theorem surrogateDiagonalTailChunk001Sub000Block015Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block015Part017CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block015Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block015Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block015Part017CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block015Part017SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block015Part017] using hcert

def TailChunk001Sub000Block015Part018SupportExplicit : Finset ℕ :=
  ([17142] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block015Part018 : ℚ :=
  (18229325575 : ℚ) / 95065212345901056

def SurrogateDiagonalTailChunk001Sub000Block015Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17142
    = surrogateDiagTailX0RatChunk001Sub000Block015Part018

theorem surrogateDiagonalTailChunk001Sub000Block015Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block015Part018CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block015Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block015Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block015Part018CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block015Part018SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block015Part018] using hcert

def TailChunk001Sub000Block015Part019SupportExplicit : Finset ℕ :=
  ([17143] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block015Part019 : ℚ :=
  (8833160029 : ℚ) / 971617414289932800

def SurrogateDiagonalTailChunk001Sub000Block015Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17143
    = surrogateDiagTailX0RatChunk001Sub000Block015Part019

theorem surrogateDiagonalTailChunk001Sub000Block015Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block015Part019CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block015Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block015Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block015Part019CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block015Part019SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block015Part019] using hcert

def TailChunk001Sub000Block015Part020SupportExplicit : Finset ℕ :=
  ([17146] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block015Part020 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block015Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17146
    = surrogateDiagTailX0RatChunk001Sub000Block015Part020

theorem surrogateDiagonalTailChunk001Sub000Block015Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block015Part020CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block015Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block015Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block015Part020CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block015Part020SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block015Part020] using hcert

def TailChunk001Sub000Block015Part021SupportExplicit : Finset ℕ :=
  ([17147] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block015Part021 : ℚ :=
  (82333459075 : ℚ) / 39115914914892206592

def SurrogateDiagonalTailChunk001Sub000Block015Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17147
    = surrogateDiagTailX0RatChunk001Sub000Block015Part021

theorem surrogateDiagonalTailChunk001Sub000Block015Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block015Part021CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block015Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block015Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block015Part021CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block015Part021SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block015Part021] using hcert

def TailChunk001Sub000Block015Part022SupportExplicit : Finset ℕ :=
  ([17149] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block015Part022 : ℚ :=
  (18323047687 : ℚ) / 5893274407693699200

def SurrogateDiagonalTailChunk001Sub000Block015Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17149
    = surrogateDiagTailX0RatChunk001Sub000Block015Part022

theorem surrogateDiagonalTailChunk001Sub000Block015Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block015Part022CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block015Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block015Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block015Part022CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block015Part022SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block015Part022] using hcert

def TailChunk001Sub000Block015Part023SupportExplicit : Finset ℕ :=
  ([17151] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block015Part023 : ℚ :=
  (178679675 : ℚ) / 3735885061526784

def SurrogateDiagonalTailChunk001Sub000Block015Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17151
    = surrogateDiagTailX0RatChunk001Sub000Block015Part023

theorem surrogateDiagonalTailChunk001Sub000Block015Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block015Part023CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block015Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block015Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block015Part023CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block015Part023SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block015Part023] using hcert

def TailChunk001Sub000Block015Part024SupportExplicit : Finset ℕ :=
  ([17153] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block015Part024 : ℚ :=
  (322264606525 : ℚ) / 169179960001563721728

def SurrogateDiagonalTailChunk001Sub000Block015Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17153
    = surrogateDiagTailX0RatChunk001Sub000Block015Part024

theorem surrogateDiagonalTailChunk001Sub000Block015Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block015Part024CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block015Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block015Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block015Part024CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block015Part024SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block015Part024] using hcert

def surrogateDiagonalTailChunk001Sub000Block015HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block015Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block015Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block015Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block015Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block015Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block015Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block015Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block015Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block015Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block015Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block015Head : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block015Part000
    + surrogateDiagTailX0RatChunk001Sub000Block015Part001
    + surrogateDiagTailX0RatChunk001Sub000Block015Part002
    + surrogateDiagTailX0RatChunk001Sub000Block015Part003
    + surrogateDiagTailX0RatChunk001Sub000Block015Part004
    + surrogateDiagTailX0RatChunk001Sub000Block015Part005
    + surrogateDiagTailX0RatChunk001Sub000Block015Part006
    + surrogateDiagTailX0RatChunk001Sub000Block015Part007
    + surrogateDiagTailX0RatChunk001Sub000Block015Part008
    + surrogateDiagTailX0RatChunk001Sub000Block015Part009

def surrogateDiagonalTailChunk001Sub000Block015MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block015Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block015Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block015Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block015Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block015Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block015Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block015Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block015Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block015Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block015Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block015Mid : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block015Part010
    + surrogateDiagTailX0RatChunk001Sub000Block015Part011
    + surrogateDiagTailX0RatChunk001Sub000Block015Part012
    + surrogateDiagTailX0RatChunk001Sub000Block015Part013
    + surrogateDiagTailX0RatChunk001Sub000Block015Part014
    + surrogateDiagTailX0RatChunk001Sub000Block015Part015
    + surrogateDiagTailX0RatChunk001Sub000Block015Part016
    + surrogateDiagTailX0RatChunk001Sub000Block015Part017
    + surrogateDiagTailX0RatChunk001Sub000Block015Part018
    + surrogateDiagTailX0RatChunk001Sub000Block015Part019

def surrogateDiagonalTailChunk001Sub000Block015TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block015Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block015Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block015Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block015Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block015Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block015Tail : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block015Part020
    + surrogateDiagTailX0RatChunk001Sub000Block015Part021
    + surrogateDiagTailX0RatChunk001Sub000Block015Part022
    + surrogateDiagTailX0RatChunk001Sub000Block015Part023
    + surrogateDiagTailX0RatChunk001Sub000Block015Part024

def surrogateDiagonalTailChunk001Sub000Block015Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk001Sub000Block015HeadSum X0
    + surrogateDiagonalTailChunk001Sub000Block015MidSum X0
    + surrogateDiagonalTailChunk001Sub000Block015TailSum X0

def surrogateDiagTailX0RatChunk001Sub000Block015 : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block015Part000
    + surrogateDiagTailX0RatChunk001Sub000Block015Part001
    + surrogateDiagTailX0RatChunk001Sub000Block015Part002
    + surrogateDiagTailX0RatChunk001Sub000Block015Part003
    + surrogateDiagTailX0RatChunk001Sub000Block015Part004
    + surrogateDiagTailX0RatChunk001Sub000Block015Part005
    + surrogateDiagTailX0RatChunk001Sub000Block015Part006
    + surrogateDiagTailX0RatChunk001Sub000Block015Part007
    + surrogateDiagTailX0RatChunk001Sub000Block015Part008
    + surrogateDiagTailX0RatChunk001Sub000Block015Part009
    + surrogateDiagTailX0RatChunk001Sub000Block015Part010
    + surrogateDiagTailX0RatChunk001Sub000Block015Part011
    + surrogateDiagTailX0RatChunk001Sub000Block015Part012
    + surrogateDiagTailX0RatChunk001Sub000Block015Part013
    + surrogateDiagTailX0RatChunk001Sub000Block015Part014
    + surrogateDiagTailX0RatChunk001Sub000Block015Part015
    + surrogateDiagTailX0RatChunk001Sub000Block015Part016
    + surrogateDiagTailX0RatChunk001Sub000Block015Part017
    + surrogateDiagTailX0RatChunk001Sub000Block015Part018
    + surrogateDiagTailX0RatChunk001Sub000Block015Part019
    + surrogateDiagTailX0RatChunk001Sub000Block015Part020
    + surrogateDiagTailX0RatChunk001Sub000Block015Part021
    + surrogateDiagTailX0RatChunk001Sub000Block015Part022
    + surrogateDiagTailX0RatChunk001Sub000Block015Part023
    + surrogateDiagTailX0RatChunk001Sub000Block015Part024

theorem surrogateDiagTailX0RatChunk001Sub000Block015_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk001Sub000Block015Head + surrogateDiagTailX0RatChunk001Sub000Block015Mid + surrogateDiagTailX0RatChunk001Sub000Block015Tail =
      surrogateDiagTailX0RatChunk001Sub000Block015 := by
  unfold surrogateDiagTailX0RatChunk001Sub000Block015Head surrogateDiagTailX0RatChunk001Sub000Block015Mid surrogateDiagTailX0RatChunk001Sub000Block015Tail surrogateDiagTailX0RatChunk001Sub000Block015
  ring

def SurrogateDiagonalTailChunk001Sub000Block015HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block015HeadSum X0 = surrogateDiagTailX0RatChunk001Sub000Block015Head

def SurrogateDiagonalTailChunk001Sub000Block015MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block015MidSum X0 = surrogateDiagTailX0RatChunk001Sub000Block015Mid

def SurrogateDiagonalTailChunk001Sub000Block015TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block015TailSum X0 = surrogateDiagTailX0RatChunk001Sub000Block015Tail

theorem surrogateDiagonalTailChunk001Sub000Block015_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk001Sub000Block015HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk001Sub000Block015MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk001Sub000Block015TailCertificateAt X0) :
    surrogateDiagonalTailChunk001Sub000Block015Sum X0 = surrogateDiagTailX0RatChunk001Sub000Block015 := by
  unfold SurrogateDiagonalTailChunk001Sub000Block015HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk001Sub000Block015MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk001Sub000Block015TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk001Sub000Block015Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk001Sub000Block015_eq_head_add_mid_add_tail

/-- Block 016 covers tail-support indices [10400,10425) and q from 17155 to 17195. -/

def TailChunk001Sub000Block016Part000SupportExplicit : Finset ℕ :=
  ([17155] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block016Part000 : ℚ :=
  (505636877275 : ℚ) / 25674788926270734336

def SurrogateDiagonalTailChunk001Sub000Block016Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17155
    = surrogateDiagTailX0RatChunk001Sub000Block016Part000

theorem surrogateDiagonalTailChunk001Sub000Block016Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block016Part000CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block016Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block016Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block016Part000CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block016Part000SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block016Part000] using hcert

def TailChunk001Sub000Block016Part001SupportExplicit : Finset ℕ :=
  ([17157] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block016Part001 : ℚ :=
  (226404327875 : ℚ) / 1881899884660948992

def SurrogateDiagonalTailChunk001Sub000Block016Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17157
    = surrogateDiagTailX0RatChunk001Sub000Block016Part001

theorem surrogateDiagonalTailChunk001Sub000Block016Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block016Part001CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block016Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block016Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block016Part001CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block016Part001SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block016Part001] using hcert

def TailChunk001Sub000Block016Part002SupportExplicit : Finset ℕ :=
  ([17158] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block016Part002 : ℚ :=
  (39676866125 : ℚ) / 3739108667496339456

def SurrogateDiagonalTailChunk001Sub000Block016Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17158
    = surrogateDiagTailX0RatChunk001Sub000Block016Part002

theorem surrogateDiagonalTailChunk001Sub000Block016Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block016Part002CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block016Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block016Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block016Part002CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block016Part002SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block016Part002] using hcert

def TailChunk001Sub000Block016Part003SupportExplicit : Finset ℕ :=
  ([17159] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block016Part003 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block016Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17159
    = surrogateDiagTailX0RatChunk001Sub000Block016Part003

theorem surrogateDiagonalTailChunk001Sub000Block016Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block016Part003CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block016Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block016Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block016Part003CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block016Part003SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block016Part003] using hcert

def TailChunk001Sub000Block016Part004SupportExplicit : Finset ℕ :=
  ([17162] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block016Part004 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block016Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17162
    = surrogateDiagTailX0RatChunk001Sub000Block016Part004

theorem surrogateDiagonalTailChunk001Sub000Block016Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block016Part004CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block016Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block016Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block016Part004CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block016Part004SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block016Part004] using hcert

def TailChunk001Sub000Block016Part005SupportExplicit : Finset ℕ :=
  ([17165] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block016Part005 : ℚ :=
  (491094543175 : ℚ) / 29602929179742437376

def SurrogateDiagonalTailChunk001Sub000Block016Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17165
    = surrogateDiagTailX0RatChunk001Sub000Block016Part005

theorem surrogateDiagonalTailChunk001Sub000Block016Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block016Part005CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block016Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block016Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block016Part005CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block016Part005SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block016Part005] using hcert

def TailChunk001Sub000Block016Part006SupportExplicit : Finset ℕ :=
  ([17166] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block016Part006 : ℚ :=
  (20457406979 : ℚ) / 53535389864985600

def SurrogateDiagonalTailChunk001Sub000Block016Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17166
    = surrogateDiagTailX0RatChunk001Sub000Block016Part006

theorem surrogateDiagonalTailChunk001Sub000Block016Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block016Part006CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block016Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block016Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block016Part006CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block016Part006SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block016Part006] using hcert

def TailChunk001Sub000Block016Part007SupportExplicit : Finset ℕ :=
  ([17167] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block016Part007 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block016Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17167
    = surrogateDiagTailX0RatChunk001Sub000Block016Part007

theorem surrogateDiagonalTailChunk001Sub000Block016Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block016Part007CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block016Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block016Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block016Part007CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block016Part007SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block016Part007] using hcert

def TailChunk001Sub000Block016Part008SupportExplicit : Finset ℕ :=
  ([17169] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block016Part008 : ℚ :=
  (1016485463075 : ℚ) / 19227098548487061504

def SurrogateDiagonalTailChunk001Sub000Block016Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17169
    = surrogateDiagTailX0RatChunk001Sub000Block016Part008

theorem surrogateDiagonalTailChunk001Sub000Block016Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block016Part008CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block016Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block016Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block016Part008CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block016Part008SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block016Part008] using hcert

def TailChunk001Sub000Block016Part009SupportExplicit : Finset ℕ :=
  ([17170] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block016Part009 : ℚ :=
  (124579457 : ℚ) / 839028572160000

def SurrogateDiagonalTailChunk001Sub000Block016Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17170
    = surrogateDiagTailX0RatChunk001Sub000Block016Part009

theorem surrogateDiagonalTailChunk001Sub000Block016Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block016Part009CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block016Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block016Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block016Part009CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block016Part009SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block016Part009] using hcert

def TailChunk001Sub000Block016Part010SupportExplicit : Finset ℕ :=
  ([17171] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block016Part010 : ℚ :=
  (339918911 : ℚ) / 26237503136136960

def SurrogateDiagonalTailChunk001Sub000Block016Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17171
    = surrogateDiagTailX0RatChunk001Sub000Block016Part010

theorem surrogateDiagonalTailChunk001Sub000Block016Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block016Part010CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block016Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block016Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block016Part010CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block016Part010SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block016Part010] using hcert

def TailChunk001Sub000Block016Part011SupportExplicit : Finset ℕ :=
  ([17173] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block016Part011 : ℚ :=
  (8781831677 : ℚ) / 3148310541769113600

def SurrogateDiagonalTailChunk001Sub000Block016Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17173
    = surrogateDiagTailX0RatChunk001Sub000Block016Part011

theorem surrogateDiagonalTailChunk001Sub000Block016Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block016Part011CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block016Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block016Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block016Part011CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block016Part011SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block016Part011] using hcert

def TailChunk001Sub000Block016Part012SupportExplicit : Finset ℕ :=
  ([17174] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block016Part012 : ℚ :=
  (3790605157 : ℚ) / 470119426140211200

def SurrogateDiagonalTailChunk001Sub000Block016Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17174
    = surrogateDiagTailX0RatChunk001Sub000Block016Part012

theorem surrogateDiagonalTailChunk001Sub000Block016Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block016Part012CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block016Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block016Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block016Part012CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block016Part012SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block016Part012] using hcert

def TailChunk001Sub000Block016Part013SupportExplicit : Finset ℕ :=
  ([17177] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block016Part013 : ℚ :=
  (87493083625 : ℚ) / 203780424360869756928

def SurrogateDiagonalTailChunk001Sub000Block016Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17177
    = surrogateDiagTailX0RatChunk001Sub000Block016Part013

theorem surrogateDiagonalTailChunk001Sub000Block016Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block016Part013CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block016Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block016Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block016Part013CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block016Part013SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block016Part013] using hcert

def TailChunk001Sub000Block016Part014SupportExplicit : Finset ℕ :=
  ([17178] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block016Part014 : ℚ :=
  (490752752675 : ℚ) / 718393674637246464

def SurrogateDiagonalTailChunk001Sub000Block016Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17178
    = surrogateDiagTailX0RatChunk001Sub000Block016Part014

theorem surrogateDiagonalTailChunk001Sub000Block016Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block016Part014CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block016Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block016Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block016Part014CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block016Part014SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block016Part014] using hcert

def TailChunk001Sub000Block016Part015SupportExplicit : Finset ℕ :=
  ([17179] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block016Part015 : ℚ :=
  (520944587 : ℚ) / 710622996276019200

def SurrogateDiagonalTailChunk001Sub000Block016Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17179
    = surrogateDiagTailX0RatChunk001Sub000Block016Part015

theorem surrogateDiagonalTailChunk001Sub000Block016Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block016Part015CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block016Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block016Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block016Part015CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block016Part015SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block016Part015] using hcert

def TailChunk001Sub000Block016Part016SupportExplicit : Finset ℕ :=
  ([17183] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block016Part016 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block016Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17183
    = surrogateDiagTailX0RatChunk001Sub000Block016Part016

theorem surrogateDiagonalTailChunk001Sub000Block016Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block016Part016CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block016Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block016Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block016Part016CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block016Part016SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block016Part016] using hcert

def TailChunk001Sub000Block016Part017SupportExplicit : Finset ℕ :=
  ([17185] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block016Part017 : ℚ :=
  (45321911953 : ℚ) / 1913005141099315200

def SurrogateDiagonalTailChunk001Sub000Block016Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17185
    = surrogateDiagTailX0RatChunk001Sub000Block016Part017

theorem surrogateDiagonalTailChunk001Sub000Block016Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block016Part017CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block016Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block016Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block016Part017CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block016Part017SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block016Part017] using hcert

def TailChunk001Sub000Block016Part018SupportExplicit : Finset ℕ :=
  ([17186] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block016Part018 : ℚ :=
  (176453501 : ℚ) / 8944064039116800

def SurrogateDiagonalTailChunk001Sub000Block016Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17186
    = surrogateDiagTailX0RatChunk001Sub000Block016Part018

theorem surrogateDiagonalTailChunk001Sub000Block016Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block016Part018CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block016Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block016Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block016Part018CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block016Part018SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block016Part018] using hcert

def TailChunk001Sub000Block016Part019SupportExplicit : Finset ℕ :=
  ([17187] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block016Part019 : ℚ :=
  (252616560275 : ℚ) / 4177282963001573376

def SurrogateDiagonalTailChunk001Sub000Block016Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17187
    = surrogateDiagTailX0RatChunk001Sub000Block016Part019

theorem surrogateDiagonalTailChunk001Sub000Block016Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block016Part019CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block016Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block016Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block016Part019CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block016Part019SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block016Part019] using hcert

def TailChunk001Sub000Block016Part020SupportExplicit : Finset ℕ :=
  ([17189] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block016Part020 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block016Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17189
    = surrogateDiagTailX0RatChunk001Sub000Block016Part020

theorem surrogateDiagonalTailChunk001Sub000Block016Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block016Part020CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block016Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block016Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block016Part020CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block016Part020SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block016Part020] using hcert

def TailChunk001Sub000Block016Part021SupportExplicit : Finset ℕ :=
  ([17191] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block016Part021 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block016Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17191
    = surrogateDiagTailX0RatChunk001Sub000Block016Part021

theorem surrogateDiagonalTailChunk001Sub000Block016Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block016Part021CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block016Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block016Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block016Part021CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block016Part021SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block016Part021] using hcert

def TailChunk001Sub000Block016Part022SupportExplicit : Finset ℕ :=
  ([17193] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block016Part022 : ℚ :=
  (82039572907 : ℚ) / 1170092531712000000

def SurrogateDiagonalTailChunk001Sub000Block016Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17193
    = surrogateDiagTailX0RatChunk001Sub000Block016Part022

theorem surrogateDiagonalTailChunk001Sub000Block016Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block016Part022CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block016Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block016Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block016Part022CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block016Part022SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block016Part022] using hcert

def TailChunk001Sub000Block016Part023SupportExplicit : Finset ℕ :=
  ([17194] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block016Part023 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block016Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17194
    = surrogateDiagTailX0RatChunk001Sub000Block016Part023

theorem surrogateDiagonalTailChunk001Sub000Block016Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block016Part023CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block016Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block016Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block016Part023CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block016Part023SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block016Part023] using hcert

def TailChunk001Sub000Block016Part024SupportExplicit : Finset ℕ :=
  ([17195] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block016Part024 : ℚ :=
  (4576561079 : ℚ) / 352709266179686400

def SurrogateDiagonalTailChunk001Sub000Block016Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17195
    = surrogateDiagTailX0RatChunk001Sub000Block016Part024

theorem surrogateDiagonalTailChunk001Sub000Block016Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block016Part024CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block016Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block016Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block016Part024CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block016Part024SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block016Part024] using hcert

def surrogateDiagonalTailChunk001Sub000Block016HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block016Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block016Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block016Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block016Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block016Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block016Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block016Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block016Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block016Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block016Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block016Head : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block016Part000
    + surrogateDiagTailX0RatChunk001Sub000Block016Part001
    + surrogateDiagTailX0RatChunk001Sub000Block016Part002
    + surrogateDiagTailX0RatChunk001Sub000Block016Part003
    + surrogateDiagTailX0RatChunk001Sub000Block016Part004
    + surrogateDiagTailX0RatChunk001Sub000Block016Part005
    + surrogateDiagTailX0RatChunk001Sub000Block016Part006
    + surrogateDiagTailX0RatChunk001Sub000Block016Part007
    + surrogateDiagTailX0RatChunk001Sub000Block016Part008
    + surrogateDiagTailX0RatChunk001Sub000Block016Part009

def surrogateDiagonalTailChunk001Sub000Block016MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block016Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block016Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block016Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block016Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block016Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block016Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block016Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block016Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block016Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block016Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block016Mid : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block016Part010
    + surrogateDiagTailX0RatChunk001Sub000Block016Part011
    + surrogateDiagTailX0RatChunk001Sub000Block016Part012
    + surrogateDiagTailX0RatChunk001Sub000Block016Part013
    + surrogateDiagTailX0RatChunk001Sub000Block016Part014
    + surrogateDiagTailX0RatChunk001Sub000Block016Part015
    + surrogateDiagTailX0RatChunk001Sub000Block016Part016
    + surrogateDiagTailX0RatChunk001Sub000Block016Part017
    + surrogateDiagTailX0RatChunk001Sub000Block016Part018
    + surrogateDiagTailX0RatChunk001Sub000Block016Part019

def surrogateDiagonalTailChunk001Sub000Block016TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block016Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block016Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block016Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block016Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block016Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block016Tail : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block016Part020
    + surrogateDiagTailX0RatChunk001Sub000Block016Part021
    + surrogateDiagTailX0RatChunk001Sub000Block016Part022
    + surrogateDiagTailX0RatChunk001Sub000Block016Part023
    + surrogateDiagTailX0RatChunk001Sub000Block016Part024

def surrogateDiagonalTailChunk001Sub000Block016Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk001Sub000Block016HeadSum X0
    + surrogateDiagonalTailChunk001Sub000Block016MidSum X0
    + surrogateDiagonalTailChunk001Sub000Block016TailSum X0

def surrogateDiagTailX0RatChunk001Sub000Block016 : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block016Part000
    + surrogateDiagTailX0RatChunk001Sub000Block016Part001
    + surrogateDiagTailX0RatChunk001Sub000Block016Part002
    + surrogateDiagTailX0RatChunk001Sub000Block016Part003
    + surrogateDiagTailX0RatChunk001Sub000Block016Part004
    + surrogateDiagTailX0RatChunk001Sub000Block016Part005
    + surrogateDiagTailX0RatChunk001Sub000Block016Part006
    + surrogateDiagTailX0RatChunk001Sub000Block016Part007
    + surrogateDiagTailX0RatChunk001Sub000Block016Part008
    + surrogateDiagTailX0RatChunk001Sub000Block016Part009
    + surrogateDiagTailX0RatChunk001Sub000Block016Part010
    + surrogateDiagTailX0RatChunk001Sub000Block016Part011
    + surrogateDiagTailX0RatChunk001Sub000Block016Part012
    + surrogateDiagTailX0RatChunk001Sub000Block016Part013
    + surrogateDiagTailX0RatChunk001Sub000Block016Part014
    + surrogateDiagTailX0RatChunk001Sub000Block016Part015
    + surrogateDiagTailX0RatChunk001Sub000Block016Part016
    + surrogateDiagTailX0RatChunk001Sub000Block016Part017
    + surrogateDiagTailX0RatChunk001Sub000Block016Part018
    + surrogateDiagTailX0RatChunk001Sub000Block016Part019
    + surrogateDiagTailX0RatChunk001Sub000Block016Part020
    + surrogateDiagTailX0RatChunk001Sub000Block016Part021
    + surrogateDiagTailX0RatChunk001Sub000Block016Part022
    + surrogateDiagTailX0RatChunk001Sub000Block016Part023
    + surrogateDiagTailX0RatChunk001Sub000Block016Part024

theorem surrogateDiagTailX0RatChunk001Sub000Block016_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk001Sub000Block016Head + surrogateDiagTailX0RatChunk001Sub000Block016Mid + surrogateDiagTailX0RatChunk001Sub000Block016Tail =
      surrogateDiagTailX0RatChunk001Sub000Block016 := by
  unfold surrogateDiagTailX0RatChunk001Sub000Block016Head surrogateDiagTailX0RatChunk001Sub000Block016Mid surrogateDiagTailX0RatChunk001Sub000Block016Tail surrogateDiagTailX0RatChunk001Sub000Block016
  ring

def SurrogateDiagonalTailChunk001Sub000Block016HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block016HeadSum X0 = surrogateDiagTailX0RatChunk001Sub000Block016Head

def SurrogateDiagonalTailChunk001Sub000Block016MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block016MidSum X0 = surrogateDiagTailX0RatChunk001Sub000Block016Mid

def SurrogateDiagonalTailChunk001Sub000Block016TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block016TailSum X0 = surrogateDiagTailX0RatChunk001Sub000Block016Tail

theorem surrogateDiagonalTailChunk001Sub000Block016_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk001Sub000Block016HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk001Sub000Block016MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk001Sub000Block016TailCertificateAt X0) :
    surrogateDiagonalTailChunk001Sub000Block016Sum X0 = surrogateDiagTailX0RatChunk001Sub000Block016 := by
  unfold SurrogateDiagonalTailChunk001Sub000Block016HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk001Sub000Block016MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk001Sub000Block016TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk001Sub000Block016Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk001Sub000Block016_eq_head_add_mid_add_tail

/-- Block 017 covers tail-support indices [10425,10450) and q from 17197 to 17234. -/

def TailChunk001Sub000Block017Part000SupportExplicit : Finset ℕ :=
  ([17197] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block017Part000 : ℚ :=
  (30619720875 : ℚ) / 31462596511791054848

def SurrogateDiagonalTailChunk001Sub000Block017Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17197
    = surrogateDiagTailX0RatChunk001Sub000Block017Part000

theorem surrogateDiagonalTailChunk001Sub000Block017Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block017Part000CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block017Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block017Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block017Part000CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block017Part000SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block017Part000] using hcert

def TailChunk001Sub000Block017Part001SupportExplicit : Finset ℕ :=
  ([17198] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block017Part001 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block017Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17198
    = surrogateDiagTailX0RatChunk001Sub000Block017Part001

theorem surrogateDiagonalTailChunk001Sub000Block017Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block017Part001CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block017Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block017Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block017Part001CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block017Part001SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block017Part001] using hcert

def TailChunk001Sub000Block017Part002SupportExplicit : Finset ℕ :=
  ([17201] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block017Part002 : ℚ :=
  (40597485275 : ℚ) / 102761373985170721344

def SurrogateDiagonalTailChunk001Sub000Block017Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17201
    = surrogateDiagTailX0RatChunk001Sub000Block017Part002

theorem surrogateDiagonalTailChunk001Sub000Block017Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block017Part002CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block017Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block017Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block017Part002CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block017Part002SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block017Part002] using hcert

def TailChunk001Sub000Block017Part003SupportExplicit : Finset ℕ :=
  ([17202] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block017Part003 : ℚ :=
  (40658992399 : ℚ) / 92863096521523200

def SurrogateDiagonalTailChunk001Sub000Block017Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17202
    = surrogateDiagTailX0RatChunk001Sub000Block017Part003

theorem surrogateDiagonalTailChunk001Sub000Block017Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block017Part003CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block017Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block017Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block017Part003CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block017Part003SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block017Part003] using hcert

def TailChunk001Sub000Block017Part004SupportExplicit : Finset ℕ :=
  ([17203] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block017Part004 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block017Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17203
    = surrogateDiagTailX0RatChunk001Sub000Block017Part004

theorem surrogateDiagonalTailChunk001Sub000Block017Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block017Part004CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block017Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block017Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block017Part004CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block017Part004SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block017Part004] using hcert

def TailChunk001Sub000Block017Part005SupportExplicit : Finset ℕ :=
  ([17205] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block017Part005 : ℚ :=
  (2041614157 : ℚ) / 15482436924211200

def SurrogateDiagonalTailChunk001Sub000Block017Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17205
    = surrogateDiagTailX0RatChunk001Sub000Block017Part005

theorem surrogateDiagonalTailChunk001Sub000Block017Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block017Part005CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block017Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block017Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block017Part005CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block017Part005SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block017Part005] using hcert

def TailChunk001Sub000Block017Part006SupportExplicit : Finset ℕ :=
  ([17206] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block017Part006 : ℚ :=
  (378644241925 : ℚ) / 7369284573591717888

def SurrogateDiagonalTailChunk001Sub000Block017Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17206
    = surrogateDiagTailX0RatChunk001Sub000Block017Part006

theorem surrogateDiagonalTailChunk001Sub000Block017Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block017Part006CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block017Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block017Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block017Part006CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block017Part006SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block017Part006] using hcert

def TailChunk001Sub000Block017Part007SupportExplicit : Finset ℕ :=
  ([17207] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block017Part007 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block017Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17207
    = surrogateDiagTailX0RatChunk001Sub000Block017Part007

theorem surrogateDiagonalTailChunk001Sub000Block017Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block017Part007CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block017Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block017Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block017Part007CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block017Part007SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block017Part007] using hcert

def TailChunk001Sub000Block017Part008SupportExplicit : Finset ℕ :=
  ([17209] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block017Part008 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block017Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17209
    = surrogateDiagTailX0RatChunk001Sub000Block017Part008

theorem surrogateDiagonalTailChunk001Sub000Block017Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block017Part008CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block017Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block017Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block017Part008CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block017Part008SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block017Part008] using hcert

def TailChunk001Sub000Block017Part009SupportExplicit : Finset ℕ :=
  ([17210] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block017Part009 : ℚ :=
  (11114565581 : ℚ) / 112049676622233600

def SurrogateDiagonalTailChunk001Sub000Block017Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17210
    = surrogateDiagTailX0RatChunk001Sub000Block017Part009

theorem surrogateDiagonalTailChunk001Sub000Block017Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block017Part009CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block017Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block017Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block017Part009CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block017Part009SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block017Part009] using hcert

def TailChunk001Sub000Block017Part010SupportExplicit : Finset ℕ :=
  ([17211] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block017Part010 : ℚ :=
  (514245261025 : ℚ) / 10827381039963512832

def SurrogateDiagonalTailChunk001Sub000Block017Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17211
    = surrogateDiagTailX0RatChunk001Sub000Block017Part010

theorem surrogateDiagonalTailChunk001Sub000Block017Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block017Part010CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block017Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block017Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block017Part010CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block017Part010SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block017Part010] using hcert

def TailChunk001Sub000Block017Part011SupportExplicit : Finset ℕ :=
  ([17213] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block017Part011 : ℚ :=
  (378472133075 : ℚ) / 59146544758910589504

def SurrogateDiagonalTailChunk001Sub000Block017Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17213
    = surrogateDiagTailX0RatChunk001Sub000Block017Part011

theorem surrogateDiagonalTailChunk001Sub000Block017Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block017Part011CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block017Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block017Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block017Part011CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block017Part011SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block017Part011] using hcert

def TailChunk001Sub000Block017Part012SupportExplicit : Finset ℕ :=
  ([17214] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block017Part012 : ℚ :=
  (1499640953 : ℚ) / 3149909856000000

def SurrogateDiagonalTailChunk001Sub000Block017Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17214
    = surrogateDiagTailX0RatChunk001Sub000Block017Part012

theorem surrogateDiagonalTailChunk001Sub000Block017Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block017Part012CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block017Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block017Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block017Part012CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block017Part012SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block017Part012] using hcert

def TailChunk001Sub000Block017Part013SupportExplicit : Finset ℕ :=
  ([17215] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block017Part013 : ℚ :=
  (32867243 : ℚ) / 2021919894798336

def SurrogateDiagonalTailChunk001Sub000Block017Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17215
    = surrogateDiagTailX0RatChunk001Sub000Block017Part013

theorem surrogateDiagonalTailChunk001Sub000Block017Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block017Part013CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block017Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block017Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block017Part013CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block017Part013SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block017Part013] using hcert

def TailChunk001Sub000Block017Part014SupportExplicit : Finset ℕ :=
  ([17218] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block017Part014 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block017Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17218
    = surrogateDiagTailX0RatChunk001Sub000Block017Part014

theorem surrogateDiagonalTailChunk001Sub000Block017Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block017Part014CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block017Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block017Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block017Part014CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block017Part014SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block017Part014] using hcert

def TailChunk001Sub000Block017Part015SupportExplicit : Finset ℕ :=
  ([17219] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block017Part015 : ℚ :=
  (98268164275 : ℚ) / 203780424360869756928

def SurrogateDiagonalTailChunk001Sub000Block017Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17219
    = surrogateDiagTailX0RatChunk001Sub000Block017Part015

theorem surrogateDiagonalTailChunk001Sub000Block017Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block017Part015CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block017Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block017Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block017Part015CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block017Part015SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block017Part015] using hcert

def TailChunk001Sub000Block017Part016SupportExplicit : Finset ℕ :=
  ([17221] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block017Part016 : ℚ :=
  (324787585525 : ℚ) / 171881383022190133248

def SurrogateDiagonalTailChunk001Sub000Block017Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17221
    = surrogateDiagTailX0RatChunk001Sub000Block017Part016

theorem surrogateDiagonalTailChunk001Sub000Block017Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block017Part016CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block017Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block017Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block017Part016CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block017Part016SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block017Part016] using hcert

def TailChunk001Sub000Block017Part017SupportExplicit : Finset ℕ :=
  ([17222] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block017Part017 : ℚ :=
  (2211377225 : ℚ) / 484313911122981888

def SurrogateDiagonalTailChunk001Sub000Block017Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17222
    = surrogateDiagTailX0RatChunk001Sub000Block017Part017

theorem surrogateDiagonalTailChunk001Sub000Block017Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block017Part017CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block017Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block017Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block017Part017CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block017Part017SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block017Part017] using hcert

def TailChunk001Sub000Block017Part018SupportExplicit : Finset ℕ :=
  ([17223] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block017Part018 : ℚ :=
  (5001 : ℚ) / 347374190643200

def SurrogateDiagonalTailChunk001Sub000Block017Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17223
    = surrogateDiagTailX0RatChunk001Sub000Block017Part018

theorem surrogateDiagonalTailChunk001Sub000Block017Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block017Part018CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block017Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block017Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block017Part018CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block017Part018SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block017Part018] using hcert

def TailChunk001Sub000Block017Part019SupportExplicit : Finset ℕ :=
  ([17227] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block017Part019 : ℚ :=
  (102709469675 : ℚ) / 10648870246883100672

def SurrogateDiagonalTailChunk001Sub000Block017Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17227
    = surrogateDiagTailX0RatChunk001Sub000Block017Part019

theorem surrogateDiagonalTailChunk001Sub000Block017Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block017Part019CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block017Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block017Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block017Part019CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block017Part019SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block017Part019] using hcert

def TailChunk001Sub000Block017Part020SupportExplicit : Finset ℕ :=
  ([17229] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block017Part020 : ℚ :=
  (41675 : ℚ) / 2898821574608256

def SurrogateDiagonalTailChunk001Sub000Block017Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17229
    = surrogateDiagTailX0RatChunk001Sub000Block017Part020

theorem surrogateDiagonalTailChunk001Sub000Block017Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block017Part020CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block017Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block017Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block017Part020CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block017Part020SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block017Part020] using hcert

def TailChunk001Sub000Block017Part021SupportExplicit : Finset ℕ :=
  ([17230] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block017Part021 : ℚ :=
  (19893518275 : ℚ) / 201020977885625856

def SurrogateDiagonalTailChunk001Sub000Block017Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17230
    = surrogateDiagTailX0RatChunk001Sub000Block017Part021

theorem surrogateDiagonalTailChunk001Sub000Block017Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block017Part021CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block017Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block017Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block017Part021CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block017Part021SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block017Part021] using hcert

def TailChunk001Sub000Block017Part022SupportExplicit : Finset ℕ :=
  ([17231] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block017Part022 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block017Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17231
    = surrogateDiagTailX0RatChunk001Sub000Block017Part022

theorem surrogateDiagonalTailChunk001Sub000Block017Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block017Part022CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block017Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block017Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block017Part022CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block017Part022SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block017Part022] using hcert

def TailChunk001Sub000Block017Part023SupportExplicit : Finset ℕ :=
  ([17233] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block017Part023 : ℚ :=
  (130964307275 : ℚ) / 88430010043448706624

def SurrogateDiagonalTailChunk001Sub000Block017Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17233
    = surrogateDiagTailX0RatChunk001Sub000Block017Part023

theorem surrogateDiagonalTailChunk001Sub000Block017Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block017Part023CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block017Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block017Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block017Part023CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block017Part023SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block017Part023] using hcert

def TailChunk001Sub000Block017Part024SupportExplicit : Finset ℕ :=
  ([17234] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block017Part024 : ℚ :=
  (15194900173 : ℚ) / 296696414153347200

def SurrogateDiagonalTailChunk001Sub000Block017Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17234
    = surrogateDiagTailX0RatChunk001Sub000Block017Part024

theorem surrogateDiagonalTailChunk001Sub000Block017Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block017Part024CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block017Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block017Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block017Part024CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block017Part024SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block017Part024] using hcert

def surrogateDiagonalTailChunk001Sub000Block017HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block017Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block017Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block017Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block017Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block017Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block017Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block017Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block017Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block017Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block017Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block017Head : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block017Part000
    + surrogateDiagTailX0RatChunk001Sub000Block017Part001
    + surrogateDiagTailX0RatChunk001Sub000Block017Part002
    + surrogateDiagTailX0RatChunk001Sub000Block017Part003
    + surrogateDiagTailX0RatChunk001Sub000Block017Part004
    + surrogateDiagTailX0RatChunk001Sub000Block017Part005
    + surrogateDiagTailX0RatChunk001Sub000Block017Part006
    + surrogateDiagTailX0RatChunk001Sub000Block017Part007
    + surrogateDiagTailX0RatChunk001Sub000Block017Part008
    + surrogateDiagTailX0RatChunk001Sub000Block017Part009

def surrogateDiagonalTailChunk001Sub000Block017MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block017Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block017Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block017Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block017Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block017Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block017Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block017Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block017Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block017Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block017Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block017Mid : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block017Part010
    + surrogateDiagTailX0RatChunk001Sub000Block017Part011
    + surrogateDiagTailX0RatChunk001Sub000Block017Part012
    + surrogateDiagTailX0RatChunk001Sub000Block017Part013
    + surrogateDiagTailX0RatChunk001Sub000Block017Part014
    + surrogateDiagTailX0RatChunk001Sub000Block017Part015
    + surrogateDiagTailX0RatChunk001Sub000Block017Part016
    + surrogateDiagTailX0RatChunk001Sub000Block017Part017
    + surrogateDiagTailX0RatChunk001Sub000Block017Part018
    + surrogateDiagTailX0RatChunk001Sub000Block017Part019

def surrogateDiagonalTailChunk001Sub000Block017TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block017Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block017Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block017Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block017Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block017Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block017Tail : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block017Part020
    + surrogateDiagTailX0RatChunk001Sub000Block017Part021
    + surrogateDiagTailX0RatChunk001Sub000Block017Part022
    + surrogateDiagTailX0RatChunk001Sub000Block017Part023
    + surrogateDiagTailX0RatChunk001Sub000Block017Part024

def surrogateDiagonalTailChunk001Sub000Block017Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk001Sub000Block017HeadSum X0
    + surrogateDiagonalTailChunk001Sub000Block017MidSum X0
    + surrogateDiagonalTailChunk001Sub000Block017TailSum X0

def surrogateDiagTailX0RatChunk001Sub000Block017 : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block017Part000
    + surrogateDiagTailX0RatChunk001Sub000Block017Part001
    + surrogateDiagTailX0RatChunk001Sub000Block017Part002
    + surrogateDiagTailX0RatChunk001Sub000Block017Part003
    + surrogateDiagTailX0RatChunk001Sub000Block017Part004
    + surrogateDiagTailX0RatChunk001Sub000Block017Part005
    + surrogateDiagTailX0RatChunk001Sub000Block017Part006
    + surrogateDiagTailX0RatChunk001Sub000Block017Part007
    + surrogateDiagTailX0RatChunk001Sub000Block017Part008
    + surrogateDiagTailX0RatChunk001Sub000Block017Part009
    + surrogateDiagTailX0RatChunk001Sub000Block017Part010
    + surrogateDiagTailX0RatChunk001Sub000Block017Part011
    + surrogateDiagTailX0RatChunk001Sub000Block017Part012
    + surrogateDiagTailX0RatChunk001Sub000Block017Part013
    + surrogateDiagTailX0RatChunk001Sub000Block017Part014
    + surrogateDiagTailX0RatChunk001Sub000Block017Part015
    + surrogateDiagTailX0RatChunk001Sub000Block017Part016
    + surrogateDiagTailX0RatChunk001Sub000Block017Part017
    + surrogateDiagTailX0RatChunk001Sub000Block017Part018
    + surrogateDiagTailX0RatChunk001Sub000Block017Part019
    + surrogateDiagTailX0RatChunk001Sub000Block017Part020
    + surrogateDiagTailX0RatChunk001Sub000Block017Part021
    + surrogateDiagTailX0RatChunk001Sub000Block017Part022
    + surrogateDiagTailX0RatChunk001Sub000Block017Part023
    + surrogateDiagTailX0RatChunk001Sub000Block017Part024

theorem surrogateDiagTailX0RatChunk001Sub000Block017_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk001Sub000Block017Head + surrogateDiagTailX0RatChunk001Sub000Block017Mid + surrogateDiagTailX0RatChunk001Sub000Block017Tail =
      surrogateDiagTailX0RatChunk001Sub000Block017 := by
  unfold surrogateDiagTailX0RatChunk001Sub000Block017Head surrogateDiagTailX0RatChunk001Sub000Block017Mid surrogateDiagTailX0RatChunk001Sub000Block017Tail surrogateDiagTailX0RatChunk001Sub000Block017
  ring

def SurrogateDiagonalTailChunk001Sub000Block017HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block017HeadSum X0 = surrogateDiagTailX0RatChunk001Sub000Block017Head

def SurrogateDiagonalTailChunk001Sub000Block017MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block017MidSum X0 = surrogateDiagTailX0RatChunk001Sub000Block017Mid

def SurrogateDiagonalTailChunk001Sub000Block017TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block017TailSum X0 = surrogateDiagTailX0RatChunk001Sub000Block017Tail

theorem surrogateDiagonalTailChunk001Sub000Block017_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk001Sub000Block017HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk001Sub000Block017MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk001Sub000Block017TailCertificateAt X0) :
    surrogateDiagonalTailChunk001Sub000Block017Sum X0 = surrogateDiagTailX0RatChunk001Sub000Block017 := by
  unfold SurrogateDiagonalTailChunk001Sub000Block017HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk001Sub000Block017MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk001Sub000Block017TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk001Sub000Block017Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk001Sub000Block017_eq_head_add_mid_add_tail

/-- Block 018 covers tail-support indices [10450,10475) and q from 17237 to 17277. -/

def TailChunk001Sub000Block018Part000SupportExplicit : Finset ℕ :=
  ([17237] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block018Part000 : ℚ :=
  (18510412543 : ℚ) / 6015252760726147200

def SurrogateDiagonalTailChunk001Sub000Block018Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17237
    = surrogateDiagTailX0RatChunk001Sub000Block018Part000

theorem surrogateDiagonalTailChunk001Sub000Block018Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block018Part000CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block018Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block018Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block018Part000CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block018Part000SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block018Part000] using hcert

def TailChunk001Sub000Block018Part001SupportExplicit : Finset ℕ :=
  ([17239] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block018Part001 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block018Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17239
    = surrogateDiagTailX0RatChunk001Sub000Block018Part001

theorem surrogateDiagonalTailChunk001Sub000Block018Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block018Part001CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block018Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block018Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block018Part001CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block018Part001SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block018Part001] using hcert

def TailChunk001Sub000Block018Part002SupportExplicit : Finset ℕ :=
  ([17241] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block018Part002 : ℚ :=
  (270959 : ℚ) / 12500262420480

def SurrogateDiagonalTailChunk001Sub000Block018Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17241
    = surrogateDiagTailX0RatChunk001Sub000Block018Part002

theorem surrogateDiagonalTailChunk001Sub000Block018Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block018Part002CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block018Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block018Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block018Part002CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block018Part002SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block018Part002] using hcert

def TailChunk001Sub000Block018Part003SupportExplicit : Finset ℕ :=
  ([17242] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block018Part003 : ℚ :=
  (246793328275 : ℚ) / 675952683345248256

def SurrogateDiagonalTailChunk001Sub000Block018Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17242
    = surrogateDiagTailX0RatChunk001Sub000Block018Part003

theorem surrogateDiagonalTailChunk001Sub000Block018Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block018Part003CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block018Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block018Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block018Part003CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block018Part003SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block018Part003] using hcert

def TailChunk001Sub000Block018Part004SupportExplicit : Finset ℕ :=
  ([17243] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block018Part004 : ℚ :=
  (6583277081 : ℚ) / 73773471744000000

def SurrogateDiagonalTailChunk001Sub000Block018Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17243
    = surrogateDiagTailX0RatChunk001Sub000Block018Part004

theorem surrogateDiagonalTailChunk001Sub000Block018Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block018Part004CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block018Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block018Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block018Part004CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block018Part004SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block018Part004] using hcert

def TailChunk001Sub000Block018Part005SupportExplicit : Finset ℕ :=
  ([17245] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block018Part005 : ℚ :=
  (12634187316475 : ℚ) / 90476512675952590848

def SurrogateDiagonalTailChunk001Sub000Block018Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17245
    = surrogateDiagTailX0RatChunk001Sub000Block018Part005

theorem surrogateDiagonalTailChunk001Sub000Block018Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block018Part005CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block018Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block018Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block018Part005CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block018Part005SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block018Part005] using hcert

def TailChunk001Sub000Block018Part006SupportExplicit : Finset ℕ :=
  ([17246] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block018Part006 : ℚ :=
  (1161814515625 : ℚ) / 3454609330187705682

def SurrogateDiagonalTailChunk001Sub000Block018Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17246
    = surrogateDiagTailX0RatChunk001Sub000Block018Part006

theorem surrogateDiagonalTailChunk001Sub000Block018Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block018Part006CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block018Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block018Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block018Part006CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block018Part006SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block018Part006] using hcert

def TailChunk001Sub000Block018Part007SupportExplicit : Finset ℕ :=
  ([17247] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block018Part007 : ℚ :=
  (8260500425125 : ℚ) / 43673085853237168128

def SurrogateDiagonalTailChunk001Sub000Block018Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17247
    = surrogateDiagTailX0RatChunk001Sub000Block018Part007

theorem surrogateDiagonalTailChunk001Sub000Block018Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block018Part007CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block018Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block018Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block018Part007CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block018Part007SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block018Part007] using hcert

def TailChunk001Sub000Block018Part008SupportExplicit : Finset ℕ :=
  ([17249] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block018Part008 : ℚ :=
  (17840440156075 : ℚ) / 200901198313228641408

def SurrogateDiagonalTailChunk001Sub000Block018Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17249
    = surrogateDiagTailX0RatChunk001Sub000Block018Part008

theorem surrogateDiagonalTailChunk001Sub000Block018Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block018Part008CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block018Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block018Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block018Part008CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block018Part008SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block018Part008] using hcert

def TailChunk001Sub000Block018Part009SupportExplicit : Finset ℕ :=
  ([17251] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block018Part009 : ℚ :=
  (2019919362125 : ℚ) / 20037150138002340096

def SurrogateDiagonalTailChunk001Sub000Block018Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17251
    = surrogateDiagTailX0RatChunk001Sub000Block018Part009

theorem surrogateDiagonalTailChunk001Sub000Block018Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block018Part009CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block018Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block018Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block018Part009CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block018Part009SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block018Part009] using hcert

def TailChunk001Sub000Block018Part010SupportExplicit : Finset ℕ :=
  ([17254] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block018Part010 : ℚ :=
  (1162892640625 : ℚ) / 3461024573270963922

def SurrogateDiagonalTailChunk001Sub000Block018Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17254
    = surrogateDiagTailX0RatChunk001Sub000Block018Part010

theorem surrogateDiagonalTailChunk001Sub000Block018Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block018Part010CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block018Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block018Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block018Part010CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block018Part010SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block018Part010] using hcert

def TailChunk001Sub000Block018Part011SupportExplicit : Finset ℕ :=
  ([17255] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block018Part011 : ℚ :=
  (458006623925 : ℚ) / 1856570205778477056

def SurrogateDiagonalTailChunk001Sub000Block018Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17255
    = surrogateDiagTailX0RatChunk001Sub000Block018Part011

theorem surrogateDiagonalTailChunk001Sub000Block018Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block018Part011CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block018Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block018Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block018Part011CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block018Part011SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block018Part011] using hcert

def TailChunk001Sub000Block018Part012SupportExplicit : Finset ℕ :=
  ([17257] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block018Part012 : ℚ :=
  (4653188265625 : ℚ) / 55427768693105766912

def SurrogateDiagonalTailChunk001Sub000Block018Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17257
    = surrogateDiagTailX0RatChunk001Sub000Block018Part012

theorem surrogateDiagonalTailChunk001Sub000Block018Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block018Part012CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block018Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block018Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block018Part012CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block018Part012SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block018Part012] using hcert

def TailChunk001Sub000Block018Part013SupportExplicit : Finset ℕ :=
  ([17258] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block018Part013 : ℚ :=
  (1163431890625 : ℚ) / 3464235543319110432

def SurrogateDiagonalTailChunk001Sub000Block018Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17258
    = surrogateDiagTailX0RatChunk001Sub000Block018Part013

theorem surrogateDiagonalTailChunk001Sub000Block018Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block018Part013CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block018Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block018Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block018Part013CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block018Part013SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block018Part013] using hcert

def TailChunk001Sub000Block018Part014SupportExplicit : Finset ℕ :=
  ([17259] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block018Part014 : ℚ :=
  (35282596133 : ℚ) / 148524759524102400

def SurrogateDiagonalTailChunk001Sub000Block018Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17259
    = surrogateDiagTailX0RatChunk001Sub000Block018Part014

theorem surrogateDiagonalTailChunk001Sub000Block018Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block018Part014CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block018Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block018Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block018Part014CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block018Part014SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block018Part014] using hcert

def TailChunk001Sub000Block018Part015SupportExplicit : Finset ℕ :=
  ([17261] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block018Part015 : ℚ :=
  (355507420901 : ℚ) / 3983767474176000000

def SurrogateDiagonalTailChunk001Sub000Block018Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17261
    = surrogateDiagTailX0RatChunk001Sub000Block018Part015

theorem surrogateDiagonalTailChunk001Sub000Block018Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block018Part015CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block018Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block018Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block018Part015CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block018Part015SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block018Part015] using hcert

def TailChunk001Sub000Block018Part016SupportExplicit : Finset ℕ :=
  ([17263] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block018Part016 : ℚ :=
  (79989662477 : ℚ) / 910847720061388800

def SurrogateDiagonalTailChunk001Sub000Block018Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17263
    = surrogateDiagTailX0RatChunk001Sub000Block018Part016

theorem surrogateDiagonalTailChunk001Sub000Block018Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block018Part016CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block018Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block018Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block018Part016CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block018Part016SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block018Part016] using hcert

def TailChunk001Sub000Block018Part017SupportExplicit : Finset ℕ :=
  ([17265] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block018Part017 : ℚ :=
  (28942643963 : ℚ) / 89567029824000000

def SurrogateDiagonalTailChunk001Sub000Block018Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17265
    = surrogateDiagTailX0RatChunk001Sub000Block018Part017

theorem surrogateDiagonalTailChunk001Sub000Block018Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block018Part017CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block018Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block018Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block018Part017CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block018Part017SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block018Part017] using hcert

def TailChunk001Sub000Block018Part018SupportExplicit : Finset ℕ :=
  ([17266] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block018Part018 : ℚ :=
  (205367211925 : ℚ) / 578921660116107264

def SurrogateDiagonalTailChunk001Sub000Block018Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17266
    = surrogateDiagTailX0RatChunk001Sub000Block018Part018

theorem surrogateDiagonalTailChunk001Sub000Block018Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block018Part018CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block018Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block018Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block018Part018CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block018Part018SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block018Part018] using hcert

def TailChunk001Sub000Block018Part019SupportExplicit : Finset ℕ :=
  ([17267] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block018Part019 : ℚ :=
  (14628667069 : ℚ) / 161298302921942400

def SurrogateDiagonalTailChunk001Sub000Block018Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17267
    = surrogateDiagTailX0RatChunk001Sub000Block018Part019

theorem surrogateDiagonalTailChunk001Sub000Block018Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block018Part019CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block018Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block018Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block018Part019CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block018Part019SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block018Part019] using hcert

def TailChunk001Sub000Block018Part020SupportExplicit : Finset ℕ :=
  ([17269] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block018Part020 : ℚ :=
  (14065455456025 : ℚ) / 119840648217104665728

def SurrogateDiagonalTailChunk001Sub000Block018Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17269
    = surrogateDiagTailX0RatChunk001Sub000Block018Part020

theorem surrogateDiagonalTailChunk001Sub000Block018Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block018Part020CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block018Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block018Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block018Part020CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block018Part020SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block018Part020] using hcert

def TailChunk001Sub000Block018Part021SupportExplicit : Finset ℕ :=
  ([17270] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block018Part021 : ℚ :=
  (4510255421 : ℚ) / 5832461234995200

def SurrogateDiagonalTailChunk001Sub000Block018Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17270
    = surrogateDiagTailX0RatChunk001Sub000Block018Part021

theorem surrogateDiagonalTailChunk001Sub000Block018Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block018Part021CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block018Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block018Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block018Part021CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block018Part021SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block018Part021] using hcert

def TailChunk001Sub000Block018Part022SupportExplicit : Finset ℕ :=
  ([17273] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block018Part022 : ℚ :=
  (62672850893 : ℚ) / 673953513750000000

def SurrogateDiagonalTailChunk001Sub000Block018Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17273
    = surrogateDiagTailX0RatChunk001Sub000Block018Part022

theorem surrogateDiagonalTailChunk001Sub000Block018Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block018Part022CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block018Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block018Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block018Part022CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block018Part022SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block018Part022] using hcert

def TailChunk001Sub000Block018Part023SupportExplicit : Finset ℕ :=
  ([17274] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block018Part023 : ℚ :=
  (647360064925 : ℚ) / 686198885909274912

def SurrogateDiagonalTailChunk001Sub000Block018Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17274
    = surrogateDiagTailX0RatChunk001Sub000Block018Part023

theorem surrogateDiagonalTailChunk001Sub000Block018Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block018Part023CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block018Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block018Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block018Part023CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block018Part023SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block018Part023] using hcert

def TailChunk001Sub000Block018Part024SupportExplicit : Finset ℕ :=
  ([17277] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block018Part024 : ℚ :=
  (602954081225 : ℚ) / 2638637055210184704

def SurrogateDiagonalTailChunk001Sub000Block018Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17277
    = surrogateDiagTailX0RatChunk001Sub000Block018Part024

theorem surrogateDiagonalTailChunk001Sub000Block018Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block018Part024CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block018Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block018Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block018Part024CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block018Part024SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block018Part024] using hcert

def surrogateDiagonalTailChunk001Sub000Block018HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block018Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block018Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block018Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block018Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block018Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block018Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block018Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block018Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block018Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block018Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block018Head : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block018Part000
    + surrogateDiagTailX0RatChunk001Sub000Block018Part001
    + surrogateDiagTailX0RatChunk001Sub000Block018Part002
    + surrogateDiagTailX0RatChunk001Sub000Block018Part003
    + surrogateDiagTailX0RatChunk001Sub000Block018Part004
    + surrogateDiagTailX0RatChunk001Sub000Block018Part005
    + surrogateDiagTailX0RatChunk001Sub000Block018Part006
    + surrogateDiagTailX0RatChunk001Sub000Block018Part007
    + surrogateDiagTailX0RatChunk001Sub000Block018Part008
    + surrogateDiagTailX0RatChunk001Sub000Block018Part009

def surrogateDiagonalTailChunk001Sub000Block018MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block018Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block018Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block018Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block018Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block018Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block018Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block018Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block018Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block018Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block018Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block018Mid : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block018Part010
    + surrogateDiagTailX0RatChunk001Sub000Block018Part011
    + surrogateDiagTailX0RatChunk001Sub000Block018Part012
    + surrogateDiagTailX0RatChunk001Sub000Block018Part013
    + surrogateDiagTailX0RatChunk001Sub000Block018Part014
    + surrogateDiagTailX0RatChunk001Sub000Block018Part015
    + surrogateDiagTailX0RatChunk001Sub000Block018Part016
    + surrogateDiagTailX0RatChunk001Sub000Block018Part017
    + surrogateDiagTailX0RatChunk001Sub000Block018Part018
    + surrogateDiagTailX0RatChunk001Sub000Block018Part019

def surrogateDiagonalTailChunk001Sub000Block018TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block018Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block018Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block018Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block018Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block018Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block018Tail : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block018Part020
    + surrogateDiagTailX0RatChunk001Sub000Block018Part021
    + surrogateDiagTailX0RatChunk001Sub000Block018Part022
    + surrogateDiagTailX0RatChunk001Sub000Block018Part023
    + surrogateDiagTailX0RatChunk001Sub000Block018Part024

def surrogateDiagonalTailChunk001Sub000Block018Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk001Sub000Block018HeadSum X0
    + surrogateDiagonalTailChunk001Sub000Block018MidSum X0
    + surrogateDiagonalTailChunk001Sub000Block018TailSum X0

def surrogateDiagTailX0RatChunk001Sub000Block018 : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block018Part000
    + surrogateDiagTailX0RatChunk001Sub000Block018Part001
    + surrogateDiagTailX0RatChunk001Sub000Block018Part002
    + surrogateDiagTailX0RatChunk001Sub000Block018Part003
    + surrogateDiagTailX0RatChunk001Sub000Block018Part004
    + surrogateDiagTailX0RatChunk001Sub000Block018Part005
    + surrogateDiagTailX0RatChunk001Sub000Block018Part006
    + surrogateDiagTailX0RatChunk001Sub000Block018Part007
    + surrogateDiagTailX0RatChunk001Sub000Block018Part008
    + surrogateDiagTailX0RatChunk001Sub000Block018Part009
    + surrogateDiagTailX0RatChunk001Sub000Block018Part010
    + surrogateDiagTailX0RatChunk001Sub000Block018Part011
    + surrogateDiagTailX0RatChunk001Sub000Block018Part012
    + surrogateDiagTailX0RatChunk001Sub000Block018Part013
    + surrogateDiagTailX0RatChunk001Sub000Block018Part014
    + surrogateDiagTailX0RatChunk001Sub000Block018Part015
    + surrogateDiagTailX0RatChunk001Sub000Block018Part016
    + surrogateDiagTailX0RatChunk001Sub000Block018Part017
    + surrogateDiagTailX0RatChunk001Sub000Block018Part018
    + surrogateDiagTailX0RatChunk001Sub000Block018Part019
    + surrogateDiagTailX0RatChunk001Sub000Block018Part020
    + surrogateDiagTailX0RatChunk001Sub000Block018Part021
    + surrogateDiagTailX0RatChunk001Sub000Block018Part022
    + surrogateDiagTailX0RatChunk001Sub000Block018Part023
    + surrogateDiagTailX0RatChunk001Sub000Block018Part024

theorem surrogateDiagTailX0RatChunk001Sub000Block018_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk001Sub000Block018Head + surrogateDiagTailX0RatChunk001Sub000Block018Mid + surrogateDiagTailX0RatChunk001Sub000Block018Tail =
      surrogateDiagTailX0RatChunk001Sub000Block018 := by
  unfold surrogateDiagTailX0RatChunk001Sub000Block018Head surrogateDiagTailX0RatChunk001Sub000Block018Mid surrogateDiagTailX0RatChunk001Sub000Block018Tail surrogateDiagTailX0RatChunk001Sub000Block018
  ring

def SurrogateDiagonalTailChunk001Sub000Block018HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block018HeadSum X0 = surrogateDiagTailX0RatChunk001Sub000Block018Head

def SurrogateDiagonalTailChunk001Sub000Block018MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block018MidSum X0 = surrogateDiagTailX0RatChunk001Sub000Block018Mid

def SurrogateDiagonalTailChunk001Sub000Block018TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block018TailSum X0 = surrogateDiagTailX0RatChunk001Sub000Block018Tail

theorem surrogateDiagonalTailChunk001Sub000Block018_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk001Sub000Block018HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk001Sub000Block018MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk001Sub000Block018TailCertificateAt X0) :
    surrogateDiagonalTailChunk001Sub000Block018Sum X0 = surrogateDiagTailX0RatChunk001Sub000Block018 := by
  unfold SurrogateDiagonalTailChunk001Sub000Block018HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk001Sub000Block018MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk001Sub000Block018TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk001Sub000Block018Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk001Sub000Block018_eq_head_add_mid_add_tail

/-- Block 019 covers tail-support indices [10475,10500) and q from 17278 to 17317. -/

def TailChunk001Sub000Block019Part000SupportExplicit : Finset ℕ :=
  ([17278] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block019Part000 : ℚ :=
  (750229444675 : ℚ) / 2098693614866254848

def SurrogateDiagonalTailChunk001Sub000Block019Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17278
    = surrogateDiagTailX0RatChunk001Sub000Block019Part000

theorem surrogateDiagonalTailChunk001Sub000Block019Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block019Part000CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block019Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block019Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block019Part000CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block019Part000SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block019Part000] using hcert

def TailChunk001Sub000Block019Part001SupportExplicit : Finset ℕ :=
  ([17279] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block019Part001 : ℚ :=
  (2217277328675 : ℚ) / 24756573893713479936

def SurrogateDiagonalTailChunk001Sub000Block019Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17279
    = surrogateDiagTailX0RatChunk001Sub000Block019Part001

theorem surrogateDiagonalTailChunk001Sub000Block019Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block019Part001CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block019Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block019Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block019Part001CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block019Part001SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block019Part001] using hcert

def TailChunk001Sub000Block019Part002SupportExplicit : Finset ℕ :=
  ([17281] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block019Part002 : ℚ :=
  (13098357663 : ℚ) / 126603065758375000

def SurrogateDiagonalTailChunk001Sub000Block019Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17281
    = surrogateDiagTailX0RatChunk001Sub000Block019Part002

theorem surrogateDiagonalTailChunk001Sub000Block019Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block019Part002CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block019Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block019Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block019Part002CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block019Part002SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block019Part002] using hcert

def TailChunk001Sub000Block019Part003SupportExplicit : Finset ℕ :=
  ([17282] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block019Part003 : ℚ :=
  (1866672025 : ℚ) / 5573677292716032

def SurrogateDiagonalTailChunk001Sub000Block019Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17282
    = surrogateDiagTailX0RatChunk001Sub000Block019Part003

theorem surrogateDiagonalTailChunk001Sub000Block019Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block019Part003CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block019Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block019Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block019Part003CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block019Part003SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block019Part003] using hcert

def TailChunk001Sub000Block019Part004SupportExplicit : Finset ℕ :=
  ([17283] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block019Part004 : ℚ :=
  (6422362466425 : ℚ) / 23672226808316971008

def SurrogateDiagonalTailChunk001Sub000Block019Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17283
    = surrogateDiagTailX0RatChunk001Sub000Block019Part004

theorem surrogateDiagonalTailChunk001Sub000Block019Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block019Part004CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block019Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block019Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block019Part004CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block019Part004SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block019Part004] using hcert

def TailChunk001Sub000Block019Part005SupportExplicit : Finset ℕ :=
  ([17285] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block019Part005 : ℚ :=
  (12692876840275 : ℚ) / 91319128763859468288

def SurrogateDiagonalTailChunk001Sub000Block019Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17285
    = surrogateDiagTailX0RatChunk001Sub000Block019Part005

theorem surrogateDiagonalTailChunk001Sub000Block019Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block019Part005CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block019Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block019Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block019Part005CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block019Part005SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block019Part005] using hcert

def TailChunk001Sub000Block019Part006SupportExplicit : Finset ℕ :=
  ([17286] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block019Part006 : ℚ :=
  (2466959499475 : ℚ) / 2362216753371138048

def SurrogateDiagonalTailChunk001Sub000Block019Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17286
    = surrogateDiagTailX0RatChunk001Sub000Block019Part006

theorem surrogateDiagonalTailChunk001Sub000Block019Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block019Part006CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block019Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block019Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block019Part006CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block019Part006SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block019Part006] using hcert

def TailChunk001Sub000Block019Part007SupportExplicit : Finset ℕ :=
  ([17287] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block019Part007 : ℚ :=
  (9015852290825 : ℚ) / 102858513407895266304

def SurrogateDiagonalTailChunk001Sub000Block019Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17287
    = surrogateDiagTailX0RatChunk001Sub000Block019Part007

theorem surrogateDiagonalTailChunk001Sub000Block019Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block019Part007CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block019Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block019Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block019Part007CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block019Part007SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block019Part007] using hcert

def TailChunk001Sub000Block019Part008SupportExplicit : Finset ℕ :=
  ([17290] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block019Part008 : ℚ :=
  (1136025889625 : ℚ) / 902935721419997184

def SurrogateDiagonalTailChunk001Sub000Block019Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17290
    = surrogateDiagTailX0RatChunk001Sub000Block019Part008

theorem surrogateDiagonalTailChunk001Sub000Block019Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block019Part008CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block019Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block019Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block019Part008CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block019Part008SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block019Part008] using hcert

def TailChunk001Sub000Block019Part009SupportExplicit : Finset ℕ :=
  ([17291] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block019Part009 : ℚ :=
  (7474467025 : ℚ) / 89385448439794962

def SurrogateDiagonalTailChunk001Sub000Block019Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17291
    = surrogateDiagTailX0RatChunk001Sub000Block019Part009

theorem surrogateDiagonalTailChunk001Sub000Block019Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block019Part009CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block019Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block019Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block019Part009CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block019Part009SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block019Part009] using hcert

def TailChunk001Sub000Block019Part010SupportExplicit : Finset ℕ :=
  ([17293] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block019Part010 : ℚ :=
  (4672622640625 : ℚ) / 55891758646464551712

def SurrogateDiagonalTailChunk001Sub000Block019Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17293
    = surrogateDiagTailX0RatChunk001Sub000Block019Part010

theorem surrogateDiagonalTailChunk001Sub000Block019Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block019Part010CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block019Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block019Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block019Part010CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block019Part010SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block019Part010] using hcert

def TailChunk001Sub000Block019Part011SupportExplicit : Finset ℕ :=
  ([17294] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block019Part011 : ℚ :=
  (1168290765625 : ℚ) / 3493234915404034482

def SurrogateDiagonalTailChunk001Sub000Block019Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17294
    = surrogateDiagTailX0RatChunk001Sub000Block019Part011

theorem surrogateDiagonalTailChunk001Sub000Block019Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block019Part011CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block019Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block019Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block019Part011CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block019Part011SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block019Part011] using hcert

def TailChunk001Sub000Block019Part012SupportExplicit : Finset ℕ :=
  ([17295] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block019Part012 : ℚ :=
  (1852947327725 : ℚ) / 6012782140830253056

def SurrogateDiagonalTailChunk001Sub000Block019Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17295
    = surrogateDiagTailX0RatChunk001Sub000Block019Part012

theorem surrogateDiagonalTailChunk001Sub000Block019Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block019Part012CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block019Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block019Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block019Part012CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block019Part012SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block019Part012] using hcert

def TailChunk001Sub000Block019Part013SupportExplicit : Finset ℕ :=
  ([17299] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block019Part013 : ℚ :=
  (4675865640625 : ℚ) / 55969372602697310802

def SurrogateDiagonalTailChunk001Sub000Block019Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17299
    = surrogateDiagTailX0RatChunk001Sub000Block019Part013

theorem surrogateDiagonalTailChunk001Sub000Block019Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block019Part013CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block019Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block019Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block019Part013CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block019Part013SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block019Part013] using hcert

def TailChunk001Sub000Block019Part014SupportExplicit : Finset ℕ :=
  ([17301] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block019Part014 : ℚ :=
  (7973873141725 : ℚ) / 39797449289315647488

def SurrogateDiagonalTailChunk001Sub000Block019Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17301
    = surrogateDiagTailX0RatChunk001Sub000Block019Part014

theorem surrogateDiagonalTailChunk001Sub000Block019Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block019Part014CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block019Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block019Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block019Part014CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block019Part014SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block019Part014] using hcert

def TailChunk001Sub000Block019Part015SupportExplicit : Finset ℕ :=
  ([17302] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block019Part015 : ℚ :=
  (640933381 : ℚ) / 1778467622400000

def SurrogateDiagonalTailChunk001Sub000Block019Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17302
    = surrogateDiagTailX0RatChunk001Sub000Block019Part015

theorem surrogateDiagonalTailChunk001Sub000Block019Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block019Part015CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block019Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block019Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block019Part015CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block019Part015SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block019Part015] using hcert

def TailChunk001Sub000Block019Part016SupportExplicit : Finset ℕ :=
  ([17305] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block019Part016 : ℚ :=
  (1197285025 : ℚ) / 9174263705683968

def SurrogateDiagonalTailChunk001Sub000Block019Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17305
    = surrogateDiagTailX0RatChunk001Sub000Block019Part016

theorem surrogateDiagonalTailChunk001Sub000Block019Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block019Part016CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block019Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block019Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block019Part016CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block019Part016SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block019Part016] using hcert

def TailChunk001Sub000Block019Part017SupportExplicit : Finset ℕ :=
  ([17306] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block019Part017 : ℚ :=
  (4279863503875 : ℚ) / 10913439334665289728

def SurrogateDiagonalTailChunk001Sub000Block019Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17306
    = surrogateDiagTailX0RatChunk001Sub000Block019Part017

theorem surrogateDiagonalTailChunk001Sub000Block019Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block019Part017CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block019Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block019Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block019Part017CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block019Part017SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block019Part017] using hcert

def TailChunk001Sub000Block019Part018SupportExplicit : Finset ℕ :=
  ([17309] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block019Part018 : ℚ :=
  (28391766419 : ℚ) / 300006868789882800

def SurrogateDiagonalTailChunk001Sub000Block019Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17309
    = surrogateDiagTailX0RatChunk001Sub000Block019Part018

theorem surrogateDiagonalTailChunk001Sub000Block019Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block019Part018CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block019Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block019Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block019Part018CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block019Part018SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block019Part018] using hcert

def TailChunk001Sub000Block019Part019SupportExplicit : Finset ℕ :=
  ([17310] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block019Part019 : ℚ :=
  (107290207675 : ℚ) / 62633147300315136

def SurrogateDiagonalTailChunk001Sub000Block019Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17310
    = surrogateDiagTailX0RatChunk001Sub000Block019Part019

theorem surrogateDiagonalTailChunk001Sub000Block019Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block019Part019CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block019Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block019Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block019Part019CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block019Part019SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block019Part019] using hcert

def TailChunk001Sub000Block019Part020SupportExplicit : Finset ℕ :=
  ([17311] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block019Part020 : ℚ :=
  (14133974644225 : ℚ) / 121011244156034777088

def SurrogateDiagonalTailChunk001Sub000Block019Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17311
    = surrogateDiagTailX0RatChunk001Sub000Block019Part020

theorem surrogateDiagonalTailChunk001Sub000Block019Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block019Part020CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block019Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block019Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block019Part020CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block019Part020SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block019Part020] using hcert

def TailChunk001Sub000Block019Part021SupportExplicit : Finset ℕ :=
  ([17313] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block019Part021 : ℚ :=
  (7811287755175 : ℚ) / 37795468053938208768

def SurrogateDiagonalTailChunk001Sub000Block019Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17313
    = surrogateDiagTailX0RatChunk001Sub000Block019Part021

theorem surrogateDiagonalTailChunk001Sub000Block019Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block019Part021CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block019Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block019Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block019Part021CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block019Part021SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block019Part021] using hcert

def TailChunk001Sub000Block019Part022SupportExplicit : Finset ℕ :=
  ([17314] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block019Part022 : ℚ :=
  (8116051769 : ℚ) / 19087411599776160

def SurrogateDiagonalTailChunk001Sub000Block019Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17314
    = surrogateDiagTailX0RatChunk001Sub000Block019Part022

theorem surrogateDiagonalTailChunk001Sub000Block019Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block019Part022CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block019Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block019Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block019Part022CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block019Part022SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block019Part022] using hcert

def TailChunk001Sub000Block019Part023SupportExplicit : Finset ℕ :=
  ([17315] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block019Part023 : ℚ :=
  (249722796875 : ℚ) / 1915727974009485696

def SurrogateDiagonalTailChunk001Sub000Block019Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17315
    = surrogateDiagTailX0RatChunk001Sub000Block019Part023

theorem surrogateDiagonalTailChunk001Sub000Block019Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block019Part023CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block019Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block019Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block019Part023CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block019Part023SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block019Part023] using hcert

def TailChunk001Sub000Block019Part024SupportExplicit : Finset ℕ :=
  ([17317] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block019Part024 : ℚ :=
  (4685601390625 : ℚ) / 56202699530340578592

def SurrogateDiagonalTailChunk001Sub000Block019Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17317
    = surrogateDiagTailX0RatChunk001Sub000Block019Part024

theorem surrogateDiagonalTailChunk001Sub000Block019Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block019Part024CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block019Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block019Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block019Part024CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block019Part024SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block019Part024] using hcert

def surrogateDiagonalTailChunk001Sub000Block019HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block019Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block019Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block019Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block019Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block019Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block019Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block019Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block019Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block019Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block019Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block019Head : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block019Part000
    + surrogateDiagTailX0RatChunk001Sub000Block019Part001
    + surrogateDiagTailX0RatChunk001Sub000Block019Part002
    + surrogateDiagTailX0RatChunk001Sub000Block019Part003
    + surrogateDiagTailX0RatChunk001Sub000Block019Part004
    + surrogateDiagTailX0RatChunk001Sub000Block019Part005
    + surrogateDiagTailX0RatChunk001Sub000Block019Part006
    + surrogateDiagTailX0RatChunk001Sub000Block019Part007
    + surrogateDiagTailX0RatChunk001Sub000Block019Part008
    + surrogateDiagTailX0RatChunk001Sub000Block019Part009

def surrogateDiagonalTailChunk001Sub000Block019MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block019Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block019Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block019Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block019Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block019Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block019Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block019Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block019Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block019Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block019Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block019Mid : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block019Part010
    + surrogateDiagTailX0RatChunk001Sub000Block019Part011
    + surrogateDiagTailX0RatChunk001Sub000Block019Part012
    + surrogateDiagTailX0RatChunk001Sub000Block019Part013
    + surrogateDiagTailX0RatChunk001Sub000Block019Part014
    + surrogateDiagTailX0RatChunk001Sub000Block019Part015
    + surrogateDiagTailX0RatChunk001Sub000Block019Part016
    + surrogateDiagTailX0RatChunk001Sub000Block019Part017
    + surrogateDiagTailX0RatChunk001Sub000Block019Part018
    + surrogateDiagTailX0RatChunk001Sub000Block019Part019

def surrogateDiagonalTailChunk001Sub000Block019TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block019Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block019Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block019Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block019Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block019Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block019Tail : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block019Part020
    + surrogateDiagTailX0RatChunk001Sub000Block019Part021
    + surrogateDiagTailX0RatChunk001Sub000Block019Part022
    + surrogateDiagTailX0RatChunk001Sub000Block019Part023
    + surrogateDiagTailX0RatChunk001Sub000Block019Part024

def surrogateDiagonalTailChunk001Sub000Block019Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk001Sub000Block019HeadSum X0
    + surrogateDiagonalTailChunk001Sub000Block019MidSum X0
    + surrogateDiagonalTailChunk001Sub000Block019TailSum X0

def surrogateDiagTailX0RatChunk001Sub000Block019 : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block019Part000
    + surrogateDiagTailX0RatChunk001Sub000Block019Part001
    + surrogateDiagTailX0RatChunk001Sub000Block019Part002
    + surrogateDiagTailX0RatChunk001Sub000Block019Part003
    + surrogateDiagTailX0RatChunk001Sub000Block019Part004
    + surrogateDiagTailX0RatChunk001Sub000Block019Part005
    + surrogateDiagTailX0RatChunk001Sub000Block019Part006
    + surrogateDiagTailX0RatChunk001Sub000Block019Part007
    + surrogateDiagTailX0RatChunk001Sub000Block019Part008
    + surrogateDiagTailX0RatChunk001Sub000Block019Part009
    + surrogateDiagTailX0RatChunk001Sub000Block019Part010
    + surrogateDiagTailX0RatChunk001Sub000Block019Part011
    + surrogateDiagTailX0RatChunk001Sub000Block019Part012
    + surrogateDiagTailX0RatChunk001Sub000Block019Part013
    + surrogateDiagTailX0RatChunk001Sub000Block019Part014
    + surrogateDiagTailX0RatChunk001Sub000Block019Part015
    + surrogateDiagTailX0RatChunk001Sub000Block019Part016
    + surrogateDiagTailX0RatChunk001Sub000Block019Part017
    + surrogateDiagTailX0RatChunk001Sub000Block019Part018
    + surrogateDiagTailX0RatChunk001Sub000Block019Part019
    + surrogateDiagTailX0RatChunk001Sub000Block019Part020
    + surrogateDiagTailX0RatChunk001Sub000Block019Part021
    + surrogateDiagTailX0RatChunk001Sub000Block019Part022
    + surrogateDiagTailX0RatChunk001Sub000Block019Part023
    + surrogateDiagTailX0RatChunk001Sub000Block019Part024

theorem surrogateDiagTailX0RatChunk001Sub000Block019_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk001Sub000Block019Head + surrogateDiagTailX0RatChunk001Sub000Block019Mid + surrogateDiagTailX0RatChunk001Sub000Block019Tail =
      surrogateDiagTailX0RatChunk001Sub000Block019 := by
  unfold surrogateDiagTailX0RatChunk001Sub000Block019Head surrogateDiagTailX0RatChunk001Sub000Block019Mid surrogateDiagTailX0RatChunk001Sub000Block019Tail surrogateDiagTailX0RatChunk001Sub000Block019
  ring

def SurrogateDiagonalTailChunk001Sub000Block019HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block019HeadSum X0 = surrogateDiagTailX0RatChunk001Sub000Block019Head

def SurrogateDiagonalTailChunk001Sub000Block019MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block019MidSum X0 = surrogateDiagTailX0RatChunk001Sub000Block019Mid

def SurrogateDiagonalTailChunk001Sub000Block019TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block019TailSum X0 = surrogateDiagTailX0RatChunk001Sub000Block019Tail

theorem surrogateDiagonalTailChunk001Sub000Block019_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk001Sub000Block019HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk001Sub000Block019MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk001Sub000Block019TailCertificateAt X0) :
    surrogateDiagonalTailChunk001Sub000Block019Sum X0 = surrogateDiagTailX0RatChunk001Sub000Block019 := by
  unfold SurrogateDiagonalTailChunk001Sub000Block019HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk001Sub000Block019MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk001Sub000Block019TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk001Sub000Block019Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk001Sub000Block019_eq_head_add_mid_add_tail

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

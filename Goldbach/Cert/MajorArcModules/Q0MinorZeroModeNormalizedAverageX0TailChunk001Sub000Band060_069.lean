import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0TailPilot25

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

open scoped BigOperators

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

/- Generated direct-term certificate blocks for tail chunk 001, subchunk 000, blocks [60,70). -/

/-- Block 060 covers tail-support indices [11500,11525) and q from 18965 to 19003. -/

def TailChunk001Sub000Block060Part000SupportExplicit : Finset ℕ :=
  ([18965] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block060Part000 : ℚ :=
  (599432835175 : ℚ) / 44118311643377565696

def SurrogateDiagonalTailChunk001Sub000Block060Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18965
    = surrogateDiagTailX0RatChunk001Sub000Block060Part000

theorem surrogateDiagonalTailChunk001Sub000Block060Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block060Part000CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block060Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block060Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block060Part000CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block060Part000SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block060Part000] using hcert

def TailChunk001Sub000Block060Part001SupportExplicit : Finset ℕ :=
  ([18966] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block060Part001 : ℚ :=
  (1183363980125 : ℚ) / 1672799897476399104

def SurrogateDiagonalTailChunk001Sub000Block060Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18966
    = surrogateDiagTailX0RatChunk001Sub000Block060Part001

theorem surrogateDiagonalTailChunk001Sub000Block060Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block060Part001CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block060Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block060Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block060Part001CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block060Part001SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block060Part001] using hcert

def TailChunk001Sub000Block060Part002SupportExplicit : Finset ℕ :=
  ([18967] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block060Part002 : ℚ :=
  (267437484425 : ℚ) / 117152603204874200064

def SurrogateDiagonalTailChunk001Sub000Block060Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18967
    = surrogateDiagTailX0RatChunk001Sub000Block060Part002

theorem surrogateDiagonalTailChunk001Sub000Block060Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block060Part002CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block060Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block060Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block060Part002CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block060Part002SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block060Part002] using hcert

def TailChunk001Sub000Block060Part003SupportExplicit : Finset ℕ :=
  ([18969] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block060Part003 : ℚ :=
  (125025 : ℚ) / 12779326114590848

def SurrogateDiagonalTailChunk001Sub000Block060Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18969
    = surrogateDiagTailX0RatChunk001Sub000Block060Part003

theorem surrogateDiagonalTailChunk001Sub000Block060Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block060Part003CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block060Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block060Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block060Part003CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block060Part003SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block060Part003] using hcert

def TailChunk001Sub000Block060Part004SupportExplicit : Finset ℕ :=
  ([18970] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block060Part004 : ℚ :=
  (7913277571 : ℚ) / 11022164568115200

def SurrogateDiagonalTailChunk001Sub000Block060Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18970
    = surrogateDiagTailX0RatChunk001Sub000Block060Part004

theorem surrogateDiagonalTailChunk001Sub000Block060Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block060Part004CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block060Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block060Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block060Part004CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block060Part004SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block060Part004] using hcert

def TailChunk001Sub000Block060Part005SupportExplicit : Finset ℕ :=
  ([18971] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block060Part005 : ℚ :=
  (1527597029 : ℚ) / 3990408642144000000

def SurrogateDiagonalTailChunk001Sub000Block060Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18971
    = surrogateDiagTailX0RatChunk001Sub000Block060Part005

theorem surrogateDiagonalTailChunk001Sub000Block060Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block060Part005CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block060Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block060Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block060Part005CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block060Part005SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block060Part005] using hcert

def TailChunk001Sub000Block060Part006SupportExplicit : Finset ℕ :=
  ([18973] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block060Part006 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block060Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18973
    = surrogateDiagTailX0RatChunk001Sub000Block060Part006

theorem surrogateDiagonalTailChunk001Sub000Block060Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block060Part006CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block060Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block060Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block060Part006CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block060Part006SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block060Part006] using hcert

def TailChunk001Sub000Block060Part007SupportExplicit : Finset ℕ :=
  ([18974] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block060Part007 : ℚ :=
  (5425092007225 : ℚ) / 18353556904243611648

def SurrogateDiagonalTailChunk001Sub000Block060Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18974
    = surrogateDiagTailX0RatChunk001Sub000Block060Part007

theorem surrogateDiagonalTailChunk001Sub000Block060Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block060Part007CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block060Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block060Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block060Part007CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block060Part007SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block060Part007] using hcert

def TailChunk001Sub000Block060Part008SupportExplicit : Finset ℕ :=
  ([18977] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block060Part008 : ℚ :=
  (18394074407 : ℚ) / 3495739159718337600

def SurrogateDiagonalTailChunk001Sub000Block060Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18977
    = surrogateDiagTailX0RatChunk001Sub000Block060Part008

theorem surrogateDiagonalTailChunk001Sub000Block060Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block060Part008CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block060Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block060Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block060Part008CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block060Part008SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block060Part008] using hcert

def TailChunk001Sub000Block060Part009SupportExplicit : Finset ℕ :=
  ([18978] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block060Part009 : ℚ :=
  (2500185683725 : ℚ) / 3999395042406108288

def SurrogateDiagonalTailChunk001Sub000Block060Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18978
    = surrogateDiagTailX0RatChunk001Sub000Block060Part009

theorem surrogateDiagonalTailChunk001Sub000Block060Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block060Part009CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block060Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block060Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block060Part009CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block060Part009SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block060Part009] using hcert

def TailChunk001Sub000Block060Part010SupportExplicit : Finset ℕ :=
  ([18979] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block060Part010 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block060Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18979
    = surrogateDiagTailX0RatChunk001Sub000Block060Part010

theorem surrogateDiagonalTailChunk001Sub000Block060Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block060Part010CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block060Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block060Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block060Part010CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block060Part010SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block060Part010] using hcert

def TailChunk001Sub000Block060Part011SupportExplicit : Finset ℕ :=
  ([18982] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block060Part011 : ℚ :=
  (2251977025 : ℚ) / 8112443776332402

def SurrogateDiagonalTailChunk001Sub000Block060Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18982
    = surrogateDiagTailX0RatChunk001Sub000Block060Part011

theorem surrogateDiagonalTailChunk001Sub000Block060Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block060Part011CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block060Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block060Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block060Part011CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block060Part011SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block060Part011] using hcert

def TailChunk001Sub000Block060Part012SupportExplicit : Finset ℕ :=
  ([18983] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block060Part012 : ℚ :=
  (1059696593 : ℚ) / 1944211319647027200

def SurrogateDiagonalTailChunk001Sub000Block060Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18983
    = surrogateDiagTailX0RatChunk001Sub000Block060Part012

theorem surrogateDiagonalTailChunk001Sub000Block060Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block060Part012CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block060Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block060Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block060Part012CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block060Part012SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block060Part012] using hcert

def TailChunk001Sub000Block060Part013SupportExplicit : Finset ℕ :=
  ([18985] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block060Part013 : ℚ :=
  (300617237625 : ℚ) / 44304759610476691456

def SurrogateDiagonalTailChunk001Sub000Block060Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18985
    = surrogateDiagTailX0RatChunk001Sub000Block060Part013

theorem surrogateDiagonalTailChunk001Sub000Block060Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block060Part013CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block060Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block060Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block060Part013CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block060Part013SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block060Part013] using hcert

def TailChunk001Sub000Block060Part014SupportExplicit : Finset ℕ :=
  ([18986] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block060Part014 : ℚ :=
  (1626697041 : ℚ) / 4601873406776560

def SurrogateDiagonalTailChunk001Sub000Block060Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18986
    = surrogateDiagTailX0RatChunk001Sub000Block060Part014

theorem surrogateDiagonalTailChunk001Sub000Block060Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block060Part014CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block060Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block060Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block060Part014CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block060Part014SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block060Part014] using hcert

def TailChunk001Sub000Block060Part015SupportExplicit : Finset ℕ :=
  ([18987] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block060Part015 : ℚ :=
  (125025 : ℚ) / 12827908956520448

def SurrogateDiagonalTailChunk001Sub000Block060Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18987
    = surrogateDiagTailX0RatChunk001Sub000Block060Part015

theorem surrogateDiagonalTailChunk001Sub000Block060Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block060Part015CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block060Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block060Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block060Part015CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block060Part015SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block060Part015] using hcert

def TailChunk001Sub000Block060Part016SupportExplicit : Finset ℕ :=
  ([18989] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block060Part016 : ℚ :=
  (393892231525 : ℚ) / 254192988989945806848

def SurrogateDiagonalTailChunk001Sub000Block060Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18989
    = surrogateDiagTailX0RatChunk001Sub000Block060Part016

theorem surrogateDiagonalTailChunk001Sub000Block060Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block060Part016CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block060Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block060Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block060Part016CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block060Part016SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block060Part016] using hcert

def TailChunk001Sub000Block060Part017SupportExplicit : Finset ℕ :=
  ([18991] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block060Part017 : ℚ :=
  (460529474675 : ℚ) / 87651752859083096064

def SurrogateDiagonalTailChunk001Sub000Block060Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18991
    = surrogateDiagTailX0RatChunk001Sub000Block060Part017

theorem surrogateDiagonalTailChunk001Sub000Block060Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block060Part017CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block060Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block060Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block060Part017CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block060Part017SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block060Part017] using hcert

def TailChunk001Sub000Block060Part018SupportExplicit : Finset ℕ :=
  ([18993] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block060Part018 : ℚ :=
  (2399027224975 : ℚ) / 46282509908098449408

def SurrogateDiagonalTailChunk001Sub000Block060Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18993
    = surrogateDiagTailX0RatChunk001Sub000Block060Part018

theorem surrogateDiagonalTailChunk001Sub000Block060Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block060Part018CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block060Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block060Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block060Part018CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block060Part018SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block060Part018] using hcert

def TailChunk001Sub000Block060Part019SupportExplicit : Finset ℕ :=
  ([18994] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block060Part019 : ℚ :=
  (1409265765625 : ℚ) / 5083112145125356032

def SurrogateDiagonalTailChunk001Sub000Block060Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18994
    = surrogateDiagTailX0RatChunk001Sub000Block060Part019

theorem surrogateDiagonalTailChunk001Sub000Block060Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block060Part019CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block060Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block060Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block060Part019CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block060Part019SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block060Part019] using hcert

def TailChunk001Sub000Block060Part020SupportExplicit : Finset ℕ :=
  ([18995] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block060Part020 : ℚ :=
  (31647461 : ℚ) / 3511740210800640

def SurrogateDiagonalTailChunk001Sub000Block060Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18995
    = surrogateDiagTailX0RatChunk001Sub000Block060Part020

theorem surrogateDiagonalTailChunk001Sub000Block060Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block060Part020CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block060Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block060Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block060Part020CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block060Part020SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block060Part020] using hcert

def TailChunk001Sub000Block060Part021SupportExplicit : Finset ℕ :=
  ([18998] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block060Part021 : ℚ :=
  (4107233610925 : ℚ) / 8590818781994600448

def SurrogateDiagonalTailChunk001Sub000Block060Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18998
    = surrogateDiagTailX0RatChunk001Sub000Block060Part021

theorem surrogateDiagonalTailChunk001Sub000Block060Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block060Part021CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block060Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block060Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block060Part021CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block060Part021SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block060Part021] using hcert

def TailChunk001Sub000Block060Part022SupportExplicit : Finset ℕ :=
  ([19001] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block060Part022 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block060Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19001
    = surrogateDiagTailX0RatChunk001Sub000Block060Part022

theorem surrogateDiagonalTailChunk001Sub000Block060Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block060Part022CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block060Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block060Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block060Part022CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block060Part022SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block060Part022] using hcert

def TailChunk001Sub000Block060Part023SupportExplicit : Finset ℕ :=
  ([19002] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block060Part023 : ℚ :=
  (783371821525 : ℚ) / 1004917692201130272

def SurrogateDiagonalTailChunk001Sub000Block060Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19002
    = surrogateDiagTailX0RatChunk001Sub000Block060Part023

theorem surrogateDiagonalTailChunk001Sub000Block060Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block060Part023CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block060Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block060Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block060Part023CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block060Part023SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block060Part023] using hcert

def TailChunk001Sub000Block060Part024SupportExplicit : Finset ℕ :=
  ([19003] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block060Part024 : ℚ :=
  (61365683 : ℚ) / 88790722115504400

def SurrogateDiagonalTailChunk001Sub000Block060Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19003
    = surrogateDiagTailX0RatChunk001Sub000Block060Part024

theorem surrogateDiagonalTailChunk001Sub000Block060Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block060Part024CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block060Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block060Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block060Part024CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block060Part024SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block060Part024] using hcert

def surrogateDiagonalTailChunk001Sub000Block060HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block060Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block060Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block060Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block060Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block060Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block060Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block060Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block060Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block060Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block060Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block060Head : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block060Part000
    + surrogateDiagTailX0RatChunk001Sub000Block060Part001
    + surrogateDiagTailX0RatChunk001Sub000Block060Part002
    + surrogateDiagTailX0RatChunk001Sub000Block060Part003
    + surrogateDiagTailX0RatChunk001Sub000Block060Part004
    + surrogateDiagTailX0RatChunk001Sub000Block060Part005
    + surrogateDiagTailX0RatChunk001Sub000Block060Part006
    + surrogateDiagTailX0RatChunk001Sub000Block060Part007
    + surrogateDiagTailX0RatChunk001Sub000Block060Part008
    + surrogateDiagTailX0RatChunk001Sub000Block060Part009

def surrogateDiagonalTailChunk001Sub000Block060MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block060Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block060Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block060Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block060Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block060Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block060Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block060Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block060Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block060Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block060Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block060Mid : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block060Part010
    + surrogateDiagTailX0RatChunk001Sub000Block060Part011
    + surrogateDiagTailX0RatChunk001Sub000Block060Part012
    + surrogateDiagTailX0RatChunk001Sub000Block060Part013
    + surrogateDiagTailX0RatChunk001Sub000Block060Part014
    + surrogateDiagTailX0RatChunk001Sub000Block060Part015
    + surrogateDiagTailX0RatChunk001Sub000Block060Part016
    + surrogateDiagTailX0RatChunk001Sub000Block060Part017
    + surrogateDiagTailX0RatChunk001Sub000Block060Part018
    + surrogateDiagTailX0RatChunk001Sub000Block060Part019

def surrogateDiagonalTailChunk001Sub000Block060TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block060Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block060Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block060Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block060Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block060Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block060Tail : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block060Part020
    + surrogateDiagTailX0RatChunk001Sub000Block060Part021
    + surrogateDiagTailX0RatChunk001Sub000Block060Part022
    + surrogateDiagTailX0RatChunk001Sub000Block060Part023
    + surrogateDiagTailX0RatChunk001Sub000Block060Part024

def surrogateDiagonalTailChunk001Sub000Block060Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk001Sub000Block060HeadSum X0
    + surrogateDiagonalTailChunk001Sub000Block060MidSum X0
    + surrogateDiagonalTailChunk001Sub000Block060TailSum X0

def surrogateDiagTailX0RatChunk001Sub000Block060 : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block060Part000
    + surrogateDiagTailX0RatChunk001Sub000Block060Part001
    + surrogateDiagTailX0RatChunk001Sub000Block060Part002
    + surrogateDiagTailX0RatChunk001Sub000Block060Part003
    + surrogateDiagTailX0RatChunk001Sub000Block060Part004
    + surrogateDiagTailX0RatChunk001Sub000Block060Part005
    + surrogateDiagTailX0RatChunk001Sub000Block060Part006
    + surrogateDiagTailX0RatChunk001Sub000Block060Part007
    + surrogateDiagTailX0RatChunk001Sub000Block060Part008
    + surrogateDiagTailX0RatChunk001Sub000Block060Part009
    + surrogateDiagTailX0RatChunk001Sub000Block060Part010
    + surrogateDiagTailX0RatChunk001Sub000Block060Part011
    + surrogateDiagTailX0RatChunk001Sub000Block060Part012
    + surrogateDiagTailX0RatChunk001Sub000Block060Part013
    + surrogateDiagTailX0RatChunk001Sub000Block060Part014
    + surrogateDiagTailX0RatChunk001Sub000Block060Part015
    + surrogateDiagTailX0RatChunk001Sub000Block060Part016
    + surrogateDiagTailX0RatChunk001Sub000Block060Part017
    + surrogateDiagTailX0RatChunk001Sub000Block060Part018
    + surrogateDiagTailX0RatChunk001Sub000Block060Part019
    + surrogateDiagTailX0RatChunk001Sub000Block060Part020
    + surrogateDiagTailX0RatChunk001Sub000Block060Part021
    + surrogateDiagTailX0RatChunk001Sub000Block060Part022
    + surrogateDiagTailX0RatChunk001Sub000Block060Part023
    + surrogateDiagTailX0RatChunk001Sub000Block060Part024

theorem surrogateDiagTailX0RatChunk001Sub000Block060_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk001Sub000Block060Head + surrogateDiagTailX0RatChunk001Sub000Block060Mid + surrogateDiagTailX0RatChunk001Sub000Block060Tail =
      surrogateDiagTailX0RatChunk001Sub000Block060 := by
  unfold surrogateDiagTailX0RatChunk001Sub000Block060Head surrogateDiagTailX0RatChunk001Sub000Block060Mid surrogateDiagTailX0RatChunk001Sub000Block060Tail surrogateDiagTailX0RatChunk001Sub000Block060
  ring

def SurrogateDiagonalTailChunk001Sub000Block060HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block060HeadSum X0 = surrogateDiagTailX0RatChunk001Sub000Block060Head

def SurrogateDiagonalTailChunk001Sub000Block060MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block060MidSum X0 = surrogateDiagTailX0RatChunk001Sub000Block060Mid

def SurrogateDiagonalTailChunk001Sub000Block060TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block060TailSum X0 = surrogateDiagTailX0RatChunk001Sub000Block060Tail

theorem surrogateDiagonalTailChunk001Sub000Block060_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk001Sub000Block060HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk001Sub000Block060MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk001Sub000Block060TailCertificateAt X0) :
    surrogateDiagonalTailChunk001Sub000Block060Sum X0 = surrogateDiagTailX0RatChunk001Sub000Block060 := by
  unfold SurrogateDiagonalTailChunk001Sub000Block060HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk001Sub000Block060MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk001Sub000Block060TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk001Sub000Block060Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk001Sub000Block060_eq_head_add_mid_add_tail

/-- Block 061 covers tail-support indices [11525,11550) and q from 19005 to 19042. -/

def TailChunk001Sub000Block061Part000SupportExplicit : Finset ℕ :=
  ([19005] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block061Part000 : ℚ :=
  (20563071481 : ℚ) / 139341932317900800

def SurrogateDiagonalTailChunk001Sub000Block061Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19005
    = surrogateDiagTailX0RatChunk001Sub000Block061Part000

theorem surrogateDiagonalTailChunk001Sub000Block061Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block061Part000CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block061Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block061Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block061Part000CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block061Part000SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block061Part000] using hcert

def TailChunk001Sub000Block061Part001SupportExplicit : Finset ℕ :=
  ([19006] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block061Part001 : ℚ :=
  (1476962357075 : ℚ) / 3524582500032577536

def SurrogateDiagonalTailChunk001Sub000Block061Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19006
    = surrogateDiagTailX0RatChunk001Sub000Block061Part001

theorem surrogateDiagonalTailChunk001Sub000Block061Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block061Part001CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block061Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block061Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block061Part001CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block061Part001SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block061Part001] using hcert

def TailChunk001Sub000Block061Part002SupportExplicit : Finset ℕ :=
  ([19007] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block061Part002 : ℚ :=
  (96705208975 : ℚ) / 305507345294841366528

def SurrogateDiagonalTailChunk001Sub000Block061Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19007
    = surrogateDiagTailX0RatChunk001Sub000Block061Part002

theorem surrogateDiagonalTailChunk001Sub000Block061Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block061Part002CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block061Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block061Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block061Part002CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block061Part002SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block061Part002] using hcert

def TailChunk001Sub000Block061Part003SupportExplicit : Finset ℕ :=
  ([19009] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block061Part003 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block061Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19009
    = surrogateDiagTailX0RatChunk001Sub000Block061Part003

theorem surrogateDiagonalTailChunk001Sub000Block061Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block061Part003CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block061Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block061Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block061Part003CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block061Part003SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block061Part003] using hcert

def TailChunk001Sub000Block061Part004SupportExplicit : Finset ℕ :=
  ([19010] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block061Part004 : ℚ :=
  (153489453199 : ℚ) / 333688484352000000

def SurrogateDiagonalTailChunk001Sub000Block061Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19010
    = surrogateDiagTailX0RatChunk001Sub000Block061Part004

theorem surrogateDiagonalTailChunk001Sub000Block061Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block061Part004CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block061Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block061Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block061Part004CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block061Part004SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block061Part004] using hcert

def TailChunk001Sub000Block061Part005SupportExplicit : Finset ℕ :=
  ([19011] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block061Part005 : ℚ :=
  (627420257275 : ℚ) / 16119349973857861632

def SurrogateDiagonalTailChunk001Sub000Block061Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19011
    = surrogateDiagTailX0RatChunk001Sub000Block061Part005

theorem surrogateDiagonalTailChunk001Sub000Block061Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block061Part005CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block061Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block061Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block061Part005CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block061Part005SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block061Part005] using hcert

def TailChunk001Sub000Block061Part006SupportExplicit : Finset ℕ :=
  ([19013] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block061Part006 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block061Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19013
    = surrogateDiagTailX0RatChunk001Sub000Block061Part006

theorem surrogateDiagonalTailChunk001Sub000Block061Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block061Part006CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block061Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block061Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block061Part006CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block061Part006SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block061Part006] using hcert

def TailChunk001Sub000Block061Part007SupportExplicit : Finset ℕ :=
  ([19014] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block061Part007 : ℚ :=
  (1568723334725 : ℚ) / 2014918746732232704

def SurrogateDiagonalTailChunk001Sub000Block061Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19014
    = surrogateDiagTailX0RatChunk001Sub000Block061Part007

theorem surrogateDiagonalTailChunk001Sub000Block061Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block061Part007CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block061Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block061Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block061Part007CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block061Part007SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block061Part007] using hcert

def TailChunk001Sub000Block061Part008SupportExplicit : Finset ℕ :=
  ([19015] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block061Part008 : ℚ :=
  (301566987375 : ℚ) / 44585538830112495616

def SurrogateDiagonalTailChunk001Sub000Block061Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19015
    = surrogateDiagTailX0RatChunk001Sub000Block061Part008

theorem surrogateDiagonalTailChunk001Sub000Block061Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block061Part008CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block061Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block061Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block061Part008CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block061Part008SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block061Part008] using hcert

def TailChunk001Sub000Block061Part009SupportExplicit : Finset ℕ :=
  ([19018] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block061Part009 : ℚ :=
  (24972738275 : ℚ) / 83510863067086848

def SurrogateDiagonalTailChunk001Sub000Block061Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19018
    = surrogateDiagTailX0RatChunk001Sub000Block061Part009

theorem surrogateDiagonalTailChunk001Sub000Block061Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block061Part009CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block061Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block061Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block061Part009CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block061Part009SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block061Part009] using hcert

def TailChunk001Sub000Block061Part010SupportExplicit : Finset ℕ :=
  ([19019] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block061Part010 : ℚ :=
  (3283049741 : ℚ) / 188111608629166080

def SurrogateDiagonalTailChunk001Sub000Block061Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19019
    = surrogateDiagTailX0RatChunk001Sub000Block061Part010

theorem surrogateDiagonalTailChunk001Sub000Block061Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block061Part010CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block061Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block061Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block061Part010CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block061Part010SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block061Part010] using hcert

def TailChunk001Sub000Block061Part011SupportExplicit : Finset ℕ :=
  ([19021] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block061Part011 : ℚ :=
  (23860217225 : ℚ) / 24788205408722034048

def SurrogateDiagonalTailChunk001Sub000Block061Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19021
    = surrogateDiagTailX0RatChunk001Sub000Block061Part011

theorem surrogateDiagonalTailChunk001Sub000Block061Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block061Part011CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block061Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block061Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block061Part011CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block061Part011SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block061Part011] using hcert

def TailChunk001Sub000Block061Part012SupportExplicit : Finset ℕ :=
  ([19022] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block061Part012 : ℚ :=
  (2261478025 : ℚ) / 8181047570347602

def SurrogateDiagonalTailChunk001Sub000Block061Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19022
    = surrogateDiagTailX0RatChunk001Sub000Block061Part012

theorem surrogateDiagonalTailChunk001Sub000Block061Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block061Part012CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block061Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block061Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block061Part012CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block061Part012SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block061Part012] using hcert

def TailChunk001Sub000Block061Part013SupportExplicit : Finset ℕ :=
  ([19023] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block061Part013 : ℚ :=
  (2457509397025 : ℚ) / 50210960788137443328

def SurrogateDiagonalTailChunk001Sub000Block061Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19023
    = surrogateDiagTailX0RatChunk001Sub000Block061Part013

theorem surrogateDiagonalTailChunk001Sub000Block061Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block061Part013CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block061Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block061Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block061Part013CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block061Part013SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block061Part013] using hcert

def TailChunk001Sub000Block061Part014SupportExplicit : Finset ℕ :=
  ([19027] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block061Part014 : ℚ :=
  (4931150225 : ℚ) / 11550452328863904768

def SurrogateDiagonalTailChunk001Sub000Block061Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19027
    = surrogateDiagTailX0RatChunk001Sub000Block061Part014

theorem surrogateDiagonalTailChunk001Sub000Block061Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block061Part014CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block061Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block061Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block061Part014CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block061Part014SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block061Part014] using hcert

def TailChunk001Sub000Block061Part015SupportExplicit : Finset ℕ :=
  ([19029] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block061Part015 : ℚ :=
  (179602519925 : ℚ) / 4622998543652325312

def SurrogateDiagonalTailChunk001Sub000Block061Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19029
    = surrogateDiagTailX0RatChunk001Sub000Block061Part015

theorem surrogateDiagonalTailChunk001Sub000Block061Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block061Part015CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block061Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block061Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block061Part015CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block061Part015SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block061Part015] using hcert

def TailChunk001Sub000Block061Part016SupportExplicit : Finset ℕ :=
  ([19030] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block061Part016 : ℚ :=
  (28000439573 : ℚ) / 44819870648893440

def SurrogateDiagonalTailChunk001Sub000Block061Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19030
    = surrogateDiagTailX0RatChunk001Sub000Block061Part016

theorem surrogateDiagonalTailChunk001Sub000Block061Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block061Part016CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block061Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block061Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block061Part016CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block061Part016SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block061Part016] using hcert

def TailChunk001Sub000Block061Part017SupportExplicit : Finset ℕ :=
  ([19031] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block061Part017 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block061Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19031
    = surrogateDiagTailX0RatChunk001Sub000Block061Part017

theorem surrogateDiagonalTailChunk001Sub000Block061Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block061Part017CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block061Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block061Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block061Part017CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block061Part017SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block061Part017] using hcert

def TailChunk001Sub000Block061Part018SupportExplicit : Finset ℕ :=
  ([19033] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block061Part018 : ℚ :=
  (462565317575 : ℚ) / 88430010043448706624

def SurrogateDiagonalTailChunk001Sub000Block061Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19033
    = surrogateDiagTailX0RatChunk001Sub000Block061Part018

theorem surrogateDiagonalTailChunk001Sub000Block061Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block061Part018CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block061Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block061Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block061Part018CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block061Part018SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block061Part018] using hcert

def TailChunk001Sub000Block061Part019SupportExplicit : Finset ℕ :=
  ([19034] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block061Part019 : ℚ :=
  (21459667627 : ℚ) / 71032577692403520

def SurrogateDiagonalTailChunk001Sub000Block061Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19034
    = surrogateDiagTailX0RatChunk001Sub000Block061Part019

theorem surrogateDiagonalTailChunk001Sub000Block061Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block061Part019CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block061Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block061Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block061Part019CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block061Part019SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block061Part019] using hcert

def TailChunk001Sub000Block061Part020SupportExplicit : Finset ℕ :=
  ([19037] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block061Part020 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block061Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19037
    = surrogateDiagTailX0RatChunk001Sub000Block061Part020

theorem surrogateDiagonalTailChunk001Sub000Block061Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block061Part020CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block061Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block061Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block061Part020CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block061Part020SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block061Part020] using hcert

def TailChunk001Sub000Block061Part021SupportExplicit : Finset ℕ :=
  ([19038] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block061Part021 : ℚ :=
  (1444732490525 : ℚ) / 1594553952715858944

def SurrogateDiagonalTailChunk001Sub000Block061Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19038
    = surrogateDiagTailX0RatChunk001Sub000Block061Part021

theorem surrogateDiagonalTailChunk001Sub000Block061Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block061Part021CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block061Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block061Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block061Part021CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block061Part021SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block061Part021] using hcert

def TailChunk001Sub000Block061Part022SupportExplicit : Finset ℕ :=
  ([19039] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block061Part022 : ℚ :=
  (11062877 : ℚ) / 34119898224721920

def SurrogateDiagonalTailChunk001Sub000Block061Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19039
    = surrogateDiagTailX0RatChunk001Sub000Block061Part022

theorem surrogateDiagonalTailChunk001Sub000Block061Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block061Part022CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block061Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block061Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block061Part022CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block061Part022SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block061Part022] using hcert

def TailChunk001Sub000Block061Part023SupportExplicit : Finset ℕ :=
  ([19041] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block061Part023 : ℚ :=
  (97293911851 : ℚ) / 1761557267821363200

def SurrogateDiagonalTailChunk001Sub000Block061Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19041
    = surrogateDiagTailX0RatChunk001Sub000Block061Part023

theorem surrogateDiagonalTailChunk001Sub000Block061Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block061Part023CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block061Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block061Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block061Part023CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block061Part023SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block061Part023] using hcert

def TailChunk001Sub000Block061Part024SupportExplicit : Finset ℕ :=
  ([19042] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block061Part024 : ℚ :=
  (2266236025 : ℚ) / 8215512178040832

def SurrogateDiagonalTailChunk001Sub000Block061Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19042
    = surrogateDiagTailX0RatChunk001Sub000Block061Part024

theorem surrogateDiagonalTailChunk001Sub000Block061Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block061Part024CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block061Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block061Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block061Part024CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block061Part024SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block061Part024] using hcert

def surrogateDiagonalTailChunk001Sub000Block061HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block061Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block061Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block061Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block061Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block061Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block061Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block061Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block061Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block061Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block061Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block061Head : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block061Part000
    + surrogateDiagTailX0RatChunk001Sub000Block061Part001
    + surrogateDiagTailX0RatChunk001Sub000Block061Part002
    + surrogateDiagTailX0RatChunk001Sub000Block061Part003
    + surrogateDiagTailX0RatChunk001Sub000Block061Part004
    + surrogateDiagTailX0RatChunk001Sub000Block061Part005
    + surrogateDiagTailX0RatChunk001Sub000Block061Part006
    + surrogateDiagTailX0RatChunk001Sub000Block061Part007
    + surrogateDiagTailX0RatChunk001Sub000Block061Part008
    + surrogateDiagTailX0RatChunk001Sub000Block061Part009

def surrogateDiagonalTailChunk001Sub000Block061MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block061Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block061Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block061Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block061Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block061Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block061Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block061Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block061Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block061Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block061Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block061Mid : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block061Part010
    + surrogateDiagTailX0RatChunk001Sub000Block061Part011
    + surrogateDiagTailX0RatChunk001Sub000Block061Part012
    + surrogateDiagTailX0RatChunk001Sub000Block061Part013
    + surrogateDiagTailX0RatChunk001Sub000Block061Part014
    + surrogateDiagTailX0RatChunk001Sub000Block061Part015
    + surrogateDiagTailX0RatChunk001Sub000Block061Part016
    + surrogateDiagTailX0RatChunk001Sub000Block061Part017
    + surrogateDiagTailX0RatChunk001Sub000Block061Part018
    + surrogateDiagTailX0RatChunk001Sub000Block061Part019

def surrogateDiagonalTailChunk001Sub000Block061TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block061Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block061Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block061Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block061Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block061Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block061Tail : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block061Part020
    + surrogateDiagTailX0RatChunk001Sub000Block061Part021
    + surrogateDiagTailX0RatChunk001Sub000Block061Part022
    + surrogateDiagTailX0RatChunk001Sub000Block061Part023
    + surrogateDiagTailX0RatChunk001Sub000Block061Part024

def surrogateDiagonalTailChunk001Sub000Block061Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk001Sub000Block061HeadSum X0
    + surrogateDiagonalTailChunk001Sub000Block061MidSum X0
    + surrogateDiagonalTailChunk001Sub000Block061TailSum X0

def surrogateDiagTailX0RatChunk001Sub000Block061 : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block061Part000
    + surrogateDiagTailX0RatChunk001Sub000Block061Part001
    + surrogateDiagTailX0RatChunk001Sub000Block061Part002
    + surrogateDiagTailX0RatChunk001Sub000Block061Part003
    + surrogateDiagTailX0RatChunk001Sub000Block061Part004
    + surrogateDiagTailX0RatChunk001Sub000Block061Part005
    + surrogateDiagTailX0RatChunk001Sub000Block061Part006
    + surrogateDiagTailX0RatChunk001Sub000Block061Part007
    + surrogateDiagTailX0RatChunk001Sub000Block061Part008
    + surrogateDiagTailX0RatChunk001Sub000Block061Part009
    + surrogateDiagTailX0RatChunk001Sub000Block061Part010
    + surrogateDiagTailX0RatChunk001Sub000Block061Part011
    + surrogateDiagTailX0RatChunk001Sub000Block061Part012
    + surrogateDiagTailX0RatChunk001Sub000Block061Part013
    + surrogateDiagTailX0RatChunk001Sub000Block061Part014
    + surrogateDiagTailX0RatChunk001Sub000Block061Part015
    + surrogateDiagTailX0RatChunk001Sub000Block061Part016
    + surrogateDiagTailX0RatChunk001Sub000Block061Part017
    + surrogateDiagTailX0RatChunk001Sub000Block061Part018
    + surrogateDiagTailX0RatChunk001Sub000Block061Part019
    + surrogateDiagTailX0RatChunk001Sub000Block061Part020
    + surrogateDiagTailX0RatChunk001Sub000Block061Part021
    + surrogateDiagTailX0RatChunk001Sub000Block061Part022
    + surrogateDiagTailX0RatChunk001Sub000Block061Part023
    + surrogateDiagTailX0RatChunk001Sub000Block061Part024

theorem surrogateDiagTailX0RatChunk001Sub000Block061_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk001Sub000Block061Head + surrogateDiagTailX0RatChunk001Sub000Block061Mid + surrogateDiagTailX0RatChunk001Sub000Block061Tail =
      surrogateDiagTailX0RatChunk001Sub000Block061 := by
  unfold surrogateDiagTailX0RatChunk001Sub000Block061Head surrogateDiagTailX0RatChunk001Sub000Block061Mid surrogateDiagTailX0RatChunk001Sub000Block061Tail surrogateDiagTailX0RatChunk001Sub000Block061
  ring

def SurrogateDiagonalTailChunk001Sub000Block061HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block061HeadSum X0 = surrogateDiagTailX0RatChunk001Sub000Block061Head

def SurrogateDiagonalTailChunk001Sub000Block061MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block061MidSum X0 = surrogateDiagTailX0RatChunk001Sub000Block061Mid

def SurrogateDiagonalTailChunk001Sub000Block061TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block061TailSum X0 = surrogateDiagTailX0RatChunk001Sub000Block061Tail

theorem surrogateDiagonalTailChunk001Sub000Block061_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk001Sub000Block061HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk001Sub000Block061MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk001Sub000Block061TailCertificateAt X0) :
    surrogateDiagonalTailChunk001Sub000Block061Sum X0 = surrogateDiagTailX0RatChunk001Sub000Block061 := by
  unfold SurrogateDiagonalTailChunk001Sub000Block061HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk001Sub000Block061MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk001Sub000Block061TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk001Sub000Block061Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk001Sub000Block061_eq_head_add_mid_add_tail

/-- Block 062 covers tail-support indices [11550,11575) and q from 19043 to 19085. -/

def TailChunk001Sub000Block062Part000SupportExplicit : Finset ℕ :=
  ([19043] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block062Part000 : ℚ :=
  (10703077625 : ℚ) / 38780093422870695936

def SurrogateDiagonalTailChunk001Sub000Block062Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19043
    = surrogateDiagTailX0RatChunk001Sub000Block062Part000

theorem surrogateDiagonalTailChunk001Sub000Block062Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block062Part000CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block062Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block062Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block062Part000CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block062Part000SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block062Part000] using hcert

def TailChunk001Sub000Block062Part001SupportExplicit : Finset ℕ :=
  ([19045] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block062Part001 : ℚ :=
  (369179634125 : ℚ) / 32166363057415520256

def SurrogateDiagonalTailChunk001Sub000Block062Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19045
    = surrogateDiagTailX0RatChunk001Sub000Block062Part001

theorem surrogateDiagonalTailChunk001Sub000Block062Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block062Part001CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block062Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block062Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block062Part001CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block062Part001SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block062Part001] using hcert

def TailChunk001Sub000Block062Part002SupportExplicit : Finset ℕ :=
  ([19046] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block062Part002 : ℚ :=
  (1832930928825 : ℚ) / 6310441627782578176

def SurrogateDiagonalTailChunk001Sub000Block062Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19046
    = surrogateDiagTailX0RatChunk001Sub000Block062Part002

theorem surrogateDiagonalTailChunk001Sub000Block062Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block062Part002CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block062Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block062Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block062Part002CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block062Part002SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block062Part002] using hcert

def TailChunk001Sub000Block062Part003SupportExplicit : Finset ℕ :=
  ([19047] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block062Part003 : ℚ :=
  (590866027675 : ℚ) / 8733828152439378432

def SurrogateDiagonalTailChunk001Sub000Block062Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19047
    = surrogateDiagTailX0RatChunk001Sub000Block062Part003

theorem surrogateDiagonalTailChunk001Sub000Block062Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block062Part003CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block062Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block062Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block062Part003CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block062Part003SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block062Part003] using hcert

def TailChunk001Sub000Block062Part004SupportExplicit : Finset ℕ :=
  ([19049] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block062Part004 : ℚ :=
  (9202848325 : ℚ) / 18560647176444297288

def SurrogateDiagonalTailChunk001Sub000Block062Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19049
    = surrogateDiagTailX0RatChunk001Sub000Block062Part004

theorem surrogateDiagonalTailChunk001Sub000Block062Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block062Part004CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block062Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block062Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block062Part004CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block062Part004SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block062Part004] using hcert

def TailChunk001Sub000Block062Part005SupportExplicit : Finset ℕ :=
  ([19051] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block062Part005 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block062Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19051
    = surrogateDiagTailX0RatChunk001Sub000Block062Part005

theorem surrogateDiagonalTailChunk001Sub000Block062Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block062Part005CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block062Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block062Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block062Part005CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block062Part005SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block062Part005] using hcert

def TailChunk001Sub000Block062Part006SupportExplicit : Finset ℕ :=
  ([19054] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block062Part006 : ℚ :=
  (10024367471 : ℚ) / 24636271421030400

def SurrogateDiagonalTailChunk001Sub000Block062Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19054
    = surrogateDiagTailX0RatChunk001Sub000Block062Part006

theorem surrogateDiagonalTailChunk001Sub000Block062Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block062Part006CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block062Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block062Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block062Part006CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block062Part006SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block062Part006] using hcert

def TailChunk001Sub000Block062Part007SupportExplicit : Finset ℕ :=
  ([19055] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block062Part007 : ℚ :=
  (1015689022825 : ℚ) / 116379775291233927168

def SurrogateDiagonalTailChunk001Sub000Block062Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19055
    = surrogateDiagTailX0RatChunk001Sub000Block062Part007

theorem surrogateDiagonalTailChunk001Sub000Block062Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block062Part007CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block062Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block062Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block062Part007CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block062Part007SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block062Part007] using hcert

def TailChunk001Sub000Block062Part008SupportExplicit : Finset ℕ :=
  ([19057] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block062Part008 : ℚ :=
  (162487138975 : ℚ) / 48668593200857874432

def SurrogateDiagonalTailChunk001Sub000Block062Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19057
    = surrogateDiagTailX0RatChunk001Sub000Block062Part008

theorem surrogateDiagonalTailChunk001Sub000Block062Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block062Part008CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block062Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block062Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block062Part008CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block062Part008SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block062Part008] using hcert

def TailChunk001Sub000Block062Part009SupportExplicit : Finset ℕ :=
  ([19058] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block062Part009 : ℚ :=
  (204485842375 : ℚ) / 14886622218413703168

def SurrogateDiagonalTailChunk001Sub000Block062Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19058
    = surrogateDiagTailX0RatChunk001Sub000Block062Part009

theorem surrogateDiagonalTailChunk001Sub000Block062Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block062Part009CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block062Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block062Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block062Part009CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block062Part009SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block062Part009] using hcert

def TailChunk001Sub000Block062Part010SupportExplicit : Finset ℕ :=
  ([19059] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block062Part010 : ℚ :=
  (630592257175 : ℚ) / 16282789478646546432

def SurrogateDiagonalTailChunk001Sub000Block062Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19059
    = surrogateDiagTailX0RatChunk001Sub000Block062Part010

theorem surrogateDiagonalTailChunk001Sub000Block062Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block062Part010CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block062Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block062Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block062Part010CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block062Part010SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block062Part010] using hcert

def TailChunk001Sub000Block062Part011SupportExplicit : Finset ℕ :=
  ([19063] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block062Part011 : ℚ :=
  (22614776653 : ℚ) / 9000743819782195200

def SurrogateDiagonalTailChunk001Sub000Block062Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19063
    = surrogateDiagTailX0RatChunk001Sub000Block062Part011

theorem surrogateDiagonalTailChunk001Sub000Block062Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block062Part011CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block062Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block062Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block062Part011CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block062Part011SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block062Part011] using hcert

def TailChunk001Sub000Block062Part012SupportExplicit : Finset ℕ :=
  ([19065] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block062Part012 : ℚ :=
  (7163589901 : ℚ) / 70793035776000000

def SurrogateDiagonalTailChunk001Sub000Block062Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19065
    = surrogateDiagTailX0RatChunk001Sub000Block062Part012

theorem surrogateDiagonalTailChunk001Sub000Block062Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block062Part012CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block062Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block062Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block062Part012CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block062Part012SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block062Part012] using hcert

def TailChunk001Sub000Block062Part013SupportExplicit : Finset ℕ :=
  ([19066] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block062Part013 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block062Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19066
    = surrogateDiagTailX0RatChunk001Sub000Block062Part013

theorem surrogateDiagonalTailChunk001Sub000Block062Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block062Part013CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block062Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block062Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block062Part013CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block062Part013SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block062Part013] using hcert

def TailChunk001Sub000Block062Part014SupportExplicit : Finset ℕ :=
  ([19067] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block062Part014 : ℚ :=
  (263701650175 : ℚ) / 275320740724753287168

def SurrogateDiagonalTailChunk001Sub000Block062Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19067
    = surrogateDiagTailX0RatChunk001Sub000Block062Part014

theorem surrogateDiagonalTailChunk001Sub000Block062Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block062Part014CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block062Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block062Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block062Part014CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block062Part014SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block062Part014] using hcert

def TailChunk001Sub000Block062Part015SupportExplicit : Finset ℕ :=
  ([19069] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block062Part015 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block062Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19069
    = surrogateDiagTailX0RatChunk001Sub000Block062Part015

theorem surrogateDiagonalTailChunk001Sub000Block062Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block062Part015CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block062Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block062Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block062Part015CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block062Part015SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block062Part015] using hcert

def TailChunk001Sub000Block062Part016SupportExplicit : Finset ℕ :=
  ([19070] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block062Part016 : ℚ :=
  (455264232025 : ℚ) / 8448087617521010688

def SurrogateDiagonalTailChunk001Sub000Block062Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19070
    = surrogateDiagTailX0RatChunk001Sub000Block062Part016

theorem surrogateDiagonalTailChunk001Sub000Block062Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block062Part016CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block062Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block062Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block062Part016CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block062Part016SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block062Part016] using hcert

def TailChunk001Sub000Block062Part017SupportExplicit : Finset ℕ :=
  ([19073] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block062Part017 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block062Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19073
    = surrogateDiagTailX0RatChunk001Sub000Block062Part017

theorem surrogateDiagonalTailChunk001Sub000Block062Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block062Part017CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block062Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block062Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block062Part017CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block062Part017SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block062Part017] using hcert

def TailChunk001Sub000Block062Part018SupportExplicit : Finset ℕ :=
  ([19077] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block062Part018 : ℚ :=
  (1263567639275 : ℚ) / 32688797154118315584

def SurrogateDiagonalTailChunk001Sub000Block062Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19077
    = surrogateDiagTailX0RatChunk001Sub000Block062Part018

theorem surrogateDiagonalTailChunk001Sub000Block062Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block062Part018CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block062Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block062Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block062Part018CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block062Part018SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block062Part018] using hcert

def TailChunk001Sub000Block062Part019SupportExplicit : Finset ℕ :=
  ([19078] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block062Part019 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block062Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19078
    = surrogateDiagTailX0RatChunk001Sub000Block062Part019

theorem surrogateDiagonalTailChunk001Sub000Block062Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block062Part019CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block062Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block062Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block062Part019CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block062Part019SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block062Part019] using hcert

def TailChunk001Sub000Block062Part020SupportExplicit : Finset ℕ :=
  ([19079] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block062Part020 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block062Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19079
    = surrogateDiagTailX0RatChunk001Sub000Block062Part020

theorem surrogateDiagonalTailChunk001Sub000Block062Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block062Part020CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block062Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block062Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block062Part020CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block062Part020SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block062Part020] using hcert

def TailChunk001Sub000Block062Part021SupportExplicit : Finset ℕ :=
  ([19081] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block062Part021 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block062Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19081
    = surrogateDiagTailX0RatChunk001Sub000Block062Part021

theorem surrogateDiagonalTailChunk001Sub000Block062Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block062Part021CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block062Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block062Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block062Part021CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block062Part021SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block062Part021] using hcert

def TailChunk001Sub000Block062Part022SupportExplicit : Finset ℕ :=
  ([19082] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block062Part022 : ℚ :=
  (30476691575 : ℚ) / 495476210551504896

def SurrogateDiagonalTailChunk001Sub000Block062Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19082
    = surrogateDiagTailX0RatChunk001Sub000Block062Part022

theorem surrogateDiagonalTailChunk001Sub000Block062Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block062Part022CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block062Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block062Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block062Part022CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block062Part022SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block062Part022] using hcert

def TailChunk001Sub000Block062Part023SupportExplicit : Finset ℕ :=
  ([19083] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block062Part023 : ℚ :=
  (5057450057 : ℚ) / 130919789935042560

def SurrogateDiagonalTailChunk001Sub000Block062Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19083
    = surrogateDiagTailX0RatChunk001Sub000Block062Part023

theorem surrogateDiagonalTailChunk001Sub000Block062Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block062Part023CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block062Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block062Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block062Part023CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block062Part023SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block062Part023] using hcert

def TailChunk001Sub000Block062Part024SupportExplicit : Finset ℕ :=
  ([19085] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block062Part024 : ℚ :=
  (77703099883 : ℚ) / 3669705482273587200

def SurrogateDiagonalTailChunk001Sub000Block062Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19085
    = surrogateDiagTailX0RatChunk001Sub000Block062Part024

theorem surrogateDiagonalTailChunk001Sub000Block062Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block062Part024CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block062Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block062Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block062Part024CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block062Part024SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block062Part024] using hcert

def surrogateDiagonalTailChunk001Sub000Block062HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block062Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block062Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block062Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block062Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block062Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block062Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block062Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block062Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block062Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block062Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block062Head : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block062Part000
    + surrogateDiagTailX0RatChunk001Sub000Block062Part001
    + surrogateDiagTailX0RatChunk001Sub000Block062Part002
    + surrogateDiagTailX0RatChunk001Sub000Block062Part003
    + surrogateDiagTailX0RatChunk001Sub000Block062Part004
    + surrogateDiagTailX0RatChunk001Sub000Block062Part005
    + surrogateDiagTailX0RatChunk001Sub000Block062Part006
    + surrogateDiagTailX0RatChunk001Sub000Block062Part007
    + surrogateDiagTailX0RatChunk001Sub000Block062Part008
    + surrogateDiagTailX0RatChunk001Sub000Block062Part009

def surrogateDiagonalTailChunk001Sub000Block062MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block062Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block062Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block062Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block062Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block062Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block062Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block062Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block062Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block062Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block062Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block062Mid : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block062Part010
    + surrogateDiagTailX0RatChunk001Sub000Block062Part011
    + surrogateDiagTailX0RatChunk001Sub000Block062Part012
    + surrogateDiagTailX0RatChunk001Sub000Block062Part013
    + surrogateDiagTailX0RatChunk001Sub000Block062Part014
    + surrogateDiagTailX0RatChunk001Sub000Block062Part015
    + surrogateDiagTailX0RatChunk001Sub000Block062Part016
    + surrogateDiagTailX0RatChunk001Sub000Block062Part017
    + surrogateDiagTailX0RatChunk001Sub000Block062Part018
    + surrogateDiagTailX0RatChunk001Sub000Block062Part019

def surrogateDiagonalTailChunk001Sub000Block062TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block062Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block062Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block062Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block062Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block062Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block062Tail : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block062Part020
    + surrogateDiagTailX0RatChunk001Sub000Block062Part021
    + surrogateDiagTailX0RatChunk001Sub000Block062Part022
    + surrogateDiagTailX0RatChunk001Sub000Block062Part023
    + surrogateDiagTailX0RatChunk001Sub000Block062Part024

def surrogateDiagonalTailChunk001Sub000Block062Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk001Sub000Block062HeadSum X0
    + surrogateDiagonalTailChunk001Sub000Block062MidSum X0
    + surrogateDiagonalTailChunk001Sub000Block062TailSum X0

def surrogateDiagTailX0RatChunk001Sub000Block062 : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block062Part000
    + surrogateDiagTailX0RatChunk001Sub000Block062Part001
    + surrogateDiagTailX0RatChunk001Sub000Block062Part002
    + surrogateDiagTailX0RatChunk001Sub000Block062Part003
    + surrogateDiagTailX0RatChunk001Sub000Block062Part004
    + surrogateDiagTailX0RatChunk001Sub000Block062Part005
    + surrogateDiagTailX0RatChunk001Sub000Block062Part006
    + surrogateDiagTailX0RatChunk001Sub000Block062Part007
    + surrogateDiagTailX0RatChunk001Sub000Block062Part008
    + surrogateDiagTailX0RatChunk001Sub000Block062Part009
    + surrogateDiagTailX0RatChunk001Sub000Block062Part010
    + surrogateDiagTailX0RatChunk001Sub000Block062Part011
    + surrogateDiagTailX0RatChunk001Sub000Block062Part012
    + surrogateDiagTailX0RatChunk001Sub000Block062Part013
    + surrogateDiagTailX0RatChunk001Sub000Block062Part014
    + surrogateDiagTailX0RatChunk001Sub000Block062Part015
    + surrogateDiagTailX0RatChunk001Sub000Block062Part016
    + surrogateDiagTailX0RatChunk001Sub000Block062Part017
    + surrogateDiagTailX0RatChunk001Sub000Block062Part018
    + surrogateDiagTailX0RatChunk001Sub000Block062Part019
    + surrogateDiagTailX0RatChunk001Sub000Block062Part020
    + surrogateDiagTailX0RatChunk001Sub000Block062Part021
    + surrogateDiagTailX0RatChunk001Sub000Block062Part022
    + surrogateDiagTailX0RatChunk001Sub000Block062Part023
    + surrogateDiagTailX0RatChunk001Sub000Block062Part024

theorem surrogateDiagTailX0RatChunk001Sub000Block062_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk001Sub000Block062Head + surrogateDiagTailX0RatChunk001Sub000Block062Mid + surrogateDiagTailX0RatChunk001Sub000Block062Tail =
      surrogateDiagTailX0RatChunk001Sub000Block062 := by
  unfold surrogateDiagTailX0RatChunk001Sub000Block062Head surrogateDiagTailX0RatChunk001Sub000Block062Mid surrogateDiagTailX0RatChunk001Sub000Block062Tail surrogateDiagTailX0RatChunk001Sub000Block062
  ring

def SurrogateDiagonalTailChunk001Sub000Block062HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block062HeadSum X0 = surrogateDiagTailX0RatChunk001Sub000Block062Head

def SurrogateDiagonalTailChunk001Sub000Block062MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block062MidSum X0 = surrogateDiagTailX0RatChunk001Sub000Block062Mid

def SurrogateDiagonalTailChunk001Sub000Block062TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block062TailSum X0 = surrogateDiagTailX0RatChunk001Sub000Block062Tail

theorem surrogateDiagonalTailChunk001Sub000Block062_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk001Sub000Block062HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk001Sub000Block062MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk001Sub000Block062TailCertificateAt X0) :
    surrogateDiagonalTailChunk001Sub000Block062Sum X0 = surrogateDiagTailX0RatChunk001Sub000Block062 := by
  unfold SurrogateDiagonalTailChunk001Sub000Block062HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk001Sub000Block062MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk001Sub000Block062TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk001Sub000Block062Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk001Sub000Block062_eq_head_add_mid_add_tail

/-- Block 063 covers tail-support indices [11575,11600) and q from 19086 to 19127. -/

def TailChunk001Sub000Block063Part000SupportExplicit : Finset ℕ :=
  ([19086] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block063Part000 : ℚ :=
  (158162527 : ℚ) / 1022810858867520

def SurrogateDiagonalTailChunk001Sub000Block063Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19086
    = surrogateDiagTailX0RatChunk001Sub000Block063Part000

theorem surrogateDiagonalTailChunk001Sub000Block063Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block063Part000CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block063Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block063Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block063Part000CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block063Part000SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block063Part000] using hcert

def TailChunk001Sub000Block063Part001SupportExplicit : Finset ℕ :=
  ([19087] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block063Part001 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block063Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19087
    = surrogateDiagTailX0RatChunk001Sub000Block063Part001

theorem surrogateDiagonalTailChunk001Sub000Block063Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block063Part001CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block063Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block063Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block063Part001CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block063Part001SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block063Part001] using hcert

def TailChunk001Sub000Block063Part002SupportExplicit : Finset ℕ :=
  ([19090] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block063Part002 : ℚ :=
  (737150268625 : ℚ) / 6779738717283975168

def SurrogateDiagonalTailChunk001Sub000Block063Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19090
    = surrogateDiagTailX0RatChunk001Sub000Block063Part002

theorem surrogateDiagonalTailChunk001Sub000Block063Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block063Part002CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block063Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block063Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block063Part002CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block063Part002SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block063Part002] using hcert

def TailChunk001Sub000Block063Part003SupportExplicit : Finset ℕ :=
  ([19091] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block063Part003 : ℚ :=
  (29048272025 : ℚ) / 23609431628201852928

def SurrogateDiagonalTailChunk001Sub000Block063Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19091
    = surrogateDiagTailX0RatChunk001Sub000Block063Part003

theorem surrogateDiagonalTailChunk001Sub000Block063Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block063Part003CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block063Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block063Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block063Part003CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block063Part003SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block063Part003] using hcert

def TailChunk001Sub000Block063Part004SupportExplicit : Finset ℕ :=
  ([19093] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block063Part004 : ℚ :=
  (4632401263 : ℚ) / 12283163360899891200

def SurrogateDiagonalTailChunk001Sub000Block063Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19093
    = surrogateDiagTailX0RatChunk001Sub000Block063Part004

theorem surrogateDiagonalTailChunk001Sub000Block063Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block063Part004CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block063Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block063Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block063Part004CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block063Part004SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block063Part004] using hcert

def TailChunk001Sub000Block063Part005SupportExplicit : Finset ℕ :=
  ([19094] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block063Part005 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block063Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19094
    = surrogateDiagTailX0RatChunk001Sub000Block063Part005

theorem surrogateDiagonalTailChunk001Sub000Block063Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block063Part005CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block063Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block063Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block063Part005CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block063Part005SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block063Part005] using hcert

def TailChunk001Sub000Block063Part006SupportExplicit : Finset ℕ :=
  ([19095] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block063Part006 : ℚ :=
  (2405066757925 : ℚ) / 20401052310663856128

def SurrogateDiagonalTailChunk001Sub000Block063Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19095
    = surrogateDiagTailX0RatChunk001Sub000Block063Part006

theorem surrogateDiagonalTailChunk001Sub000Block063Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block063Part006CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block063Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block063Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block063Part006CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block063Part006SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block063Part006] using hcert

def TailChunk001Sub000Block063Part007SupportExplicit : Finset ℕ :=
  ([19099] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block063Part007 : ℚ :=
  (1067343271 : ℚ) / 3097121157715468800

def SurrogateDiagonalTailChunk001Sub000Block063Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19099
    = surrogateDiagTailX0RatChunk001Sub000Block063Part007

theorem surrogateDiagonalTailChunk001Sub000Block063Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block063Part007CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block063Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block063Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block063Part007CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block063Part007SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block063Part007] using hcert

def TailChunk001Sub000Block063Part008SupportExplicit : Finset ℕ :=
  ([19101] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block063Part008 : ℚ :=
  (1266748639175 : ℚ) / 32853631606717575744

def SurrogateDiagonalTailChunk001Sub000Block063Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19101
    = surrogateDiagTailX0RatChunk001Sub000Block063Part008

theorem surrogateDiagonalTailChunk001Sub000Block063Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block063Part008CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block063Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block063Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block063Part008CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block063Part008SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block063Part008] using hcert

def TailChunk001Sub000Block063Part009SupportExplicit : Finset ℕ :=
  ([19102] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block063Part009 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block063Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19102
    = surrogateDiagTailX0RatChunk001Sub000Block063Part009

theorem surrogateDiagonalTailChunk001Sub000Block063Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block063Part009CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block063Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block063Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block063Part009CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block063Part009SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block063Part009] using hcert

def TailChunk001Sub000Block063Part010SupportExplicit : Finset ℕ :=
  ([19103] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block063Part010 : ℚ :=
  (465968387075 : ℚ) / 89738608019912146944

def SurrogateDiagonalTailChunk001Sub000Block063Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19103
    = surrogateDiagTailX0RatChunk001Sub000Block063Part010

theorem surrogateDiagonalTailChunk001Sub000Block063Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block063Part010CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block063Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block063Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block063Part010CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block063Part010SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block063Part010] using hcert

def TailChunk001Sub000Block063Part011SupportExplicit : Finset ℕ :=
  ([19105] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block063Part011 : ℚ :=
  (72997406749 : ℚ) / 5452306569921331200

def SurrogateDiagonalTailChunk001Sub000Block063Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19105
    = surrogateDiagTailX0RatChunk001Sub000Block063Part011

theorem surrogateDiagonalTailChunk001Sub000Block063Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block063Part011CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block063Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block063Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block063Part011CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block063Part011SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block063Part011] using hcert

def TailChunk001Sub000Block063Part012SupportExplicit : Finset ℕ :=
  ([19106] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block063Part012 : ℚ :=
  (143667147 : ℚ) / 30907758726348800

def SurrogateDiagonalTailChunk001Sub000Block063Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19106
    = surrogateDiagTailX0RatChunk001Sub000Block063Part012

theorem surrogateDiagonalTailChunk001Sub000Block063Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block063Part012CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block063Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block063Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block063Part012CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block063Part012SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block063Part012] using hcert

def TailChunk001Sub000Block063Part013SupportExplicit : Finset ℕ :=
  ([19109] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block063Part013 : ℚ :=
  (14999049025 : ℚ) / 52237793719618633728

def SurrogateDiagonalTailChunk001Sub000Block063Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19109
    = surrogateDiagTailX0RatChunk001Sub000Block063Part013

theorem surrogateDiagonalTailChunk001Sub000Block063Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block063Part013CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block063Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block063Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block063Part013CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block063Part013SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block063Part013] using hcert

def TailChunk001Sub000Block063Part014SupportExplicit : Finset ℕ :=
  ([19111] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block063Part014 : ℚ :=
  (37485106875 : ℚ) / 48018800616896334848

def SurrogateDiagonalTailChunk001Sub000Block063Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19111
    = surrogateDiagTailX0RatChunk001Sub000Block063Part014

theorem surrogateDiagonalTailChunk001Sub000Block063Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block063Part014CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block063Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block063Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block063Part014CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block063Part014SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block063Part014] using hcert

def TailChunk001Sub000Block063Part015SupportExplicit : Finset ℕ :=
  ([19113] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block063Part015 : ℚ :=
  (276068453975 : ℚ) / 6042704871873871872

def SurrogateDiagonalTailChunk001Sub000Block063Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19113
    = surrogateDiagTailX0RatChunk001Sub000Block063Part015

theorem surrogateDiagonalTailChunk001Sub000Block063Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block063Part015CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block063Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block063Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block063Part015CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block063Part015SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block063Part015] using hcert

def TailChunk001Sub000Block063Part016SupportExplicit : Finset ℕ :=
  ([19114] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block063Part016 : ℚ :=
  (36786829525 : ℚ) / 4167463036751921952

def SurrogateDiagonalTailChunk001Sub000Block063Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19114
    = surrogateDiagTailX0RatChunk001Sub000Block063Part016

theorem surrogateDiagonalTailChunk001Sub000Block063Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block063Part016CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block063Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block063Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block063Part016CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block063Part016SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block063Part016] using hcert

def TailChunk001Sub000Block063Part017SupportExplicit : Finset ℕ :=
  ([19115] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block063Part017 : ℚ :=
  (608948428675 : ℚ) / 45531116529114617856

def SurrogateDiagonalTailChunk001Sub000Block063Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19115
    = surrogateDiagTailX0RatChunk001Sub000Block063Part017

theorem surrogateDiagonalTailChunk001Sub000Block063Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block063Part017CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block063Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block063Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block063Part017CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block063Part017SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block063Part017] using hcert

def TailChunk001Sub000Block063Part018SupportExplicit : Finset ℕ :=
  ([19117] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block063Part018 : ℚ :=
  (1439018881 : ℚ) / 553858834689014400

def SurrogateDiagonalTailChunk001Sub000Block063Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19117
    = surrogateDiagTailX0RatChunk001Sub000Block063Part018

theorem surrogateDiagonalTailChunk001Sub000Block063Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block063Part018CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block063Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block063Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block063Part018CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block063Part018SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block063Part018] using hcert

def TailChunk001Sub000Block063Part019SupportExplicit : Finset ℕ :=
  ([19119] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block063Part019 : ℚ :=
  (317284253525 : ℚ) / 8244416486003763456

def SurrogateDiagonalTailChunk001Sub000Block063Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19119
    = surrogateDiagTailX0RatChunk001Sub000Block063Part019

theorem surrogateDiagonalTailChunk001Sub000Block063Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block063Part019CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block063Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block063Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block063Part019CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block063Part019SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block063Part019] using hcert

def TailChunk001Sub000Block063Part020SupportExplicit : Finset ℕ :=
  ([19121] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block063Part020 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block063Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19121
    = surrogateDiagTailX0RatChunk001Sub000Block063Part020

theorem surrogateDiagonalTailChunk001Sub000Block063Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block063Part020CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block063Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block063Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block063Part020CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block063Part020SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block063Part020] using hcert

def TailChunk001Sub000Block063Part021SupportExplicit : Finset ℕ :=
  ([19122] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block063Part021 : ℚ :=
  (634597770725 : ℚ) / 2061104121500940864

def SurrogateDiagonalTailChunk001Sub000Block063Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19122
    = surrogateDiagTailX0RatChunk001Sub000Block063Part021

theorem surrogateDiagonalTailChunk001Sub000Block063Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block063Part021CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block063Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block063Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block063Part021CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block063Part021SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block063Part021] using hcert

def TailChunk001Sub000Block063Part022SupportExplicit : Finset ℕ :=
  ([19123] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block063Part022 : ℚ :=
  (10873073777 : ℚ) / 4842294263407641600

def SurrogateDiagonalTailChunk001Sub000Block063Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19123
    = surrogateDiagTailX0RatChunk001Sub000Block063Part022

theorem surrogateDiagonalTailChunk001Sub000Block063Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block063Part022CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block063Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block063Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block063Part022CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block063Part022SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block063Part022] using hcert

def TailChunk001Sub000Block063Part023SupportExplicit : Finset ℕ :=
  ([19126] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block063Part023 : ℚ :=
  (829103521 : ℚ) / 255899236685414400

def SurrogateDiagonalTailChunk001Sub000Block063Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19126
    = surrogateDiagTailX0RatChunk001Sub000Block063Part023

theorem surrogateDiagonalTailChunk001Sub000Block063Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block063Part023CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block063Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block063Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block063Part023CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block063Part023SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block063Part023] using hcert

def TailChunk001Sub000Block063Part024SupportExplicit : Finset ℕ :=
  ([19127] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block063Part024 : ℚ :=
  (20710703 : ℚ) / 30378301869484800

def SurrogateDiagonalTailChunk001Sub000Block063Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19127
    = surrogateDiagTailX0RatChunk001Sub000Block063Part024

theorem surrogateDiagonalTailChunk001Sub000Block063Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block063Part024CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block063Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block063Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block063Part024CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block063Part024SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block063Part024] using hcert

def surrogateDiagonalTailChunk001Sub000Block063HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block063Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block063Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block063Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block063Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block063Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block063Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block063Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block063Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block063Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block063Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block063Head : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block063Part000
    + surrogateDiagTailX0RatChunk001Sub000Block063Part001
    + surrogateDiagTailX0RatChunk001Sub000Block063Part002
    + surrogateDiagTailX0RatChunk001Sub000Block063Part003
    + surrogateDiagTailX0RatChunk001Sub000Block063Part004
    + surrogateDiagTailX0RatChunk001Sub000Block063Part005
    + surrogateDiagTailX0RatChunk001Sub000Block063Part006
    + surrogateDiagTailX0RatChunk001Sub000Block063Part007
    + surrogateDiagTailX0RatChunk001Sub000Block063Part008
    + surrogateDiagTailX0RatChunk001Sub000Block063Part009

def surrogateDiagonalTailChunk001Sub000Block063MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block063Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block063Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block063Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block063Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block063Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block063Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block063Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block063Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block063Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block063Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block063Mid : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block063Part010
    + surrogateDiagTailX0RatChunk001Sub000Block063Part011
    + surrogateDiagTailX0RatChunk001Sub000Block063Part012
    + surrogateDiagTailX0RatChunk001Sub000Block063Part013
    + surrogateDiagTailX0RatChunk001Sub000Block063Part014
    + surrogateDiagTailX0RatChunk001Sub000Block063Part015
    + surrogateDiagTailX0RatChunk001Sub000Block063Part016
    + surrogateDiagTailX0RatChunk001Sub000Block063Part017
    + surrogateDiagTailX0RatChunk001Sub000Block063Part018
    + surrogateDiagTailX0RatChunk001Sub000Block063Part019

def surrogateDiagonalTailChunk001Sub000Block063TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block063Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block063Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block063Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block063Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block063Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block063Tail : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block063Part020
    + surrogateDiagTailX0RatChunk001Sub000Block063Part021
    + surrogateDiagTailX0RatChunk001Sub000Block063Part022
    + surrogateDiagTailX0RatChunk001Sub000Block063Part023
    + surrogateDiagTailX0RatChunk001Sub000Block063Part024

def surrogateDiagonalTailChunk001Sub000Block063Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk001Sub000Block063HeadSum X0
    + surrogateDiagonalTailChunk001Sub000Block063MidSum X0
    + surrogateDiagonalTailChunk001Sub000Block063TailSum X0

def surrogateDiagTailX0RatChunk001Sub000Block063 : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block063Part000
    + surrogateDiagTailX0RatChunk001Sub000Block063Part001
    + surrogateDiagTailX0RatChunk001Sub000Block063Part002
    + surrogateDiagTailX0RatChunk001Sub000Block063Part003
    + surrogateDiagTailX0RatChunk001Sub000Block063Part004
    + surrogateDiagTailX0RatChunk001Sub000Block063Part005
    + surrogateDiagTailX0RatChunk001Sub000Block063Part006
    + surrogateDiagTailX0RatChunk001Sub000Block063Part007
    + surrogateDiagTailX0RatChunk001Sub000Block063Part008
    + surrogateDiagTailX0RatChunk001Sub000Block063Part009
    + surrogateDiagTailX0RatChunk001Sub000Block063Part010
    + surrogateDiagTailX0RatChunk001Sub000Block063Part011
    + surrogateDiagTailX0RatChunk001Sub000Block063Part012
    + surrogateDiagTailX0RatChunk001Sub000Block063Part013
    + surrogateDiagTailX0RatChunk001Sub000Block063Part014
    + surrogateDiagTailX0RatChunk001Sub000Block063Part015
    + surrogateDiagTailX0RatChunk001Sub000Block063Part016
    + surrogateDiagTailX0RatChunk001Sub000Block063Part017
    + surrogateDiagTailX0RatChunk001Sub000Block063Part018
    + surrogateDiagTailX0RatChunk001Sub000Block063Part019
    + surrogateDiagTailX0RatChunk001Sub000Block063Part020
    + surrogateDiagTailX0RatChunk001Sub000Block063Part021
    + surrogateDiagTailX0RatChunk001Sub000Block063Part022
    + surrogateDiagTailX0RatChunk001Sub000Block063Part023
    + surrogateDiagTailX0RatChunk001Sub000Block063Part024

theorem surrogateDiagTailX0RatChunk001Sub000Block063_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk001Sub000Block063Head + surrogateDiagTailX0RatChunk001Sub000Block063Mid + surrogateDiagTailX0RatChunk001Sub000Block063Tail =
      surrogateDiagTailX0RatChunk001Sub000Block063 := by
  unfold surrogateDiagTailX0RatChunk001Sub000Block063Head surrogateDiagTailX0RatChunk001Sub000Block063Mid surrogateDiagTailX0RatChunk001Sub000Block063Tail surrogateDiagTailX0RatChunk001Sub000Block063
  ring

def SurrogateDiagonalTailChunk001Sub000Block063HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block063HeadSum X0 = surrogateDiagTailX0RatChunk001Sub000Block063Head

def SurrogateDiagonalTailChunk001Sub000Block063MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block063MidSum X0 = surrogateDiagTailX0RatChunk001Sub000Block063Mid

def SurrogateDiagonalTailChunk001Sub000Block063TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block063TailSum X0 = surrogateDiagTailX0RatChunk001Sub000Block063Tail

theorem surrogateDiagonalTailChunk001Sub000Block063_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk001Sub000Block063HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk001Sub000Block063MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk001Sub000Block063TailCertificateAt X0) :
    surrogateDiagonalTailChunk001Sub000Block063Sum X0 = surrogateDiagTailX0RatChunk001Sub000Block063 := by
  unfold SurrogateDiagonalTailChunk001Sub000Block063HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk001Sub000Block063MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk001Sub000Block063TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk001Sub000Block063Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk001Sub000Block063_eq_head_add_mid_add_tail

/-- Block 064 covers tail-support indices [11600,11625) and q from 19129 to 19171. -/

def TailChunk001Sub000Block064Part000SupportExplicit : Finset ℕ :=
  ([19129] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block064Part000 : ℚ :=
  (279782927 : ℚ) / 69647322391142400

def SurrogateDiagonalTailChunk001Sub000Block064Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19129
    = surrogateDiagTailX0RatChunk001Sub000Block064Part000

theorem surrogateDiagonalTailChunk001Sub000Block064Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block064Part000CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block064Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block064Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block064Part000CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block064Part000SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block064Part000] using hcert

def TailChunk001Sub000Block064Part001SupportExplicit : Finset ℕ :=
  ([19130] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block064Part001 : ℚ :=
  (458127157525 : ℚ) / 8554967735279812608

def SurrogateDiagonalTailChunk001Sub000Block064Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19130
    = surrogateDiagTailX0RatChunk001Sub000Block064Part001

theorem surrogateDiagonalTailChunk001Sub000Block064Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block064Part001CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block064Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block064Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block064Part001CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block064Part001SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block064Part001] using hcert

def TailChunk001Sub000Block064Part002SupportExplicit : Finset ℕ :=
  ([19131] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block064Part002 : ℚ :=
  (97450744753 : ℚ) / 1422254785374259200

def SurrogateDiagonalTailChunk001Sub000Block064Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19131
    = surrogateDiagTailX0RatChunk001Sub000Block064Part002

theorem surrogateDiagonalTailChunk001Sub000Block064Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block064Part002CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block064Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block064Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block064Part002CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block064Part002SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block064Part002] using hcert

def TailChunk001Sub000Block064Part003SupportExplicit : Finset ℕ :=
  ([19135] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block064Part003 : ℚ :=
  (11509293025 : ℚ) / 1357412994080833536

def SurrogateDiagonalTailChunk001Sub000Block064Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19135
    = surrogateDiagTailX0RatChunk001Sub000Block064Part003

theorem surrogateDiagonalTailChunk001Sub000Block064Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block064Part003CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block064Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block064Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block064Part003CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block064Part003SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block064Part003] using hcert

def TailChunk001Sub000Block064Part004SupportExplicit : Finset ℕ :=
  ([19137] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block064Part004 : ℚ :=
  (1271527639025 : ℚ) / 33102051156123061824

def SurrogateDiagonalTailChunk001Sub000Block064Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19137
    = surrogateDiagTailX0RatChunk001Sub000Block064Part004

theorem surrogateDiagonalTailChunk001Sub000Block064Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block064Part004CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block064Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block064Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block064Part004CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block064Part004SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block064Part004] using hcert

def TailChunk001Sub000Block064Part005SupportExplicit : Finset ℕ :=
  ([19138] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block064Part005 : ℚ :=
  (468083532325 : ℚ) / 11283261613435110528

def SurrogateDiagonalTailChunk001Sub000Block064Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19138
    = surrogateDiagTailX0RatChunk001Sub000Block064Part005

theorem surrogateDiagonalTailChunk001Sub000Block064Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block064Part005CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block064Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block064Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block064Part005CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block064Part005SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block064Part005] using hcert

def TailChunk001Sub000Block064Part006SupportExplicit : Finset ℕ :=
  ([19139] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block064Part006 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block064Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19139
    = surrogateDiagTailX0RatChunk001Sub000Block064Part006

theorem surrogateDiagonalTailChunk001Sub000Block064Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block064Part006CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block064Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block064Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block064Part006CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block064Part006SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block064Part006] using hcert

def TailChunk001Sub000Block064Part007SupportExplicit : Finset ℕ :=
  ([19141] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block064Part007 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block064Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19141
    = surrogateDiagTailX0RatChunk001Sub000Block064Part007

theorem surrogateDiagonalTailChunk001Sub000Block064Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block064Part007CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block064Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block064Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block064Part007CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block064Part007SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block064Part007] using hcert

def TailChunk001Sub000Block064Part008SupportExplicit : Finset ℕ :=
  ([19142] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block064Part008 : ℚ :=
  (162699033925 : ℚ) / 16347526565473026048

def SurrogateDiagonalTailChunk001Sub000Block064Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19142
    = surrogateDiagTailX0RatChunk001Sub000Block064Part008

theorem surrogateDiagonalTailChunk001Sub000Block064Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block064Part008CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block064Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block064Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block064Part008CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block064Part008SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block064Part008] using hcert

def TailChunk001Sub000Block064Part009SupportExplicit : Finset ℕ :=
  ([19145] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block064Part009 : ℚ :=
  (1386324499375 : ℚ) / 73729688073801596928

def SurrogateDiagonalTailChunk001Sub000Block064Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19145
    = surrogateDiagTailX0RatChunk001Sub000Block064Part009

theorem surrogateDiagonalTailChunk001Sub000Block064Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block064Part009CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block064Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block064Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block064Part009CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block064Part009SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block064Part009] using hcert

def TailChunk001Sub000Block064Part010SupportExplicit : Finset ℕ :=
  ([19146] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block064Part010 : ℚ :=
  (25447658069 : ℚ) / 82858977449793600

def SurrogateDiagonalTailChunk001Sub000Block064Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19146
    = surrogateDiagTailX0RatChunk001Sub000Block064Part010

theorem surrogateDiagonalTailChunk001Sub000Block064Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block064Part010CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block064Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block064Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block064Part010CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block064Part010SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block064Part010] using hcert

def TailChunk001Sub000Block064Part011SupportExplicit : Finset ℕ :=
  ([19147] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block064Part011 : ℚ :=
  (646005487 : ℚ) / 1207453687850680320

def SurrogateDiagonalTailChunk001Sub000Block064Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19147
    = surrogateDiagTailX0RatChunk001Sub000Block064Part011

theorem surrogateDiagonalTailChunk001Sub000Block064Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block064Part011CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block064Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block064Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block064Part011CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block064Part011SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block064Part011] using hcert

def TailChunk001Sub000Block064Part012SupportExplicit : Finset ℕ :=
  ([19149] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block064Part012 : ℚ :=
  (97542244183 : ℚ) / 1913005141099315200

def SurrogateDiagonalTailChunk001Sub000Block064Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19149
    = surrogateDiagTailX0RatChunk001Sub000Block064Part012

theorem surrogateDiagonalTailChunk001Sub000Block064Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block064Part012CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block064Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block064Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block064Part012CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block064Part012SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block064Part012] using hcert

def TailChunk001Sub000Block064Part013SupportExplicit : Finset ℕ :=
  ([19151] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block064Part013 : ℚ :=
  (22823013157 : ℚ) / 9168195032352000000

def SurrogateDiagonalTailChunk001Sub000Block064Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19151
    = surrogateDiagTailX0RatChunk001Sub000Block064Part013

theorem surrogateDiagonalTailChunk001Sub000Block064Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block064Part013CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block064Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block064Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block064Part013CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block064Part013SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block064Part013] using hcert

def TailChunk001Sub000Block064Part014SupportExplicit : Finset ℕ :=
  ([19153] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block064Part014 : ℚ :=
  (29486952375 : ℚ) / 105635301077338151296

def SurrogateDiagonalTailChunk001Sub000Block064Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19153
    = surrogateDiagTailX0RatChunk001Sub000Block064Part014

theorem surrogateDiagonalTailChunk001Sub000Block064Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block064Part014CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block064Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block064Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block064Part014CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block064Part014SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block064Part014] using hcert

def TailChunk001Sub000Block064Part015SupportExplicit : Finset ℕ :=
  ([19154] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block064Part015 : ℚ :=
  (298334623 : ℚ) / 85299745561804800

def SurrogateDiagonalTailChunk001Sub000Block064Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19154
    = surrogateDiagTailX0RatChunk001Sub000Block064Part015

theorem surrogateDiagonalTailChunk001Sub000Block064Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block064Part015CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block064Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block064Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block064Part015CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block064Part015SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block064Part015] using hcert

def TailChunk001Sub000Block064Part016SupportExplicit : Finset ℕ :=
  ([19155] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block064Part016 : ℚ :=
  (560341032025 : ℚ) / 6787807432687091712

def SurrogateDiagonalTailChunk001Sub000Block064Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19155
    = surrogateDiagTailX0RatChunk001Sub000Block064Part016

theorem surrogateDiagonalTailChunk001Sub000Block064Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block064Part016CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block064Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block064Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block064Part016CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block064Part016SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block064Part016] using hcert

def TailChunk001Sub000Block064Part017SupportExplicit : Finset ℕ :=
  ([19157] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block064Part017 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block064Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19157
    = surrogateDiagTailX0RatChunk001Sub000Block064Part017

theorem surrogateDiagonalTailChunk001Sub000Block064Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block064Part017CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block064Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block064Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block064Part017CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block064Part017SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block064Part017] using hcert

def TailChunk001Sub000Block064Part018SupportExplicit : Finset ℕ :=
  ([19158] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block064Part018 : ℚ :=
  (925899359 : ℚ) / 2598356751436800

def SurrogateDiagonalTailChunk001Sub000Block064Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19158
    = surrogateDiagTailX0RatChunk001Sub000Block064Part018

theorem surrogateDiagonalTailChunk001Sub000Block064Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block064Part018CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block064Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block064Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block064Part018CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block064Part018SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block064Part018] using hcert

def TailChunk001Sub000Block064Part019SupportExplicit : Finset ℕ :=
  ([19162] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block064Part019 : ℚ :=
  (2940187403 : ℚ) / 65589802953523200

def SurrogateDiagonalTailChunk001Sub000Block064Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19162
    = surrogateDiagTailX0RatChunk001Sub000Block064Part019

theorem surrogateDiagonalTailChunk001Sub000Block064Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block064Part019CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block064Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block064Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block064Part019CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block064Part019SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block064Part019] using hcert

def TailChunk001Sub000Block064Part020SupportExplicit : Finset ℕ :=
  ([19163] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block064Part020 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block064Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19163
    = surrogateDiagTailX0RatChunk001Sub000Block064Part020

theorem surrogateDiagonalTailChunk001Sub000Block064Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block064Part020CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block064Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block064Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block064Part020CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block064Part020SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block064Part020] using hcert

def TailChunk001Sub000Block064Part021SupportExplicit : Finset ℕ :=
  ([19165] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block064Part021 : ℚ :=
  (306338236125 : ℚ) / 46009506084068786176

def SurrogateDiagonalTailChunk001Sub000Block064Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19165
    = surrogateDiagTailX0RatChunk001Sub000Block064Part021

theorem surrogateDiagonalTailChunk001Sub000Block064Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block064Part021CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block064Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block064Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block064Part021CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block064Part021SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block064Part021] using hcert

def TailChunk001Sub000Block064Part022SupportExplicit : Finset ℕ :=
  ([19167] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block064Part022 : ℚ :=
  (318879253475 : ℚ) / 8327535340152903936

def SurrogateDiagonalTailChunk001Sub000Block064Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19167
    = surrogateDiagTailX0RatChunk001Sub000Block064Part022

theorem surrogateDiagonalTailChunk001Sub000Block064Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block064Part022CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block064Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block064Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block064Part022CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block064Part022SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block064Part022] using hcert

def TailChunk001Sub000Block064Part023SupportExplicit : Finset ℕ :=
  ([19169] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block064Part023 : ℚ :=
  (2654374979 : ℚ) / 3888422639294054400

def SurrogateDiagonalTailChunk001Sub000Block064Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19169
    = surrogateDiagTailX0RatChunk001Sub000Block064Part023

theorem surrogateDiagonalTailChunk001Sub000Block064Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block064Part023CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block064Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block064Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block064Part023CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block064Part023SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block064Part023] using hcert

def TailChunk001Sub000Block064Part024SupportExplicit : Finset ℕ :=
  ([19171] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block064Part024 : ℚ :=
  (10090267025 : ℚ) / 8468549480974270464

def SurrogateDiagonalTailChunk001Sub000Block064Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19171
    = surrogateDiagTailX0RatChunk001Sub000Block064Part024

theorem surrogateDiagonalTailChunk001Sub000Block064Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block064Part024CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block064Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block064Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block064Part024CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block064Part024SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block064Part024] using hcert

def surrogateDiagonalTailChunk001Sub000Block064HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block064Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block064Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block064Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block064Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block064Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block064Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block064Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block064Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block064Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block064Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block064Head : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block064Part000
    + surrogateDiagTailX0RatChunk001Sub000Block064Part001
    + surrogateDiagTailX0RatChunk001Sub000Block064Part002
    + surrogateDiagTailX0RatChunk001Sub000Block064Part003
    + surrogateDiagTailX0RatChunk001Sub000Block064Part004
    + surrogateDiagTailX0RatChunk001Sub000Block064Part005
    + surrogateDiagTailX0RatChunk001Sub000Block064Part006
    + surrogateDiagTailX0RatChunk001Sub000Block064Part007
    + surrogateDiagTailX0RatChunk001Sub000Block064Part008
    + surrogateDiagTailX0RatChunk001Sub000Block064Part009

def surrogateDiagonalTailChunk001Sub000Block064MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block064Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block064Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block064Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block064Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block064Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block064Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block064Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block064Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block064Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block064Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block064Mid : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block064Part010
    + surrogateDiagTailX0RatChunk001Sub000Block064Part011
    + surrogateDiagTailX0RatChunk001Sub000Block064Part012
    + surrogateDiagTailX0RatChunk001Sub000Block064Part013
    + surrogateDiagTailX0RatChunk001Sub000Block064Part014
    + surrogateDiagTailX0RatChunk001Sub000Block064Part015
    + surrogateDiagTailX0RatChunk001Sub000Block064Part016
    + surrogateDiagTailX0RatChunk001Sub000Block064Part017
    + surrogateDiagTailX0RatChunk001Sub000Block064Part018
    + surrogateDiagTailX0RatChunk001Sub000Block064Part019

def surrogateDiagonalTailChunk001Sub000Block064TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block064Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block064Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block064Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block064Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block064Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block064Tail : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block064Part020
    + surrogateDiagTailX0RatChunk001Sub000Block064Part021
    + surrogateDiagTailX0RatChunk001Sub000Block064Part022
    + surrogateDiagTailX0RatChunk001Sub000Block064Part023
    + surrogateDiagTailX0RatChunk001Sub000Block064Part024

def surrogateDiagonalTailChunk001Sub000Block064Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk001Sub000Block064HeadSum X0
    + surrogateDiagonalTailChunk001Sub000Block064MidSum X0
    + surrogateDiagonalTailChunk001Sub000Block064TailSum X0

def surrogateDiagTailX0RatChunk001Sub000Block064 : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block064Part000
    + surrogateDiagTailX0RatChunk001Sub000Block064Part001
    + surrogateDiagTailX0RatChunk001Sub000Block064Part002
    + surrogateDiagTailX0RatChunk001Sub000Block064Part003
    + surrogateDiagTailX0RatChunk001Sub000Block064Part004
    + surrogateDiagTailX0RatChunk001Sub000Block064Part005
    + surrogateDiagTailX0RatChunk001Sub000Block064Part006
    + surrogateDiagTailX0RatChunk001Sub000Block064Part007
    + surrogateDiagTailX0RatChunk001Sub000Block064Part008
    + surrogateDiagTailX0RatChunk001Sub000Block064Part009
    + surrogateDiagTailX0RatChunk001Sub000Block064Part010
    + surrogateDiagTailX0RatChunk001Sub000Block064Part011
    + surrogateDiagTailX0RatChunk001Sub000Block064Part012
    + surrogateDiagTailX0RatChunk001Sub000Block064Part013
    + surrogateDiagTailX0RatChunk001Sub000Block064Part014
    + surrogateDiagTailX0RatChunk001Sub000Block064Part015
    + surrogateDiagTailX0RatChunk001Sub000Block064Part016
    + surrogateDiagTailX0RatChunk001Sub000Block064Part017
    + surrogateDiagTailX0RatChunk001Sub000Block064Part018
    + surrogateDiagTailX0RatChunk001Sub000Block064Part019
    + surrogateDiagTailX0RatChunk001Sub000Block064Part020
    + surrogateDiagTailX0RatChunk001Sub000Block064Part021
    + surrogateDiagTailX0RatChunk001Sub000Block064Part022
    + surrogateDiagTailX0RatChunk001Sub000Block064Part023
    + surrogateDiagTailX0RatChunk001Sub000Block064Part024

theorem surrogateDiagTailX0RatChunk001Sub000Block064_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk001Sub000Block064Head + surrogateDiagTailX0RatChunk001Sub000Block064Mid + surrogateDiagTailX0RatChunk001Sub000Block064Tail =
      surrogateDiagTailX0RatChunk001Sub000Block064 := by
  unfold surrogateDiagTailX0RatChunk001Sub000Block064Head surrogateDiagTailX0RatChunk001Sub000Block064Mid surrogateDiagTailX0RatChunk001Sub000Block064Tail surrogateDiagTailX0RatChunk001Sub000Block064
  ring

def SurrogateDiagonalTailChunk001Sub000Block064HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block064HeadSum X0 = surrogateDiagTailX0RatChunk001Sub000Block064Head

def SurrogateDiagonalTailChunk001Sub000Block064MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block064MidSum X0 = surrogateDiagTailX0RatChunk001Sub000Block064Mid

def SurrogateDiagonalTailChunk001Sub000Block064TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block064TailSum X0 = surrogateDiagTailX0RatChunk001Sub000Block064Tail

theorem surrogateDiagonalTailChunk001Sub000Block064_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk001Sub000Block064HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk001Sub000Block064MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk001Sub000Block064TailCertificateAt X0) :
    surrogateDiagonalTailChunk001Sub000Block064Sum X0 = surrogateDiagTailX0RatChunk001Sub000Block064 := by
  unfold SurrogateDiagonalTailChunk001Sub000Block064HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk001Sub000Block064MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk001Sub000Block064TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk001Sub000Block064Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk001Sub000Block064_eq_head_add_mid_add_tail

/-- Block 065 covers tail-support indices [11625,11650) and q from 19173 to 19210. -/

def TailChunk001Sub000Block065Part000SupportExplicit : Finset ℕ :=
  ([19173] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block065Part000 : ℚ :=
  (92318755303 : ℚ) / 937707185472307200

def SurrogateDiagonalTailChunk001Sub000Block065Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19173
    = surrogateDiagTailX0RatChunk001Sub000Block065Part000

theorem surrogateDiagonalTailChunk001Sub000Block065Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block065Part000CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block065Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block065Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block065Part000CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block065Part000SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block065Part000] using hcert

def TailChunk001Sub000Block065Part001SupportExplicit : Finset ℕ :=
  ([19174] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block065Part001 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block065Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19174
    = surrogateDiagTailX0RatChunk001Sub000Block065Part001

theorem surrogateDiagonalTailChunk001Sub000Block065Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block065Part001CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block065Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block065Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block065Part001CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block065Part001SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block065Part001] using hcert

def TailChunk001Sub000Block065Part002SupportExplicit : Finset ℕ :=
  ([19177] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block065Part002 : ℚ :=
  (31527673 : ℚ) / 118170836941500000

def SurrogateDiagonalTailChunk001Sub000Block065Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19177
    = surrogateDiagTailX0RatChunk001Sub000Block065Part002

theorem surrogateDiagonalTailChunk001Sub000Block065Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block065Part002CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block065Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block065Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block065Part002CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block065Part002SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block065Part002] using hcert

def TailChunk001Sub000Block065Part003SupportExplicit : Finset ℕ :=
  ([19178] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block065Part003 : ℚ :=
  (80680267525 : ℚ) / 18898873508959452288

def SurrogateDiagonalTailChunk001Sub000Block065Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19178
    = surrogateDiagTailX0RatChunk001Sub000Block065Part003

theorem surrogateDiagonalTailChunk001Sub000Block065Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block065Part003CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block065Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block065Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block065Part003CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block065Part003SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block065Part003] using hcert

def TailChunk001Sub000Block065Part004SupportExplicit : Finset ℕ :=
  ([19181] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block065Part004 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block065Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19181
    = surrogateDiagTailX0RatChunk001Sub000Block065Part004

theorem surrogateDiagonalTailChunk001Sub000Block065Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block065Part004CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block065Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block065Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block065Part004CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block065Part004SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block065Part004] using hcert

def TailChunk001Sub000Block065Part005SupportExplicit : Finset ℕ :=
  ([19182] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block065Part005 : ℚ :=
  (74917699625 : ℚ) / 377669054492116992

def SurrogateDiagonalTailChunk001Sub000Block065Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19182
    = surrogateDiagTailX0RatChunk001Sub000Block065Part005

theorem surrogateDiagonalTailChunk001Sub000Block065Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block065Part005CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block065Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block065Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block065Part005CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block065Part005SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block065Part005] using hcert

def TailChunk001Sub000Block065Part006SupportExplicit : Finset ℕ :=
  ([19183] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block065Part006 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block065Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19183
    = surrogateDiagTailX0RatChunk001Sub000Block065Part006

theorem surrogateDiagonalTailChunk001Sub000Block065Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block065Part006CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block065Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block065Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block065Part006CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block065Part006SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block065Part006] using hcert

def TailChunk001Sub000Block065Part007SupportExplicit : Finset ℕ :=
  ([19185] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block065Part007 : ℚ :=
  (717184080775 : ℚ) / 27321857515324735488

def SurrogateDiagonalTailChunk001Sub000Block065Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19185
    = surrogateDiagTailX0RatChunk001Sub000Block065Part007

theorem surrogateDiagonalTailChunk001Sub000Block065Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block065Part007CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block065Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block065Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block065Part007CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block065Part007SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block065Part007] using hcert

def TailChunk001Sub000Block065Part008SupportExplicit : Finset ℕ :=
  ([19186] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block065Part008 : ℚ :=
  (2909964277 : ℚ) / 767697710056243200

def SurrogateDiagonalTailChunk001Sub000Block065Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19186
    = surrogateDiagTailX0RatChunk001Sub000Block065Part008

theorem surrogateDiagonalTailChunk001Sub000Block065Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block065Part008CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block065Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block065Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block065Part008CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block065Part008SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block065Part008] using hcert

def TailChunk001Sub000Block065Part009SupportExplicit : Finset ℕ :=
  ([19187] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block065Part009 : ℚ :=
  (18802742687 : ℚ) / 3653121421036569600

def SurrogateDiagonalTailChunk001Sub000Block065Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19187
    = surrogateDiagTailX0RatChunk001Sub000Block065Part009

theorem surrogateDiagonalTailChunk001Sub000Block065Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block065Part009CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block065Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block065Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block065Part009CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block065Part009SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block065Part009] using hcert

def TailChunk001Sub000Block065Part010SupportExplicit : Finset ℕ :=
  ([19189] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block065Part010 : ℚ :=
  (100027511 : ℚ) / 147718803901409640

def SurrogateDiagonalTailChunk001Sub000Block065Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19189
    = surrogateDiagTailX0RatChunk001Sub000Block065Part010

theorem surrogateDiagonalTailChunk001Sub000Block065Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block065Part010CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block065Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block065Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block065Part010CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block065Part010SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block065Part010] using hcert

def TailChunk001Sub000Block065Part011SupportExplicit : Finset ℕ :=
  ([19190] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block065Part011 : ℚ :=
  (1505207033 : ℚ) / 13439615385600000

def SurrogateDiagonalTailChunk001Sub000Block065Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19190
    = surrogateDiagTailX0RatChunk001Sub000Block065Part011

theorem surrogateDiagonalTailChunk001Sub000Block065Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block065Part011CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block065Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block065Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block065Part011CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block065Part011SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block065Part011] using hcert

def TailChunk001Sub000Block065Part012SupportExplicit : Finset ℕ :=
  ([19191] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block065Part012 : ℚ :=
  (41675 : ℚ) / 4462749937391616

def SurrogateDiagonalTailChunk001Sub000Block065Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19191
    = surrogateDiagTailX0RatChunk001Sub000Block065Part012

theorem surrogateDiagonalTailChunk001Sub000Block065Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block065Part012CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block065Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block065Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block065Part012CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block065Part012SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block065Part012] using hcert

def TailChunk001Sub000Block065Part013SupportExplicit : Finset ℕ :=
  ([19193] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block065Part013 : ℚ :=
  (402300496525 : ℚ) / 265303627475303006208

def SurrogateDiagonalTailChunk001Sub000Block065Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19193
    = surrogateDiagTailX0RatChunk001Sub000Block065Part013

theorem surrogateDiagonalTailChunk001Sub000Block065Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block065Part013CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block065Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block065Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block065Part013CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block065Part013SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block065Part013] using hcert

def TailChunk001Sub000Block065Part014SupportExplicit : Finset ℕ :=
  ([19194] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block065Part014 : ℚ :=
  (378748836725 : ℚ) / 1120937034666737664

def SurrogateDiagonalTailChunk001Sub000Block065Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19194
    = surrogateDiagTailX0RatChunk001Sub000Block065Part014

theorem surrogateDiagonalTailChunk001Sub000Block065Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block065Part014CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block065Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block065Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block065Part014CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block065Part014SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block065Part014] using hcert

def TailChunk001Sub000Block065Part015SupportExplicit : Finset ℕ :=
  ([19195] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block065Part015 : ℚ :=
  (1666796183 : ℚ) / 129492851215564800

def SurrogateDiagonalTailChunk001Sub000Block065Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19195
    = surrogateDiagTailX0RatChunk001Sub000Block065Part015

theorem surrogateDiagonalTailChunk001Sub000Block065Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block065Part015CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block065Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block065Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block065Part015CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block065Part015SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block065Part015] using hcert

def TailChunk001Sub000Block065Part016SupportExplicit : Finset ℕ :=
  ([19198] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block065Part016 : ℚ :=
  (4421530429 : ℚ) / 729079244867635200

def SurrogateDiagonalTailChunk001Sub000Block065Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19198
    = surrogateDiagTailX0RatChunk001Sub000Block065Part016

theorem surrogateDiagonalTailChunk001Sub000Block065Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block065Part016CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block065Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block065Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block065Part016CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block065Part016SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block065Part016] using hcert

def TailChunk001Sub000Block065Part017SupportExplicit : Finset ℕ :=
  ([19199] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block065Part017 : ℚ :=
  (103567125775 : ℚ) / 316637253546366763008

def SurrogateDiagonalTailChunk001Sub000Block065Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19199
    = surrogateDiagTailX0RatChunk001Sub000Block065Part017

theorem surrogateDiagonalTailChunk001Sub000Block065Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block065Part017CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block065Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block065Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block065Part017CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block065Part017SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block065Part017] using hcert

def TailChunk001Sub000Block065Part018SupportExplicit : Finset ℕ :=
  ([19201] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block065Part018 : ℚ :=
  (9330211067 : ℚ) / 1045499935922749440

def SurrogateDiagonalTailChunk001Sub000Block065Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19201
    = surrogateDiagTailX0RatChunk001Sub000Block065Part018

theorem surrogateDiagonalTailChunk001Sub000Block065Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block065Part018CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block065Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block065Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block065Part018CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block065Part018SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block065Part018] using hcert

def TailChunk001Sub000Block065Part019SupportExplicit : Finset ℕ :=
  ([19202] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block065Part019 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block065Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19202
    = surrogateDiagTailX0RatChunk001Sub000Block065Part019

theorem surrogateDiagonalTailChunk001Sub000Block065Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block065Part019CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block065Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block065Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block065Part019CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block065Part019SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block065Part019] using hcert

def TailChunk001Sub000Block065Part020SupportExplicit : Finset ℕ :=
  ([19203] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block065Part020 : ℚ :=
  (32897875375 : ℚ) / 14703158566369492992

def SurrogateDiagonalTailChunk001Sub000Block065Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19203
    = surrogateDiagTailX0RatChunk001Sub000Block065Part020

theorem surrogateDiagonalTailChunk001Sub000Block065Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block065Part020CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block065Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block065Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block065Part020CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block065Part020SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block065Part020] using hcert

def TailChunk001Sub000Block065Part021SupportExplicit : Finset ℕ :=
  ([19205] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block065Part021 : ℚ :=
  (532243921175 : ℚ) / 56932454008139956224

def SurrogateDiagonalTailChunk001Sub000Block065Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19205
    = surrogateDiagTailX0RatChunk001Sub000Block065Part021

theorem surrogateDiagonalTailChunk001Sub000Block065Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block065Part021CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block065Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block065Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block065Part021CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block065Part021SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block065Part021] using hcert

def TailChunk001Sub000Block065Part022SupportExplicit : Finset ℕ :=
  ([19207] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block065Part022 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block065Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19207
    = surrogateDiagTailX0RatChunk001Sub000Block065Part022

theorem surrogateDiagonalTailChunk001Sub000Block065Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block065Part022CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block065Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block065Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block065Part022CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block065Part022SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block065Part022] using hcert

def TailChunk001Sub000Block065Part023SupportExplicit : Finset ℕ :=
  ([19209] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block065Part023 : ℚ :=
  (248869025 : ℚ) / 59742853481299968

def SurrogateDiagonalTailChunk001Sub000Block065Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19209
    = surrogateDiagTailX0RatChunk001Sub000Block065Part023

theorem surrogateDiagonalTailChunk001Sub000Block065Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block065Part023CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block065Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block065Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block065Part023CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block065Part023SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block065Part023] using hcert

def TailChunk001Sub000Block065Part024SupportExplicit : Finset ℕ :=
  ([19210] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block065Part024 : ℚ :=
  (186961538775 : ℚ) / 2200379503144861696

def SurrogateDiagonalTailChunk001Sub000Block065Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19210
    = surrogateDiagTailX0RatChunk001Sub000Block065Part024

theorem surrogateDiagonalTailChunk001Sub000Block065Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block065Part024CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block065Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block065Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block065Part024CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block065Part024SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block065Part024] using hcert

def surrogateDiagonalTailChunk001Sub000Block065HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block065Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block065Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block065Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block065Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block065Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block065Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block065Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block065Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block065Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block065Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block065Head : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block065Part000
    + surrogateDiagTailX0RatChunk001Sub000Block065Part001
    + surrogateDiagTailX0RatChunk001Sub000Block065Part002
    + surrogateDiagTailX0RatChunk001Sub000Block065Part003
    + surrogateDiagTailX0RatChunk001Sub000Block065Part004
    + surrogateDiagTailX0RatChunk001Sub000Block065Part005
    + surrogateDiagTailX0RatChunk001Sub000Block065Part006
    + surrogateDiagTailX0RatChunk001Sub000Block065Part007
    + surrogateDiagTailX0RatChunk001Sub000Block065Part008
    + surrogateDiagTailX0RatChunk001Sub000Block065Part009

def surrogateDiagonalTailChunk001Sub000Block065MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block065Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block065Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block065Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block065Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block065Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block065Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block065Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block065Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block065Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block065Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block065Mid : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block065Part010
    + surrogateDiagTailX0RatChunk001Sub000Block065Part011
    + surrogateDiagTailX0RatChunk001Sub000Block065Part012
    + surrogateDiagTailX0RatChunk001Sub000Block065Part013
    + surrogateDiagTailX0RatChunk001Sub000Block065Part014
    + surrogateDiagTailX0RatChunk001Sub000Block065Part015
    + surrogateDiagTailX0RatChunk001Sub000Block065Part016
    + surrogateDiagTailX0RatChunk001Sub000Block065Part017
    + surrogateDiagTailX0RatChunk001Sub000Block065Part018
    + surrogateDiagTailX0RatChunk001Sub000Block065Part019

def surrogateDiagonalTailChunk001Sub000Block065TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block065Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block065Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block065Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block065Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block065Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block065Tail : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block065Part020
    + surrogateDiagTailX0RatChunk001Sub000Block065Part021
    + surrogateDiagTailX0RatChunk001Sub000Block065Part022
    + surrogateDiagTailX0RatChunk001Sub000Block065Part023
    + surrogateDiagTailX0RatChunk001Sub000Block065Part024

def surrogateDiagonalTailChunk001Sub000Block065Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk001Sub000Block065HeadSum X0
    + surrogateDiagonalTailChunk001Sub000Block065MidSum X0
    + surrogateDiagonalTailChunk001Sub000Block065TailSum X0

def surrogateDiagTailX0RatChunk001Sub000Block065 : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block065Part000
    + surrogateDiagTailX0RatChunk001Sub000Block065Part001
    + surrogateDiagTailX0RatChunk001Sub000Block065Part002
    + surrogateDiagTailX0RatChunk001Sub000Block065Part003
    + surrogateDiagTailX0RatChunk001Sub000Block065Part004
    + surrogateDiagTailX0RatChunk001Sub000Block065Part005
    + surrogateDiagTailX0RatChunk001Sub000Block065Part006
    + surrogateDiagTailX0RatChunk001Sub000Block065Part007
    + surrogateDiagTailX0RatChunk001Sub000Block065Part008
    + surrogateDiagTailX0RatChunk001Sub000Block065Part009
    + surrogateDiagTailX0RatChunk001Sub000Block065Part010
    + surrogateDiagTailX0RatChunk001Sub000Block065Part011
    + surrogateDiagTailX0RatChunk001Sub000Block065Part012
    + surrogateDiagTailX0RatChunk001Sub000Block065Part013
    + surrogateDiagTailX0RatChunk001Sub000Block065Part014
    + surrogateDiagTailX0RatChunk001Sub000Block065Part015
    + surrogateDiagTailX0RatChunk001Sub000Block065Part016
    + surrogateDiagTailX0RatChunk001Sub000Block065Part017
    + surrogateDiagTailX0RatChunk001Sub000Block065Part018
    + surrogateDiagTailX0RatChunk001Sub000Block065Part019
    + surrogateDiagTailX0RatChunk001Sub000Block065Part020
    + surrogateDiagTailX0RatChunk001Sub000Block065Part021
    + surrogateDiagTailX0RatChunk001Sub000Block065Part022
    + surrogateDiagTailX0RatChunk001Sub000Block065Part023
    + surrogateDiagTailX0RatChunk001Sub000Block065Part024

theorem surrogateDiagTailX0RatChunk001Sub000Block065_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk001Sub000Block065Head + surrogateDiagTailX0RatChunk001Sub000Block065Mid + surrogateDiagTailX0RatChunk001Sub000Block065Tail =
      surrogateDiagTailX0RatChunk001Sub000Block065 := by
  unfold surrogateDiagTailX0RatChunk001Sub000Block065Head surrogateDiagTailX0RatChunk001Sub000Block065Mid surrogateDiagTailX0RatChunk001Sub000Block065Tail surrogateDiagTailX0RatChunk001Sub000Block065
  ring

def SurrogateDiagonalTailChunk001Sub000Block065HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block065HeadSum X0 = surrogateDiagTailX0RatChunk001Sub000Block065Head

def SurrogateDiagonalTailChunk001Sub000Block065MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block065MidSum X0 = surrogateDiagTailX0RatChunk001Sub000Block065Mid

def SurrogateDiagonalTailChunk001Sub000Block065TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block065TailSum X0 = surrogateDiagTailX0RatChunk001Sub000Block065Tail

theorem surrogateDiagonalTailChunk001Sub000Block065_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk001Sub000Block065HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk001Sub000Block065MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk001Sub000Block065TailCertificateAt X0) :
    surrogateDiagonalTailChunk001Sub000Block065Sum X0 = surrogateDiagTailX0RatChunk001Sub000Block065 := by
  unfold SurrogateDiagonalTailChunk001Sub000Block065HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk001Sub000Block065MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk001Sub000Block065TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk001Sub000Block065Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk001Sub000Block065_eq_head_add_mid_add_tail

/-- Block 066 covers tail-support indices [11650,11675) and q from 19211 to 19253. -/

def TailChunk001Sub000Block066Part000SupportExplicit : Finset ℕ :=
  ([19211] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block066Part000 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block066Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19211
    = surrogateDiagTailX0RatChunk001Sub000Block066Part000

theorem surrogateDiagonalTailChunk001Sub000Block066Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block066Part000CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block066Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block066Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block066Part000CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block066Part000SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block066Part000] using hcert

def TailChunk001Sub000Block066Part001SupportExplicit : Finset ℕ :=
  ([19213] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block066Part001 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block066Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19213
    = surrogateDiagTailX0RatChunk001Sub000Block066Part001

theorem surrogateDiagonalTailChunk001Sub000Block066Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block066Part001CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block066Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block066Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block066Part001CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block066Part001SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block066Part001] using hcert

def TailChunk001Sub000Block066Part002SupportExplicit : Finset ℕ :=
  ([19214] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block066Part002 : ℚ :=
  (120874101425 : ℚ) / 7690371054854759424

def SurrogateDiagonalTailChunk001Sub000Block066Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19214
    = surrogateDiagTailX0RatChunk001Sub000Block066Part002

theorem surrogateDiagonalTailChunk001Sub000Block066Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block066Part002CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block066Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block066Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block066Part002CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block066Part002SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block066Part002] using hcert

def TailChunk001Sub000Block066Part003SupportExplicit : Finset ℕ :=
  ([19217] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block066Part003 : ℚ :=
  (22979820283 : ℚ) / 9295308492216451200

def SurrogateDiagonalTailChunk001Sub000Block066Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19217
    = surrogateDiagTailX0RatChunk001Sub000Block066Part003

theorem surrogateDiagonalTailChunk001Sub000Block066Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block066Part003CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block066Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block066Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block066Part003CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block066Part003SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block066Part003] using hcert

def TailChunk001Sub000Block066Part004SupportExplicit : Finset ℕ :=
  ([19218] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block066Part004 : ℚ :=
  (320712678725 : ℚ) / 2102820277207769664

def SurrogateDiagonalTailChunk001Sub000Block066Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19218
    = surrogateDiagTailX0RatChunk001Sub000Block066Part004

theorem surrogateDiagonalTailChunk001Sub000Block066Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block066Part004CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block066Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block066Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block066Part004CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block066Part004SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block066Part004] using hcert

def TailChunk001Sub000Block066Part005SupportExplicit : Finset ℕ :=
  ([19219] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block066Part005 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block066Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19219
    = surrogateDiagTailX0RatChunk001Sub000Block066Part005

theorem surrogateDiagonalTailChunk001Sub000Block066Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block066Part005CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block066Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block066Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block066Part005CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block066Part005SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block066Part005] using hcert

def TailChunk001Sub000Block066Part006SupportExplicit : Finset ℕ :=
  ([19221] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block066Part006 : ℚ :=
  (59075580275 : ℚ) / 29864886532676665344

def SurrogateDiagonalTailChunk001Sub000Block066Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19221
    = surrogateDiagTailX0RatChunk001Sub000Block066Part006

theorem surrogateDiagonalTailChunk001Sub000Block066Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block066Part006CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block066Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block066Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block066Part006CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block066Part006SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block066Part006] using hcert

def TailChunk001Sub000Block066Part007SupportExplicit : Finset ℕ :=
  ([19222] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block066Part007 : ℚ :=
  (402132025 : ℚ) / 13019062765814784

def SurrogateDiagonalTailChunk001Sub000Block066Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19222
    = surrogateDiagTailX0RatChunk001Sub000Block066Part007

theorem surrogateDiagonalTailChunk001Sub000Block066Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block066Part007CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block066Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block066Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block066Part007CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block066Part007SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block066Part007] using hcert

def TailChunk001Sub000Block066Part008SupportExplicit : Finset ℕ :=
  ([19223] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block066Part008 : ℚ :=
  (138900742825 : ℚ) / 310240747382965567488

def SurrogateDiagonalTailChunk001Sub000Block066Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19223
    = surrogateDiagTailX0RatChunk001Sub000Block066Part008

theorem surrogateDiagonalTailChunk001Sub000Block066Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block066Part008CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block066Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block066Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block066Part008CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block066Part008SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block066Part008] using hcert

def TailChunk001Sub000Block066Part009SupportExplicit : Finset ℕ :=
  ([19226] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block066Part009 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block066Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19226
    = surrogateDiagTailX0RatChunk001Sub000Block066Part009

theorem surrogateDiagonalTailChunk001Sub000Block066Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block066Part009CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block066Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block066Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block066Part009CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block066Part009SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block066Part009] using hcert

def TailChunk001Sub000Block066Part010SupportExplicit : Finset ℕ :=
  ([19227] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block066Part010 : ℚ :=
  (546076411225 : ℚ) / 33418263704012587008

def SurrogateDiagonalTailChunk001Sub000Block066Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19227
    = surrogateDiagTailX0RatChunk001Sub000Block066Part010

theorem surrogateDiagonalTailChunk001Sub000Block066Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block066Part010CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block066Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block066Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block066Part010CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block066Part010SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block066Part010] using hcert

def TailChunk001Sub000Block066Part011SupportExplicit : Finset ℕ :=
  ([19229] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block066Part011 : ℚ :=
  (1665323591 : ℚ) / 419774738902548480

def SurrogateDiagonalTailChunk001Sub000Block066Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19229
    = surrogateDiagTailX0RatChunk001Sub000Block066Part011

theorem surrogateDiagonalTailChunk001Sub000Block066Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block066Part011CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block066Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block066Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block066Part011CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block066Part011SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block066Part011] using hcert

def TailChunk001Sub000Block066Part012SupportExplicit : Finset ℕ :=
  ([19230] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block066Part012 : ℚ :=
  (28774427929 : ℚ) / 68733220631347200

def SurrogateDiagonalTailChunk001Sub000Block066Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19230
    = surrogateDiagTailX0RatChunk001Sub000Block066Part012

theorem surrogateDiagonalTailChunk001Sub000Block066Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block066Part012CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block066Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block066Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block066Part012CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block066Part012SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block066Part012] using hcert

def TailChunk001Sub000Block066Part013SupportExplicit : Finset ℕ :=
  ([19231] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block066Part013 : ℚ :=
  (9245784025 : ℚ) / 136774138248188082

def SurrogateDiagonalTailChunk001Sub000Block066Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19231
    = surrogateDiagTailX0RatChunk001Sub000Block066Part013

theorem surrogateDiagonalTailChunk001Sub000Block066Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block066Part013CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block066Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block066Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block066Part013CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block066Part013SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block066Part013] using hcert

def TailChunk001Sub000Block066Part014SupportExplicit : Finset ℕ :=
  ([19234] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block066Part014 : ℚ :=
  (5585833088725 : ℚ) / 19489418944752716928

def SurrogateDiagonalTailChunk001Sub000Block066Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19234
    = surrogateDiagTailX0RatChunk001Sub000Block066Part014

theorem surrogateDiagonalTailChunk001Sub000Block066Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block066Part014CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block066Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block066Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block066Part014CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block066Part014SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block066Part014] using hcert

def TailChunk001Sub000Block066Part015SupportExplicit : Finset ℕ :=
  ([19235] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block066Part015 : ℚ :=
  (15718927897525 : ℚ) / 140056717566144595968

def SurrogateDiagonalTailChunk001Sub000Block066Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19235
    = surrogateDiagTailX0RatChunk001Sub000Block066Part015

theorem surrogateDiagonalTailChunk001Sub000Block066Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block066Part015CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block066Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block066Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block066Part015CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block066Part015SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block066Part015] using hcert

def TailChunk001Sub000Block066Part016SupportExplicit : Finset ℕ :=
  ([19237] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block066Part016 : ℚ :=
  (5782221390625 : ℚ) / 85590574442887947552

def SurrogateDiagonalTailChunk001Sub000Block066Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19237
    = surrogateDiagTailX0RatChunk001Sub000Block066Part016

theorem surrogateDiagonalTailChunk001Sub000Block066Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block066Part016CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block066Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block066Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block066Part016CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block066Part016SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block066Part016] using hcert

def TailChunk001Sub000Block066Part017SupportExplicit : Finset ℕ :=
  ([19238] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block066Part017 : ℚ :=
  (1445705640625 : ℚ) / 5349410902680496722

def SurrogateDiagonalTailChunk001Sub000Block066Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19238
    = surrogateDiagTailX0RatChunk001Sub000Block066Part017

theorem surrogateDiagonalTailChunk001Sub000Block066Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block066Part017CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block066Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block066Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block066Part017CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block066Part017SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block066Part017] using hcert

def TailChunk001Sub000Block066Part018SupportExplicit : Finset ℕ :=
  ([19241] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block066Part018 : ℚ :=
  (4746331151 : ℚ) / 67526192538000000

def SurrogateDiagonalTailChunk001Sub000Block066Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19241
    = surrogateDiagTailX0RatChunk001Sub000Block066Part018

theorem surrogateDiagonalTailChunk001Sub000Block066Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block066Part018CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block066Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block066Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block066Part018CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block066Part018SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block066Part018] using hcert

def TailChunk001Sub000Block066Part019SupportExplicit : Finset ℕ :=
  ([19243] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block066Part019 : ℚ :=
  (17465855476225 : ℚ) / 184798641362736826368

def SurrogateDiagonalTailChunk001Sub000Block066Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19243
    = surrogateDiagTailX0RatChunk001Sub000Block066Part019

theorem surrogateDiagonalTailChunk001Sub000Block066Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block066Part019CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block066Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block066Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block066Part019CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block066Part019SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block066Part019] using hcert

def TailChunk001Sub000Block066Part020SupportExplicit : Finset ℕ :=
  ([19245] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block066Part020 : ℚ :=
  (899129049275 : ℚ) / 3458190557188755456

def SurrogateDiagonalTailChunk001Sub000Block066Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19245
    = surrogateDiagTailX0RatChunk001Sub000Block066Part020

theorem surrogateDiagonalTailChunk001Sub000Block066Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block066Part020CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block066Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block066Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block066Part020CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block066Part020SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block066Part020] using hcert

def TailChunk001Sub000Block066Part021SupportExplicit : Finset ℕ :=
  ([19246] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block066Part021 : ℚ :=
  (1446908265625 : ℚ) / 5358315454899629682

def SurrogateDiagonalTailChunk001Sub000Block066Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19246
    = surrogateDiagTailX0RatChunk001Sub000Block066Part021

theorem surrogateDiagonalTailChunk001Sub000Block066Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block066Part021CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block066Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block066Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block066Part021CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block066Part021SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block066Part021] using hcert

def TailChunk001Sub000Block066Part022SupportExplicit : Finset ℕ :=
  ([19247] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block066Part022 : ℚ :=
  (913140780575 : ℚ) / 11970466988032751616

def SurrogateDiagonalTailChunk001Sub000Block066Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19247
    = surrogateDiagTailX0RatChunk001Sub000Block066Part022

theorem surrogateDiagonalTailChunk001Sub000Block066Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block066Part022CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block066Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block066Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block066Part022CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block066Part022SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block066Part022] using hcert

def TailChunk001Sub000Block066Part023SupportExplicit : Finset ℕ :=
  ([19249] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block066Part023 : ℚ :=
  (5789437515625 : ℚ) / 85804350359918026752

def SurrogateDiagonalTailChunk001Sub000Block066Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19249
    = surrogateDiagTailX0RatChunk001Sub000Block066Part023

theorem surrogateDiagonalTailChunk001Sub000Block066Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block066Part023CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block066Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block066Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block066Part023CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block066Part023SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block066Part023] using hcert

def TailChunk001Sub000Block066Part024SupportExplicit : Finset ℕ :=
  ([19253] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block066Part024 : ℚ :=
  (799696095337 : ℚ) / 9950816004223795200

def SurrogateDiagonalTailChunk001Sub000Block066Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19253
    = surrogateDiagTailX0RatChunk001Sub000Block066Part024

theorem surrogateDiagonalTailChunk001Sub000Block066Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block066Part024CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block066Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block066Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block066Part024CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block066Part024SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block066Part024] using hcert

def surrogateDiagonalTailChunk001Sub000Block066HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block066Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block066Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block066Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block066Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block066Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block066Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block066Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block066Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block066Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block066Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block066Head : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block066Part000
    + surrogateDiagTailX0RatChunk001Sub000Block066Part001
    + surrogateDiagTailX0RatChunk001Sub000Block066Part002
    + surrogateDiagTailX0RatChunk001Sub000Block066Part003
    + surrogateDiagTailX0RatChunk001Sub000Block066Part004
    + surrogateDiagTailX0RatChunk001Sub000Block066Part005
    + surrogateDiagTailX0RatChunk001Sub000Block066Part006
    + surrogateDiagTailX0RatChunk001Sub000Block066Part007
    + surrogateDiagTailX0RatChunk001Sub000Block066Part008
    + surrogateDiagTailX0RatChunk001Sub000Block066Part009

def surrogateDiagonalTailChunk001Sub000Block066MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block066Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block066Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block066Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block066Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block066Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block066Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block066Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block066Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block066Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block066Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block066Mid : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block066Part010
    + surrogateDiagTailX0RatChunk001Sub000Block066Part011
    + surrogateDiagTailX0RatChunk001Sub000Block066Part012
    + surrogateDiagTailX0RatChunk001Sub000Block066Part013
    + surrogateDiagTailX0RatChunk001Sub000Block066Part014
    + surrogateDiagTailX0RatChunk001Sub000Block066Part015
    + surrogateDiagTailX0RatChunk001Sub000Block066Part016
    + surrogateDiagTailX0RatChunk001Sub000Block066Part017
    + surrogateDiagTailX0RatChunk001Sub000Block066Part018
    + surrogateDiagTailX0RatChunk001Sub000Block066Part019

def surrogateDiagonalTailChunk001Sub000Block066TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block066Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block066Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block066Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block066Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block066Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block066Tail : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block066Part020
    + surrogateDiagTailX0RatChunk001Sub000Block066Part021
    + surrogateDiagTailX0RatChunk001Sub000Block066Part022
    + surrogateDiagTailX0RatChunk001Sub000Block066Part023
    + surrogateDiagTailX0RatChunk001Sub000Block066Part024

def surrogateDiagonalTailChunk001Sub000Block066Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk001Sub000Block066HeadSum X0
    + surrogateDiagonalTailChunk001Sub000Block066MidSum X0
    + surrogateDiagonalTailChunk001Sub000Block066TailSum X0

def surrogateDiagTailX0RatChunk001Sub000Block066 : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block066Part000
    + surrogateDiagTailX0RatChunk001Sub000Block066Part001
    + surrogateDiagTailX0RatChunk001Sub000Block066Part002
    + surrogateDiagTailX0RatChunk001Sub000Block066Part003
    + surrogateDiagTailX0RatChunk001Sub000Block066Part004
    + surrogateDiagTailX0RatChunk001Sub000Block066Part005
    + surrogateDiagTailX0RatChunk001Sub000Block066Part006
    + surrogateDiagTailX0RatChunk001Sub000Block066Part007
    + surrogateDiagTailX0RatChunk001Sub000Block066Part008
    + surrogateDiagTailX0RatChunk001Sub000Block066Part009
    + surrogateDiagTailX0RatChunk001Sub000Block066Part010
    + surrogateDiagTailX0RatChunk001Sub000Block066Part011
    + surrogateDiagTailX0RatChunk001Sub000Block066Part012
    + surrogateDiagTailX0RatChunk001Sub000Block066Part013
    + surrogateDiagTailX0RatChunk001Sub000Block066Part014
    + surrogateDiagTailX0RatChunk001Sub000Block066Part015
    + surrogateDiagTailX0RatChunk001Sub000Block066Part016
    + surrogateDiagTailX0RatChunk001Sub000Block066Part017
    + surrogateDiagTailX0RatChunk001Sub000Block066Part018
    + surrogateDiagTailX0RatChunk001Sub000Block066Part019
    + surrogateDiagTailX0RatChunk001Sub000Block066Part020
    + surrogateDiagTailX0RatChunk001Sub000Block066Part021
    + surrogateDiagTailX0RatChunk001Sub000Block066Part022
    + surrogateDiagTailX0RatChunk001Sub000Block066Part023
    + surrogateDiagTailX0RatChunk001Sub000Block066Part024

theorem surrogateDiagTailX0RatChunk001Sub000Block066_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk001Sub000Block066Head + surrogateDiagTailX0RatChunk001Sub000Block066Mid + surrogateDiagTailX0RatChunk001Sub000Block066Tail =
      surrogateDiagTailX0RatChunk001Sub000Block066 := by
  unfold surrogateDiagTailX0RatChunk001Sub000Block066Head surrogateDiagTailX0RatChunk001Sub000Block066Mid surrogateDiagTailX0RatChunk001Sub000Block066Tail surrogateDiagTailX0RatChunk001Sub000Block066
  ring

def SurrogateDiagonalTailChunk001Sub000Block066HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block066HeadSum X0 = surrogateDiagTailX0RatChunk001Sub000Block066Head

def SurrogateDiagonalTailChunk001Sub000Block066MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block066MidSum X0 = surrogateDiagTailX0RatChunk001Sub000Block066Mid

def SurrogateDiagonalTailChunk001Sub000Block066TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block066TailSum X0 = surrogateDiagTailX0RatChunk001Sub000Block066Tail

theorem surrogateDiagonalTailChunk001Sub000Block066_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk001Sub000Block066HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk001Sub000Block066MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk001Sub000Block066TailCertificateAt X0) :
    surrogateDiagonalTailChunk001Sub000Block066Sum X0 = surrogateDiagTailX0RatChunk001Sub000Block066 := by
  unfold SurrogateDiagonalTailChunk001Sub000Block066HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk001Sub000Block066MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk001Sub000Block066TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk001Sub000Block066Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk001Sub000Block066_eq_head_add_mid_add_tail

/-- Block 067 covers tail-support indices [11675,11700) and q from 19254 to 19294. -/

def TailChunk001Sub000Block067Part000SupportExplicit : Finset ℕ :=
  ([19254] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block067Part000 : ℚ :=
  (1608579710225 : ℚ) / 2118625934812790784

def SurrogateDiagonalTailChunk001Sub000Block067Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19254
    = surrogateDiagTailX0RatChunk001Sub000Block067Part000

theorem surrogateDiagonalTailChunk001Sub000Block067Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block067Part000CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block067Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block067Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block067Part000CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block067Part000SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block067Part000] using hcert

def TailChunk001Sub000Block067Part001SupportExplicit : Finset ℕ :=
  ([19255] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block067Part001 : ℚ :=
  (630065559049 : ℚ) / 5625611457312000000

def SurrogateDiagonalTailChunk001Sub000Block067Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19255
    = surrogateDiagTailX0RatChunk001Sub000Block067Part001

theorem surrogateDiagonalTailChunk001Sub000Block067Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block067Part001CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block067Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block067Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block067Part001CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block067Part001SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block067Part001] using hcert

def TailChunk001Sub000Block067Part002SupportExplicit : Finset ℕ :=
  ([19258] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block067Part002 : ℚ :=
  (1448713140625 : ℚ) / 5371693121431686432

def SurrogateDiagonalTailChunk001Sub000Block067Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19258
    = surrogateDiagTailX0RatChunk001Sub000Block067Part002

theorem surrogateDiagonalTailChunk001Sub000Block067Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block067Part002CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block067Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block067Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block067Part002CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block067Part002SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block067Part002] using hcert

def TailChunk001Sub000Block067Part003SupportExplicit : Finset ℕ :=
  ([19259] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block067Part003 : ℚ :=
  (5795454390625 : ℚ) / 85982802647954019762

def SurrogateDiagonalTailChunk001Sub000Block067Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19259
    = surrogateDiagTailX0RatChunk001Sub000Block067Part003

theorem surrogateDiagonalTailChunk001Sub000Block067Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block067Part003CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block067Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block067Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block067Part003CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block067Part003SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block067Part003] using hcert

def TailChunk001Sub000Block067Part004SupportExplicit : Finset ℕ :=
  ([19261] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block067Part004 : ℚ :=
  (19168158187 : ℚ) / 197090171368243200

def SurrogateDiagonalTailChunk001Sub000Block067Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19261
    = surrogateDiagTailX0RatChunk001Sub000Block067Part004

theorem surrogateDiagonalTailChunk001Sub000Block067Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block067Part004CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block067Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block067Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block067Part004CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block067Part004SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block067Part004] using hcert

def TailChunk001Sub000Block067Part005SupportExplicit : Finset ℕ :=
  ([19262] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block067Part005 : ℚ :=
  (2318904025 : ℚ) / 8601852648134322

def SurrogateDiagonalTailChunk001Sub000Block067Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19262
    = surrogateDiagTailX0RatChunk001Sub000Block067Part005

theorem surrogateDiagonalTailChunk001Sub000Block067Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block067Part005CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block067Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block067Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block067Part005CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block067Part005SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block067Part005] using hcert

def TailChunk001Sub000Block067Part006SupportExplicit : Finset ℕ :=
  ([19263] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block067Part006 : ℚ :=
  (412188974317 : ℚ) / 2718610219657267200

def SurrogateDiagonalTailChunk001Sub000Block067Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19263
    = surrogateDiagTailX0RatChunk001Sub000Block067Part006

theorem surrogateDiagonalTailChunk001Sub000Block067Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block067Part006CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block067Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block067Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block067Part006CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block067Part006SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block067Part006] using hcert

def TailChunk001Sub000Block067Part007SupportExplicit : Finset ℕ :=
  ([19265] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block067Part007 : ℚ :=
  (15768007266775 : ℚ) / 140932753787032731648

def SurrogateDiagonalTailChunk001Sub000Block067Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19265
    = surrogateDiagTailX0RatChunk001Sub000Block067Part007

theorem surrogateDiagonalTailChunk001Sub000Block067Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block067Part007CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block067Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block067Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block067Part007CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block067Part007SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block067Part007] using hcert

def TailChunk001Sub000Block067Part008SupportExplicit : Finset ℕ :=
  ([19267] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block067Part008 : ℚ :=
  (5800270140625 : ℚ) / 86125764774680423442

def SurrogateDiagonalTailChunk001Sub000Block067Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19267
    = surrogateDiagTailX0RatChunk001Sub000Block067Part008

theorem surrogateDiagonalTailChunk001Sub000Block067Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block067Part008CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block067Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block067Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block067Part008CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block067Part008SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block067Part008] using hcert

def TailChunk001Sub000Block067Part009SupportExplicit : Finset ℕ :=
  ([19270] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block067Part009 : ℚ :=
  (10427401797 : ℚ) / 19566216221818880

def SurrogateDiagonalTailChunk001Sub000Block067Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19270
    = surrogateDiagTailX0RatChunk001Sub000Block067Part009

theorem surrogateDiagonalTailChunk001Sub000Block067Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block067Part009CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block067Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block067Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block067Part009CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block067Part009SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block067Part009] using hcert

def TailChunk001Sub000Block067Part010SupportExplicit : Finset ℕ :=
  ([19271] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block067Part010 : ℚ :=
  (17516733772225 : ℚ) / 185876967555090874368

def SurrogateDiagonalTailChunk001Sub000Block067Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19271
    = surrogateDiagTailX0RatChunk001Sub000Block067Part010

theorem surrogateDiagonalTailChunk001Sub000Block067Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block067Part010CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block067Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block067Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block067Part010CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block067Part010SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block067Part010] using hcert

def TailChunk001Sub000Block067Part011SupportExplicit : Finset ℕ :=
  ([19273] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block067Part011 : ℚ :=
  (5803883265625 : ℚ) / 86233103306327020032

def SurrogateDiagonalTailChunk001Sub000Block067Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19273
    = surrogateDiagTailX0RatChunk001Sub000Block067Part011

theorem surrogateDiagonalTailChunk001Sub000Block067Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block067Part011CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block067Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block067Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block067Part011CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block067Part011SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block067Part011] using hcert

def TailChunk001Sub000Block067Part012SupportExplicit : Finset ℕ :=
  ([19274] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block067Part012 : ℚ :=
  (676646480525 : ℚ) / 2235284065883772816

def SurrogateDiagonalTailChunk001Sub000Block067Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19274
    = surrogateDiagTailX0RatChunk001Sub000Block067Part012

theorem surrogateDiagonalTailChunk001Sub000Block067Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block067Part012CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block067Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block067Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block067Part012CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block067Part012SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block067Part012] using hcert

def TailChunk001Sub000Block067Part013SupportExplicit : Finset ℕ :=
  ([19277] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block067Part013 : ℚ :=
  (1362197227 : ℚ) / 18955499013734400

def SurrogateDiagonalTailChunk001Sub000Block067Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19277
    = surrogateDiagTailX0RatChunk001Sub000Block067Part013

theorem surrogateDiagonalTailChunk001Sub000Block067Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block067Part013CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block067Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block067Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block067Part013CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block067Part013SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block067Part013] using hcert

def TailChunk001Sub000Block067Part014SupportExplicit : Finset ℕ :=
  ([19279] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block067Part014 : ℚ :=
  (9166192175 : ℚ) / 114365721618929664

def SurrogateDiagonalTailChunk001Sub000Block067Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19279
    = surrogateDiagTailX0RatChunk001Sub000Block067Part014

theorem surrogateDiagonalTailChunk001Sub000Block067Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block067Part014CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block067Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block067Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block067Part014CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block067Part014SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block067Part014] using hcert

def TailChunk001Sub000Block067Part015SupportExplicit : Finset ℕ :=
  ([19281] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block067Part015 : ℚ :=
  (10323993357325 : ℚ) / 68219687615784340608

def SurrogateDiagonalTailChunk001Sub000Block067Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19281
    = surrogateDiagTailX0RatChunk001Sub000Block067Part015

theorem surrogateDiagonalTailChunk001Sub000Block067Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block067Part015CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block067Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block067Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block067Part015CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block067Part015SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block067Part015] using hcert

def TailChunk001Sub000Block067Part016SupportExplicit : Finset ℕ :=
  ([19282] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block067Part016 : ℚ :=
  (4404678497 : ℚ) / 14964032408040000

def SurrogateDiagonalTailChunk001Sub000Block067Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19282
    = surrogateDiagTailX0RatChunk001Sub000Block067Part016

theorem surrogateDiagonalTailChunk001Sub000Block067Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block067Part016CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block067Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block067Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block067Part016CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block067Part016SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block067Part016] using hcert

def TailChunk001Sub000Block067Part017SupportExplicit : Finset ℕ :=
  ([19283] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block067Part017 : ℚ :=
  (195726667369 : ℚ) / 2355934794244300800

def SurrogateDiagonalTailChunk001Sub000Block067Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19283
    = surrogateDiagTailX0RatChunk001Sub000Block067Part017

theorem surrogateDiagonalTailChunk001Sub000Block067Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block067Part017CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block067Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block067Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block067Part017CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block067Part017SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block067Part017] using hcert

def TailChunk001Sub000Block067Part018SupportExplicit : Finset ℕ :=
  ([19285] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block067Part018 : ℚ :=
  (3270056732825 : ℚ) / 17843198906414923776

def SurrogateDiagonalTailChunk001Sub000Block067Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19285
    = surrogateDiagTailX0RatChunk001Sub000Block067Part018

theorem surrogateDiagonalTailChunk001Sub000Block067Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block067Part018CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block067Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block067Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block067Part018CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block067Part018SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block067Part018] using hcert

def TailChunk001Sub000Block067Part019SupportExplicit : Finset ℕ :=
  ([19286] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block067Part019 : ℚ :=
  (1452928890625 : ℚ) / 5403005083396501362

def SurrogateDiagonalTailChunk001Sub000Block067Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19286
    = surrogateDiagTailX0RatChunk001Sub000Block067Part019

theorem surrogateDiagonalTailChunk001Sub000Block067Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block067Part019CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block067Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block067Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block067Part019CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block067Part019SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block067Part019] using hcert

def TailChunk001Sub000Block067Part020SupportExplicit : Finset ℕ :=
  ([19289] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block067Part020 : ℚ :=
  (5813523765625 : ℚ) / 86519829919619707392

def SurrogateDiagonalTailChunk001Sub000Block067Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19289
    = surrogateDiagTailX0RatChunk001Sub000Block067Part020

theorem surrogateDiagonalTailChunk001Sub000Block067Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block067Part020CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block067Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block067Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block067Part020CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block067Part020SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block067Part020] using hcert

def TailChunk001Sub000Block067Part021SupportExplicit : Finset ℕ :=
  ([19290] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block067Part021 : ℚ :=
  (1147680739925 : ℚ) / 869955270290325504

def SurrogateDiagonalTailChunk001Sub000Block067Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19290
    = surrogateDiagTailX0RatChunk001Sub000Block067Part021

theorem surrogateDiagonalTailChunk001Sub000Block067Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block067Part021CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block067Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block067Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block067Part021CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block067Part021SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block067Part021] using hcert

def TailChunk001Sub000Block067Part022SupportExplicit : Finset ℕ :=
  ([19291] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block067Part022 : ℚ :=
  (7248582893 : ℚ) / 104277651360000000

def SurrogateDiagonalTailChunk001Sub000Block067Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19291
    = surrogateDiagTailX0RatChunk001Sub000Block067Part022

theorem surrogateDiagonalTailChunk001Sub000Block067Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block067Part022CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block067Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block067Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block067Part022CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block067Part022SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block067Part022] using hcert

def TailChunk001Sub000Block067Part023SupportExplicit : Finset ℕ :=
  ([19293] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block067Part023 : ℚ :=
  (9908694697975 : ℚ) / 61596188269835747328

def SurrogateDiagonalTailChunk001Sub000Block067Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19293
    = surrogateDiagTailX0RatChunk001Sub000Block067Part023

theorem surrogateDiagonalTailChunk001Sub000Block067Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block067Part023CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block067Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block067Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block067Part023CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block067Part023SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block067Part023] using hcert

def TailChunk001Sub000Block067Part024SupportExplicit : Finset ℕ :=
  ([19294] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block067Part024 : ℚ :=
  (199668720241 : ℚ) / 588983698561075200

def SurrogateDiagonalTailChunk001Sub000Block067Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19294
    = surrogateDiagTailX0RatChunk001Sub000Block067Part024

theorem surrogateDiagonalTailChunk001Sub000Block067Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block067Part024CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block067Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block067Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block067Part024CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block067Part024SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block067Part024] using hcert

def surrogateDiagonalTailChunk001Sub000Block067HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block067Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block067Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block067Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block067Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block067Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block067Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block067Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block067Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block067Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block067Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block067Head : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block067Part000
    + surrogateDiagTailX0RatChunk001Sub000Block067Part001
    + surrogateDiagTailX0RatChunk001Sub000Block067Part002
    + surrogateDiagTailX0RatChunk001Sub000Block067Part003
    + surrogateDiagTailX0RatChunk001Sub000Block067Part004
    + surrogateDiagTailX0RatChunk001Sub000Block067Part005
    + surrogateDiagTailX0RatChunk001Sub000Block067Part006
    + surrogateDiagTailX0RatChunk001Sub000Block067Part007
    + surrogateDiagTailX0RatChunk001Sub000Block067Part008
    + surrogateDiagTailX0RatChunk001Sub000Block067Part009

def surrogateDiagonalTailChunk001Sub000Block067MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block067Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block067Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block067Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block067Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block067Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block067Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block067Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block067Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block067Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block067Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block067Mid : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block067Part010
    + surrogateDiagTailX0RatChunk001Sub000Block067Part011
    + surrogateDiagTailX0RatChunk001Sub000Block067Part012
    + surrogateDiagTailX0RatChunk001Sub000Block067Part013
    + surrogateDiagTailX0RatChunk001Sub000Block067Part014
    + surrogateDiagTailX0RatChunk001Sub000Block067Part015
    + surrogateDiagTailX0RatChunk001Sub000Block067Part016
    + surrogateDiagTailX0RatChunk001Sub000Block067Part017
    + surrogateDiagTailX0RatChunk001Sub000Block067Part018
    + surrogateDiagTailX0RatChunk001Sub000Block067Part019

def surrogateDiagonalTailChunk001Sub000Block067TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block067Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block067Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block067Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block067Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block067Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block067Tail : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block067Part020
    + surrogateDiagTailX0RatChunk001Sub000Block067Part021
    + surrogateDiagTailX0RatChunk001Sub000Block067Part022
    + surrogateDiagTailX0RatChunk001Sub000Block067Part023
    + surrogateDiagTailX0RatChunk001Sub000Block067Part024

def surrogateDiagonalTailChunk001Sub000Block067Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk001Sub000Block067HeadSum X0
    + surrogateDiagonalTailChunk001Sub000Block067MidSum X0
    + surrogateDiagonalTailChunk001Sub000Block067TailSum X0

def surrogateDiagTailX0RatChunk001Sub000Block067 : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block067Part000
    + surrogateDiagTailX0RatChunk001Sub000Block067Part001
    + surrogateDiagTailX0RatChunk001Sub000Block067Part002
    + surrogateDiagTailX0RatChunk001Sub000Block067Part003
    + surrogateDiagTailX0RatChunk001Sub000Block067Part004
    + surrogateDiagTailX0RatChunk001Sub000Block067Part005
    + surrogateDiagTailX0RatChunk001Sub000Block067Part006
    + surrogateDiagTailX0RatChunk001Sub000Block067Part007
    + surrogateDiagTailX0RatChunk001Sub000Block067Part008
    + surrogateDiagTailX0RatChunk001Sub000Block067Part009
    + surrogateDiagTailX0RatChunk001Sub000Block067Part010
    + surrogateDiagTailX0RatChunk001Sub000Block067Part011
    + surrogateDiagTailX0RatChunk001Sub000Block067Part012
    + surrogateDiagTailX0RatChunk001Sub000Block067Part013
    + surrogateDiagTailX0RatChunk001Sub000Block067Part014
    + surrogateDiagTailX0RatChunk001Sub000Block067Part015
    + surrogateDiagTailX0RatChunk001Sub000Block067Part016
    + surrogateDiagTailX0RatChunk001Sub000Block067Part017
    + surrogateDiagTailX0RatChunk001Sub000Block067Part018
    + surrogateDiagTailX0RatChunk001Sub000Block067Part019
    + surrogateDiagTailX0RatChunk001Sub000Block067Part020
    + surrogateDiagTailX0RatChunk001Sub000Block067Part021
    + surrogateDiagTailX0RatChunk001Sub000Block067Part022
    + surrogateDiagTailX0RatChunk001Sub000Block067Part023
    + surrogateDiagTailX0RatChunk001Sub000Block067Part024

theorem surrogateDiagTailX0RatChunk001Sub000Block067_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk001Sub000Block067Head + surrogateDiagTailX0RatChunk001Sub000Block067Mid + surrogateDiagTailX0RatChunk001Sub000Block067Tail =
      surrogateDiagTailX0RatChunk001Sub000Block067 := by
  unfold surrogateDiagTailX0RatChunk001Sub000Block067Head surrogateDiagTailX0RatChunk001Sub000Block067Mid surrogateDiagTailX0RatChunk001Sub000Block067Tail surrogateDiagTailX0RatChunk001Sub000Block067
  ring

def SurrogateDiagonalTailChunk001Sub000Block067HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block067HeadSum X0 = surrogateDiagTailX0RatChunk001Sub000Block067Head

def SurrogateDiagonalTailChunk001Sub000Block067MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block067MidSum X0 = surrogateDiagTailX0RatChunk001Sub000Block067Mid

def SurrogateDiagonalTailChunk001Sub000Block067TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block067TailSum X0 = surrogateDiagTailX0RatChunk001Sub000Block067Tail

theorem surrogateDiagonalTailChunk001Sub000Block067_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk001Sub000Block067HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk001Sub000Block067MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk001Sub000Block067TailCertificateAt X0) :
    surrogateDiagonalTailChunk001Sub000Block067Sum X0 = surrogateDiagTailX0RatChunk001Sub000Block067 := by
  unfold SurrogateDiagonalTailChunk001Sub000Block067HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk001Sub000Block067MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk001Sub000Block067TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk001Sub000Block067Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk001Sub000Block067_eq_head_add_mid_add_tail

/-- Block 068 covers tail-support indices [11700,11725) and q from 19295 to 19335. -/

def TailChunk001Sub000Block068Part000SupportExplicit : Finset ℕ :=
  ([19295] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block068Part000 : ℚ :=
  (13305435883525 : ℚ) / 109441115595428855808

def SurrogateDiagonalTailChunk001Sub000Block068Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19295
    = surrogateDiagTailX0RatChunk001Sub000Block068Part000

theorem surrogateDiagonalTailChunk001Sub000Block068Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block068Part000CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block068Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block068Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block068Part000CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block068Part000SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block068Part000] using hcert

def TailChunk001Sub000Block068Part001SupportExplicit : Finset ℕ :=
  ([19297] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block068Part001 : ℚ :=
  (21470912288875 : ℚ) / 288864156914430100608

def SurrogateDiagonalTailChunk001Sub000Block068Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19297
    = surrogateDiagTailX0RatChunk001Sub000Block068Part001

theorem surrogateDiagonalTailChunk001Sub000Block068Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block068Part001CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block068Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block068Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block068Part001CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block068Part001SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block068Part001] using hcert

def TailChunk001Sub000Block068Part002SupportExplicit : Finset ℕ :=
  ([19298] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block068Part002 : ℚ :=
  (1454737515625 : ℚ) / 5416466316573745152

def SurrogateDiagonalTailChunk001Sub000Block068Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19298
    = surrogateDiagTailX0RatChunk001Sub000Block068Part002

theorem surrogateDiagonalTailChunk001Sub000Block068Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block068Part002CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block068Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block068Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block068Part002CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block068Part002SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block068Part002] using hcert

def TailChunk001Sub000Block068Part003SupportExplicit : Finset ℕ :=
  ([19299] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block068Part003 : ℚ :=
  (7956754441825 : ℚ) / 36823288275741984768

def SurrogateDiagonalTailChunk001Sub000Block068Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19299
    = surrogateDiagTailX0RatChunk001Sub000Block068Part003

theorem surrogateDiagonalTailChunk001Sub000Block068Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block068Part003CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block068Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block068Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block068Part003CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block068Part003SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block068Part003] using hcert

def TailChunk001Sub000Block068Part004SupportExplicit : Finset ℕ :=
  ([19301] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block068Part004 : ℚ :=
  (372528601 : ℚ) / 5551061994400800

def SurrogateDiagonalTailChunk001Sub000Block068Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19301
    = surrogateDiagTailX0RatChunk001Sub000Block068Part004

theorem surrogateDiagonalTailChunk001Sub000Block068Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block068Part004CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block068Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block068Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block068Part004CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block068Part004SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block068Part004] using hcert

def TailChunk001Sub000Block068Part005SupportExplicit : Finset ℕ :=
  ([19302] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block068Part005 : ℚ :=
  (2586288678325 : ℚ) / 4279677089638514688

def SurrogateDiagonalTailChunk001Sub000Block068Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19302
    = surrogateDiagTailX0RatChunk001Sub000Block068Part005

theorem surrogateDiagonalTailChunk001Sub000Block068Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block068Part005CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block068Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block068Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block068Part005CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block068Part005SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block068Part005] using hcert

def TailChunk001Sub000Block068Part006SupportExplicit : Finset ℕ :=
  ([19303] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block068Part006 : ℚ :=
  (11335988522975 : ℚ) / 163208418485310849024

def SurrogateDiagonalTailChunk001Sub000Block068Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19303
    = surrogateDiagTailX0RatChunk001Sub000Block068Part006

theorem surrogateDiagonalTailChunk001Sub000Block068Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block068Part006CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block068Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block068Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block068Part006CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block068Part006SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block068Part006] using hcert

def TailChunk001Sub000Block068Part007SupportExplicit : Finset ℕ :=
  ([19307] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block068Part007 : ℚ :=
  (22268033126875 : ℚ) / 313426762317711802368

def SurrogateDiagonalTailChunk001Sub000Block068Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19307
    = surrogateDiagTailX0RatChunk001Sub000Block068Part007

theorem surrogateDiagonalTailChunk001Sub000Block068Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block068Part007CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block068Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block068Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block068Part007CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block068Part007SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block068Part007] using hcert

def TailChunk001Sub000Block068Part008SupportExplicit : Finset ℕ :=
  ([19309] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block068Part008 : ℚ :=
  (5825585640625 : ℚ) / 86879242998931521312

def SurrogateDiagonalTailChunk001Sub000Block068Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19309
    = surrogateDiagTailX0RatChunk001Sub000Block068Part008

theorem surrogateDiagonalTailChunk001Sub000Block068Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block068Part008CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block068Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block068Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block068Part008CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block068Part008SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block068Part008] using hcert

def TailChunk001Sub000Block068Part009SupportExplicit : Finset ℕ :=
  ([19310] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block068Part009 : ℚ :=
  (55898862339 : ℚ) / 118422655880550400

def SurrogateDiagonalTailChunk001Sub000Block068Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19310
    = surrogateDiagTailX0RatChunk001Sub000Block068Part009

theorem surrogateDiagonalTailChunk001Sub000Block068Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block068Part009CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block068Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block068Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block068Part009CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block068Part009SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block068Part009] using hcert

def TailChunk001Sub000Block068Part010SupportExplicit : Finset ℕ :=
  ([19311] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block068Part010 : ℚ :=
  (394060392997 : ℚ) / 2426303873758003200

def SurrogateDiagonalTailChunk001Sub000Block068Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19311
    = surrogateDiagTailX0RatChunk001Sub000Block068Part010

theorem surrogateDiagonalTailChunk001Sub000Block068Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block068Part010CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block068Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block068Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block068Part010CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block068Part010SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block068Part010] using hcert

def TailChunk001Sub000Block068Part011SupportExplicit : Finset ℕ :=
  ([19313] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block068Part011 : ℚ :=
  (9065170181 : ℚ) / 87453070604697600

def SurrogateDiagonalTailChunk001Sub000Block068Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19313
    = surrogateDiagTailX0RatChunk001Sub000Block068Part011

theorem surrogateDiagonalTailChunk001Sub000Block068Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block068Part011CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block068Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block068Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block068Part011CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block068Part011SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block068Part011] using hcert

def TailChunk001Sub000Block068Part012SupportExplicit : Finset ℕ :=
  ([19315] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block068Part012 : ℚ :=
  (932268390625 : ℚ) / 8900121169177615488

def SurrogateDiagonalTailChunk001Sub000Block068Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19315
    = surrogateDiagTailX0RatChunk001Sub000Block068Part012

theorem surrogateDiagonalTailChunk001Sub000Block068Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block068Part012CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block068Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block068Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block068Part012CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block068Part012SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block068Part012] using hcert

def TailChunk001Sub000Block068Part013SupportExplicit : Finset ℕ :=
  ([19317] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block068Part013 : ℚ :=
  (3297325701075 : ℚ) / 20427374313281683456

def SurrogateDiagonalTailChunk001Sub000Block068Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19317
    = surrogateDiagTailX0RatChunk001Sub000Block068Part013

theorem surrogateDiagonalTailChunk001Sub000Block068Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block068Part013CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block068Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block068Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block068Part013CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block068Part013SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block068Part013] using hcert

def TailChunk001Sub000Block068Part014SupportExplicit : Finset ℕ :=
  ([19318] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block068Part014 : ℚ :=
  (5166066704875 : ℚ) / 15716920781701859328

def SurrogateDiagonalTailChunk001Sub000Block068Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19318
    = surrogateDiagTailX0RatChunk001Sub000Block068Part014

theorem surrogateDiagonalTailChunk001Sub000Block068Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block068Part014CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block068Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block068Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block068Part014CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block068Part014SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block068Part014] using hcert

def TailChunk001Sub000Block068Part015SupportExplicit : Finset ℕ :=
  ([19319] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block068Part015 : ℚ :=
  (5831621265625 : ℚ) / 87059368876406471922

def SurrogateDiagonalTailChunk001Sub000Block068Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19319
    = surrogateDiagTailX0RatChunk001Sub000Block068Part015

theorem surrogateDiagonalTailChunk001Sub000Block068Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block068Part015CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block068Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block068Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block068Part015CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block068Part015SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block068Part015] using hcert

def TailChunk001Sub000Block068Part016SupportExplicit : Finset ℕ :=
  ([19322] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block068Part016 : ℚ :=
  (2333373025 : ℚ) / 8709542763600672

def SurrogateDiagonalTailChunk001Sub000Block068Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19322
    = surrogateDiagTailX0RatChunk001Sub000Block068Part016

theorem surrogateDiagonalTailChunk001Sub000Block068Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block068Part016CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block068Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block068Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block068Part016CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block068Part016SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block068Part016] using hcert

def TailChunk001Sub000Block068Part017SupportExplicit : Finset ℕ :=
  ([19326] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block068Part017 : ℚ :=
  (103708987117 : ℚ) / 172040350885939200

def SurrogateDiagonalTailChunk001Sub000Block068Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19326
    = surrogateDiagTailX0RatChunk001Sub000Block068Part017

theorem surrogateDiagonalTailChunk001Sub000Block068Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block068Part017CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block068Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block068Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block068Part017CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block068Part017SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block068Part017] using hcert

def TailChunk001Sub000Block068Part018SupportExplicit : Finset ℕ :=
  ([19327] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block068Part018 : ℚ :=
  (288488926463 : ℚ) / 2531756250000000000

def SurrogateDiagonalTailChunk001Sub000Block068Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19327
    = surrogateDiagTailX0RatChunk001Sub000Block068Part018

theorem surrogateDiagonalTailChunk001Sub000Block068Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block068Part018CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block068Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block068Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block068Part018CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block068Part018SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block068Part018] using hcert

def TailChunk001Sub000Block068Part019SupportExplicit : Finset ℕ :=
  ([19329] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block068Part019 : ℚ :=
  (9368868036775 : ℚ) / 53529596719244771328

def SurrogateDiagonalTailChunk001Sub000Block068Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19329
    = surrogateDiagTailX0RatChunk001Sub000Block068Part019

theorem surrogateDiagonalTailChunk001Sub000Block068Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block068Part019CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block068Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block068Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block068Part019CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block068Part019SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block068Part019] using hcert

def TailChunk001Sub000Block068Part020SupportExplicit : Finset ℕ :=
  ([19330] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block068Part020 : ℚ :=
  (600157932475 : ℚ) / 1274081684275298304

def SurrogateDiagonalTailChunk001Sub000Block068Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19330
    = surrogateDiagTailX0RatChunk001Sub000Block068Part020

theorem surrogateDiagonalTailChunk001Sub000Block068Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block068Part020CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block068Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block068Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block068Part020CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block068Part020SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block068Part020] using hcert

def TailChunk001Sub000Block068Part021SupportExplicit : Finset ℕ :=
  ([19331] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block068Part021 : ℚ :=
  (20154801107125 : ℚ) / 252829112849152985088

def SurrogateDiagonalTailChunk001Sub000Block068Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19331
    = surrogateDiagTailX0RatChunk001Sub000Block068Part021

theorem surrogateDiagonalTailChunk001Sub000Block068Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block068Part021CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block068Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block068Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block068Part021CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block068Part021SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block068Part021] using hcert

def TailChunk001Sub000Block068Part022SupportExplicit : Finset ℕ :=
  ([19333] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block068Part022 : ℚ :=
  (5840076390625 : ℚ) / 87312015477124522272

def SurrogateDiagonalTailChunk001Sub000Block068Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19333
    = surrogateDiagTailX0RatChunk001Sub000Block068Part022

theorem surrogateDiagonalTailChunk001Sub000Block068Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block068Part022CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block068Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block068Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block068Part022CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block068Part022SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block068Part022] using hcert

def TailChunk001Sub000Block068Part023SupportExplicit : Finset ℕ :=
  ([19334] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block068Part023 : ℚ :=
  (45253451803 : ℚ) / 117529856535052800

def SurrogateDiagonalTailChunk001Sub000Block068Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19334
    = surrogateDiagTailX0RatChunk001Sub000Block068Part023

theorem surrogateDiagonalTailChunk001Sub000Block068Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block068Part023CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block068Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block068Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block068Part023CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block068Part023SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block068Part023] using hcert

def TailChunk001Sub000Block068Part024SupportExplicit : Finset ℕ :=
  ([19335] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block068Part024 : ℚ :=
  (141799942975 : ℚ) / 575246756921475072

def SurrogateDiagonalTailChunk001Sub000Block068Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19335
    = surrogateDiagTailX0RatChunk001Sub000Block068Part024

theorem surrogateDiagonalTailChunk001Sub000Block068Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block068Part024CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block068Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block068Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block068Part024CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block068Part024SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block068Part024] using hcert

def surrogateDiagonalTailChunk001Sub000Block068HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block068Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block068Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block068Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block068Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block068Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block068Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block068Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block068Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block068Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block068Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block068Head : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block068Part000
    + surrogateDiagTailX0RatChunk001Sub000Block068Part001
    + surrogateDiagTailX0RatChunk001Sub000Block068Part002
    + surrogateDiagTailX0RatChunk001Sub000Block068Part003
    + surrogateDiagTailX0RatChunk001Sub000Block068Part004
    + surrogateDiagTailX0RatChunk001Sub000Block068Part005
    + surrogateDiagTailX0RatChunk001Sub000Block068Part006
    + surrogateDiagTailX0RatChunk001Sub000Block068Part007
    + surrogateDiagTailX0RatChunk001Sub000Block068Part008
    + surrogateDiagTailX0RatChunk001Sub000Block068Part009

def surrogateDiagonalTailChunk001Sub000Block068MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block068Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block068Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block068Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block068Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block068Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block068Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block068Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block068Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block068Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block068Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block068Mid : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block068Part010
    + surrogateDiagTailX0RatChunk001Sub000Block068Part011
    + surrogateDiagTailX0RatChunk001Sub000Block068Part012
    + surrogateDiagTailX0RatChunk001Sub000Block068Part013
    + surrogateDiagTailX0RatChunk001Sub000Block068Part014
    + surrogateDiagTailX0RatChunk001Sub000Block068Part015
    + surrogateDiagTailX0RatChunk001Sub000Block068Part016
    + surrogateDiagTailX0RatChunk001Sub000Block068Part017
    + surrogateDiagTailX0RatChunk001Sub000Block068Part018
    + surrogateDiagTailX0RatChunk001Sub000Block068Part019

def surrogateDiagonalTailChunk001Sub000Block068TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block068Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block068Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block068Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block068Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block068Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block068Tail : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block068Part020
    + surrogateDiagTailX0RatChunk001Sub000Block068Part021
    + surrogateDiagTailX0RatChunk001Sub000Block068Part022
    + surrogateDiagTailX0RatChunk001Sub000Block068Part023
    + surrogateDiagTailX0RatChunk001Sub000Block068Part024

def surrogateDiagonalTailChunk001Sub000Block068Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk001Sub000Block068HeadSum X0
    + surrogateDiagonalTailChunk001Sub000Block068MidSum X0
    + surrogateDiagonalTailChunk001Sub000Block068TailSum X0

def surrogateDiagTailX0RatChunk001Sub000Block068 : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block068Part000
    + surrogateDiagTailX0RatChunk001Sub000Block068Part001
    + surrogateDiagTailX0RatChunk001Sub000Block068Part002
    + surrogateDiagTailX0RatChunk001Sub000Block068Part003
    + surrogateDiagTailX0RatChunk001Sub000Block068Part004
    + surrogateDiagTailX0RatChunk001Sub000Block068Part005
    + surrogateDiagTailX0RatChunk001Sub000Block068Part006
    + surrogateDiagTailX0RatChunk001Sub000Block068Part007
    + surrogateDiagTailX0RatChunk001Sub000Block068Part008
    + surrogateDiagTailX0RatChunk001Sub000Block068Part009
    + surrogateDiagTailX0RatChunk001Sub000Block068Part010
    + surrogateDiagTailX0RatChunk001Sub000Block068Part011
    + surrogateDiagTailX0RatChunk001Sub000Block068Part012
    + surrogateDiagTailX0RatChunk001Sub000Block068Part013
    + surrogateDiagTailX0RatChunk001Sub000Block068Part014
    + surrogateDiagTailX0RatChunk001Sub000Block068Part015
    + surrogateDiagTailX0RatChunk001Sub000Block068Part016
    + surrogateDiagTailX0RatChunk001Sub000Block068Part017
    + surrogateDiagTailX0RatChunk001Sub000Block068Part018
    + surrogateDiagTailX0RatChunk001Sub000Block068Part019
    + surrogateDiagTailX0RatChunk001Sub000Block068Part020
    + surrogateDiagTailX0RatChunk001Sub000Block068Part021
    + surrogateDiagTailX0RatChunk001Sub000Block068Part022
    + surrogateDiagTailX0RatChunk001Sub000Block068Part023
    + surrogateDiagTailX0RatChunk001Sub000Block068Part024

theorem surrogateDiagTailX0RatChunk001Sub000Block068_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk001Sub000Block068Head + surrogateDiagTailX0RatChunk001Sub000Block068Mid + surrogateDiagTailX0RatChunk001Sub000Block068Tail =
      surrogateDiagTailX0RatChunk001Sub000Block068 := by
  unfold surrogateDiagTailX0RatChunk001Sub000Block068Head surrogateDiagTailX0RatChunk001Sub000Block068Mid surrogateDiagTailX0RatChunk001Sub000Block068Tail surrogateDiagTailX0RatChunk001Sub000Block068
  ring

def SurrogateDiagonalTailChunk001Sub000Block068HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block068HeadSum X0 = surrogateDiagTailX0RatChunk001Sub000Block068Head

def SurrogateDiagonalTailChunk001Sub000Block068MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block068MidSum X0 = surrogateDiagTailX0RatChunk001Sub000Block068Mid

def SurrogateDiagonalTailChunk001Sub000Block068TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block068TailSum X0 = surrogateDiagTailX0RatChunk001Sub000Block068Tail

theorem surrogateDiagonalTailChunk001Sub000Block068_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk001Sub000Block068HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk001Sub000Block068MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk001Sub000Block068TailCertificateAt X0) :
    surrogateDiagonalTailChunk001Sub000Block068Sum X0 = surrogateDiagTailX0RatChunk001Sub000Block068 := by
  unfold SurrogateDiagonalTailChunk001Sub000Block068HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk001Sub000Block068MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk001Sub000Block068TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk001Sub000Block068Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk001Sub000Block068_eq_head_add_mid_add_tail

/-- Block 069 covers tail-support indices [11725,11750) and q from 19337 to 19379. -/

def TailChunk001Sub000Block069Part000SupportExplicit : Finset ℕ :=
  ([19337] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block069Part000 : ℚ :=
  (225817191781 : ℚ) / 3231321653567692800

def SurrogateDiagonalTailChunk001Sub000Block069Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19337
    = surrogateDiagTailX0RatChunk001Sub000Block069Part000

theorem surrogateDiagonalTailChunk001Sub000Block069Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block069Part000CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block069Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block069Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block069Part000CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block069Part000SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block069Part000] using hcert

def TailChunk001Sub000Block069Part001SupportExplicit : Finset ℕ :=
  ([19338] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block069Part001 : ℚ :=
  (9212092219 : ℚ) / 11634245897502720

def SurrogateDiagonalTailChunk001Sub000Block069Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19338
    = surrogateDiagTailX0RatChunk001Sub000Block069Part001

theorem surrogateDiagonalTailChunk001Sub000Block069Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block069Part001CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block069Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block069Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block069Part001CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block069Part001SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block069Part001] using hcert

def TailChunk001Sub000Block069Part002SupportExplicit : Finset ℕ :=
  ([19339] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block069Part002 : ℚ :=
  (1419830795125 : ℚ) / 20469829501482682368

def SurrogateDiagonalTailChunk001Sub000Block069Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19339
    = surrogateDiagTailX0RatChunk001Sub000Block069Part002

theorem surrogateDiagonalTailChunk001Sub000Block069Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block069Part002CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block069Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block069Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block069Part002CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block069Part002SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block069Part002] using hcert

def TailChunk001Sub000Block069Part003SupportExplicit : Finset ℕ :=
  ([19342] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block069Part003 : ℚ :=
  (1344342649075 : ℚ) / 4370304899581235712

def SurrogateDiagonalTailChunk001Sub000Block069Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19342
    = surrogateDiagTailX0RatChunk001Sub000Block069Part003

theorem surrogateDiagonalTailChunk001Sub000Block069Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block069Part003CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block069Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block069Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block069Part003CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block069Part003SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block069Part003] using hcert

def TailChunk001Sub000Block069Part004SupportExplicit : Finset ℕ :=
  ([19345] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block069Part004 : ℚ :=
  (14165044760725 : ℚ) / 125779592815614885888

def SurrogateDiagonalTailChunk001Sub000Block069Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19345
    = surrogateDiagTailX0RatChunk001Sub000Block069Part004

theorem surrogateDiagonalTailChunk001Sub000Block069Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block069Part004CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block069Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block069Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block069Part004CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block069Part004SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block069Part004] using hcert

def TailChunk001Sub000Block069Part005SupportExplicit : Finset ℕ :=
  ([19346] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block069Part005 : ℚ :=
  (5329083992725 : ℚ) / 17056901140492320768

def SurrogateDiagonalTailChunk001Sub000Block069Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19346
    = surrogateDiagTailX0RatChunk001Sub000Block069Part005

theorem surrogateDiagonalTailChunk001Sub000Block069Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block069Part005CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block069Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block069Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block069Part005CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block069Part005SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block069Part005] using hcert

def TailChunk001Sub000Block069Part006SupportExplicit : Finset ℕ :=
  ([19347] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block069Part006 : ℚ :=
  (10394800355125 : ℚ) / 69158721598668668928

def SurrogateDiagonalTailChunk001Sub000Block069Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19347
    = surrogateDiagTailX0RatChunk001Sub000Block069Part006

theorem surrogateDiagonalTailChunk001Sub000Block069Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block069Part006CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block069Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block069Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block069Part006CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block069Part006SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block069Part006] using hcert

def TailChunk001Sub000Block069Part007SupportExplicit : Finset ℕ :=
  ([19349] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block069Part007 : ℚ :=
  (49267335589 : ℚ) / 597093509703976200

def SurrogateDiagonalTailChunk001Sub000Block069Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19349
    = surrogateDiagTailX0RatChunk001Sub000Block069Part007

theorem surrogateDiagonalTailChunk001Sub000Block069Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block069Part007CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block069Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block069Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block069Part007CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block069Part007SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block069Part007] using hcert

def TailChunk001Sub000Block069Part008SupportExplicit : Finset ℕ :=
  ([19351] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block069Part008 : ℚ :=
  (22220364564475 : ℚ) / 311830703116043470848

def SurrogateDiagonalTailChunk001Sub000Block069Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19351
    = surrogateDiagTailX0RatChunk001Sub000Block069Part008

theorem surrogateDiagonalTailChunk001Sub000Block069Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block069Part008CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block069Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block069Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block069Part008CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block069Part008SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block069Part008] using hcert

def TailChunk001Sub000Block069Part009SupportExplicit : Finset ℕ :=
  ([19353] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block069Part009 : ℚ :=
  (416049974197 : ℚ) / 2769782655762000000

def SurrogateDiagonalTailChunk001Sub000Block069Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19353
    = surrogateDiagTailX0RatChunk001Sub000Block069Part009

theorem surrogateDiagonalTailChunk001Sub000Block069Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block069Part009CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block069Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block069Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block069Part009CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block069Part009SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block069Part009] using hcert

def TailChunk001Sub000Block069Part010SupportExplicit : Finset ℕ :=
  ([19354] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block069Part010 : ℚ :=
  (1463192640625 : ℚ) / 5479618286391735072

def SurrogateDiagonalTailChunk001Sub000Block069Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19354
    = surrogateDiagTailX0RatChunk001Sub000Block069Part010

theorem surrogateDiagonalTailChunk001Sub000Block069Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block069Part010CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block069Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block069Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block069Part010CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block069Part010SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block069Part010] using hcert

def TailChunk001Sub000Block069Part011SupportExplicit : Finset ℕ :=
  ([19357] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block069Part011 : ℚ :=
  (10174009027925 : ℚ) / 127096494494972903424

def SurrogateDiagonalTailChunk001Sub000Block069Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19357
    = surrogateDiagTailX0RatChunk001Sub000Block069Part011

theorem surrogateDiagonalTailChunk001Sub000Block069Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block069Part011CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block069Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block069Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block069Part011CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block069Part011SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block069Part011] using hcert

def TailChunk001Sub000Block069Part012SupportExplicit : Finset ℕ :=
  ([19358] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block069Part012 : ℚ :=
  (1463797515625 : ℚ) / 5484150173494966482

def SurrogateDiagonalTailChunk001Sub000Block069Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19358
    = surrogateDiagTailX0RatChunk001Sub000Block069Part012

theorem surrogateDiagonalTailChunk001Sub000Block069Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block069Part012CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block069Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block069Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block069Part012CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block069Part012SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block069Part012] using hcert

def TailChunk001Sub000Block069Part013SupportExplicit : Finset ℕ :=
  ([19361] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block069Part013 : ℚ :=
  (21251948012425 : ℚ) / 281908383512843484288

def SurrogateDiagonalTailChunk001Sub000Block069Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19361
    = surrogateDiagTailX0RatChunk001Sub000Block069Part013

theorem surrogateDiagonalTailChunk001Sub000Block069Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block069Part013CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block069Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block069Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block069Part013CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block069Part013SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block069Part013] using hcert

def TailChunk001Sub000Block069Part014SupportExplicit : Finset ℕ :=
  ([19362] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block069Part014 : ℚ :=
  (1942752091 : ℚ) / 1719686972620800

def SurrogateDiagonalTailChunk001Sub000Block069Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19362
    = surrogateDiagTailX0RatChunk001Sub000Block069Part014

theorem surrogateDiagonalTailChunk001Sub000Block069Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block069Part014CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block069Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block069Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block069Part014CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block069Part014SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block069Part014] using hcert

def TailChunk001Sub000Block069Part015SupportExplicit : Finset ℕ :=
  ([19365] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block069Part015 : ℚ :=
  (92930459519 : ℚ) / 378167658600038400

def SurrogateDiagonalTailChunk001Sub000Block069Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19365
    = surrogateDiagTailX0RatChunk001Sub000Block069Part015

theorem surrogateDiagonalTailChunk001Sub000Block069Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block069Part015CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block069Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block069Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block069Part015CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block069Part015SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block069Part015] using hcert

def TailChunk001Sub000Block069Part016SupportExplicit : Finset ℕ :=
  ([19366] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block069Part016 : ℚ :=
  (12144513151 : ℚ) / 40504402492646400

def SurrogateDiagonalTailChunk001Sub000Block069Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19366
    = surrogateDiagTailX0RatChunk001Sub000Block069Part016

theorem surrogateDiagonalTailChunk001Sub000Block069Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block069Part016CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block069Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block069Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block069Part016CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block069Part016SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block069Part016] using hcert

def TailChunk001Sub000Block069Part017SupportExplicit : Finset ℕ :=
  ([19367] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block069Part017 : ℚ :=
  (304562782757 : ℚ) / 4418542910307686400

def SurrogateDiagonalTailChunk001Sub000Block069Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19367
    = surrogateDiagTailX0RatChunk001Sub000Block069Part017

theorem surrogateDiagonalTailChunk001Sub000Block069Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block069Part017CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block069Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block069Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block069Part017CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block069Part017SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block069Part017] using hcert

def TailChunk001Sub000Block069Part018SupportExplicit : Finset ℕ :=
  ([19369] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block069Part018 : ℚ :=
  (17695390596025 : ℚ) / 189688308359433395328

def SurrogateDiagonalTailChunk001Sub000Block069Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19369
    = surrogateDiagTailX0RatChunk001Sub000Block069Part018

theorem surrogateDiagonalTailChunk001Sub000Block069Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block069Part018CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block069Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block069Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block069Part018CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block069Part018SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block069Part018] using hcert

def TailChunk001Sub000Block069Part019SupportExplicit : Finset ℕ :=
  ([19370] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block069Part019 : ℚ :=
  (146368284625 : ℚ) / 265355093445967872

def SurrogateDiagonalTailChunk001Sub000Block069Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19370
    = surrogateDiagTailX0RatChunk001Sub000Block069Part019

theorem surrogateDiagonalTailChunk001Sub000Block069Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block069Part019CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block069Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block069Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block069Part019CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block069Part019SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block069Part019] using hcert

def TailChunk001Sub000Block069Part020SupportExplicit : Finset ℕ :=
  ([19371] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block069Part020 : ℚ :=
  (14818841319 : ℚ) / 78629597985708800

def SurrogateDiagonalTailChunk001Sub000Block069Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19371
    = surrogateDiagTailX0RatChunk001Sub000Block069Part020

theorem surrogateDiagonalTailChunk001Sub000Block069Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block069Part020CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block069Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block069Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block069Part020CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block069Part020SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block069Part020] using hcert

def TailChunk001Sub000Block069Part021SupportExplicit : Finset ℕ :=
  ([19373] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block069Part021 : ℚ :=
  (5864267640625 : ℚ) / 88036893412022982432

def SurrogateDiagonalTailChunk001Sub000Block069Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19373
    = surrogateDiagTailX0RatChunk001Sub000Block069Part021

theorem surrogateDiagonalTailChunk001Sub000Block069Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block069Part021CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block069Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block069Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block069Part021CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block069Part021SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block069Part021] using hcert

def TailChunk001Sub000Block069Part022SupportExplicit : Finset ℕ :=
  ([19374] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block069Part022 : ℚ :=
  (1628695427975 : ℚ) / 2171955635471361024

def SurrogateDiagonalTailChunk001Sub000Block069Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19374
    = surrogateDiagTailX0RatChunk001Sub000Block069Part022

theorem surrogateDiagonalTailChunk001Sub000Block069Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block069Part022CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block069Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block069Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block069Part022CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block069Part022SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block069Part022] using hcert

def TailChunk001Sub000Block069Part023SupportExplicit : Finset ℕ :=
  ([19378] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block069Part023 : ℚ :=
  (1466823765625 : ℚ) / 5506851789336801792

def SurrogateDiagonalTailChunk001Sub000Block069Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19378
    = surrogateDiagTailX0RatChunk001Sub000Block069Part023

theorem surrogateDiagonalTailChunk001Sub000Block069Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block069Part023CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block069Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block069Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block069Part023CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block069Part023SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block069Part023] using hcert

def TailChunk001Sub000Block069Part024SupportExplicit : Finset ℕ :=
  ([19379] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block069Part024 : ℚ :=
  (5867900640625 : ℚ) / 88146013134609833682

def SurrogateDiagonalTailChunk001Sub000Block069Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19379
    = surrogateDiagTailX0RatChunk001Sub000Block069Part024

theorem surrogateDiagonalTailChunk001Sub000Block069Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block069Part024CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block069Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block069Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block069Part024CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block069Part024SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block069Part024] using hcert

def surrogateDiagonalTailChunk001Sub000Block069HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block069Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block069Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block069Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block069Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block069Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block069Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block069Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block069Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block069Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block069Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block069Head : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block069Part000
    + surrogateDiagTailX0RatChunk001Sub000Block069Part001
    + surrogateDiagTailX0RatChunk001Sub000Block069Part002
    + surrogateDiagTailX0RatChunk001Sub000Block069Part003
    + surrogateDiagTailX0RatChunk001Sub000Block069Part004
    + surrogateDiagTailX0RatChunk001Sub000Block069Part005
    + surrogateDiagTailX0RatChunk001Sub000Block069Part006
    + surrogateDiagTailX0RatChunk001Sub000Block069Part007
    + surrogateDiagTailX0RatChunk001Sub000Block069Part008
    + surrogateDiagTailX0RatChunk001Sub000Block069Part009

def surrogateDiagonalTailChunk001Sub000Block069MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block069Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block069Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block069Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block069Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block069Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block069Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block069Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block069Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block069Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block069Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block069Mid : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block069Part010
    + surrogateDiagTailX0RatChunk001Sub000Block069Part011
    + surrogateDiagTailX0RatChunk001Sub000Block069Part012
    + surrogateDiagTailX0RatChunk001Sub000Block069Part013
    + surrogateDiagTailX0RatChunk001Sub000Block069Part014
    + surrogateDiagTailX0RatChunk001Sub000Block069Part015
    + surrogateDiagTailX0RatChunk001Sub000Block069Part016
    + surrogateDiagTailX0RatChunk001Sub000Block069Part017
    + surrogateDiagTailX0RatChunk001Sub000Block069Part018
    + surrogateDiagTailX0RatChunk001Sub000Block069Part019

def surrogateDiagonalTailChunk001Sub000Block069TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block069Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block069Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block069Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block069Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block069Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block069Tail : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block069Part020
    + surrogateDiagTailX0RatChunk001Sub000Block069Part021
    + surrogateDiagTailX0RatChunk001Sub000Block069Part022
    + surrogateDiagTailX0RatChunk001Sub000Block069Part023
    + surrogateDiagTailX0RatChunk001Sub000Block069Part024

def surrogateDiagonalTailChunk001Sub000Block069Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk001Sub000Block069HeadSum X0
    + surrogateDiagonalTailChunk001Sub000Block069MidSum X0
    + surrogateDiagonalTailChunk001Sub000Block069TailSum X0

def surrogateDiagTailX0RatChunk001Sub000Block069 : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block069Part000
    + surrogateDiagTailX0RatChunk001Sub000Block069Part001
    + surrogateDiagTailX0RatChunk001Sub000Block069Part002
    + surrogateDiagTailX0RatChunk001Sub000Block069Part003
    + surrogateDiagTailX0RatChunk001Sub000Block069Part004
    + surrogateDiagTailX0RatChunk001Sub000Block069Part005
    + surrogateDiagTailX0RatChunk001Sub000Block069Part006
    + surrogateDiagTailX0RatChunk001Sub000Block069Part007
    + surrogateDiagTailX0RatChunk001Sub000Block069Part008
    + surrogateDiagTailX0RatChunk001Sub000Block069Part009
    + surrogateDiagTailX0RatChunk001Sub000Block069Part010
    + surrogateDiagTailX0RatChunk001Sub000Block069Part011
    + surrogateDiagTailX0RatChunk001Sub000Block069Part012
    + surrogateDiagTailX0RatChunk001Sub000Block069Part013
    + surrogateDiagTailX0RatChunk001Sub000Block069Part014
    + surrogateDiagTailX0RatChunk001Sub000Block069Part015
    + surrogateDiagTailX0RatChunk001Sub000Block069Part016
    + surrogateDiagTailX0RatChunk001Sub000Block069Part017
    + surrogateDiagTailX0RatChunk001Sub000Block069Part018
    + surrogateDiagTailX0RatChunk001Sub000Block069Part019
    + surrogateDiagTailX0RatChunk001Sub000Block069Part020
    + surrogateDiagTailX0RatChunk001Sub000Block069Part021
    + surrogateDiagTailX0RatChunk001Sub000Block069Part022
    + surrogateDiagTailX0RatChunk001Sub000Block069Part023
    + surrogateDiagTailX0RatChunk001Sub000Block069Part024

theorem surrogateDiagTailX0RatChunk001Sub000Block069_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk001Sub000Block069Head + surrogateDiagTailX0RatChunk001Sub000Block069Mid + surrogateDiagTailX0RatChunk001Sub000Block069Tail =
      surrogateDiagTailX0RatChunk001Sub000Block069 := by
  unfold surrogateDiagTailX0RatChunk001Sub000Block069Head surrogateDiagTailX0RatChunk001Sub000Block069Mid surrogateDiagTailX0RatChunk001Sub000Block069Tail surrogateDiagTailX0RatChunk001Sub000Block069
  ring

def SurrogateDiagonalTailChunk001Sub000Block069HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block069HeadSum X0 = surrogateDiagTailX0RatChunk001Sub000Block069Head

def SurrogateDiagonalTailChunk001Sub000Block069MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block069MidSum X0 = surrogateDiagTailX0RatChunk001Sub000Block069Mid

def SurrogateDiagonalTailChunk001Sub000Block069TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block069TailSum X0 = surrogateDiagTailX0RatChunk001Sub000Block069Tail

theorem surrogateDiagonalTailChunk001Sub000Block069_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk001Sub000Block069HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk001Sub000Block069MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk001Sub000Block069TailCertificateAt X0) :
    surrogateDiagonalTailChunk001Sub000Block069Sum X0 = surrogateDiagTailX0RatChunk001Sub000Block069 := by
  unfold SurrogateDiagonalTailChunk001Sub000Block069HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk001Sub000Block069MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk001Sub000Block069TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk001Sub000Block069Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk001Sub000Block069_eq_head_add_mid_add_tail

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

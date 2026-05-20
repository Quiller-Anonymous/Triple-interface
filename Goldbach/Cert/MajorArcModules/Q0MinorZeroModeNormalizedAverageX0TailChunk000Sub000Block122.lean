import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0TailPilot25

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

open scoped BigOperators

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

/- Generated direct-term certificate blocks for tail chunk 000, subchunk 000, blocks [122,123). -/

/- Block 122 covers tail-support indices [3050,3075) and q from 5071 to 5110. -/

def TailChunk000Sub000Block122Part000SupportExplicit : Finset ℕ :=
  ([5071] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block122Part000 : ℚ :=
  (729081287 : ℚ) / 559793936400000

def SurrogateDiagonalTailChunk000Sub000Block122Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5071
    = surrogateDiagTailX0RatChunk000Sub000Block122Part000

theorem surrogateDiagonalTailChunk000Sub000Block122Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block122Part000CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block122Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block122Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block122Part000CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block122Part000SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block122Part000] using hcert

def TailChunk000Sub000Block122Part001SupportExplicit : Finset ℕ :=
  ([5073] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block122Part001 : ℚ :=
  (1004504543725 : ℚ) / 251864843341529088

def SurrogateDiagonalTailChunk000Sub000Block122Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5073
    = surrogateDiagTailX0RatChunk000Sub000Block122Part001

theorem surrogateDiagonalTailChunk000Sub000Block122Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block122Part001CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block122Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block122Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block122Part001CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block122Part001SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block122Part001] using hcert

def TailChunk000Sub000Block122Part002SupportExplicit : Finset ℕ :=
  ([5074] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block122Part002 : ℚ :=
  (193086497575 : ℚ) / 22012836272677152

def SurrogateDiagonalTailChunk000Sub000Block122Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5074
    = surrogateDiagTailX0RatChunk000Sub000Block122Part002

theorem surrogateDiagonalTailChunk000Sub000Block122Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block122Part002CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block122Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block122Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block122Part002CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block122Part002SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block122Part002] using hcert

def TailChunk000Sub000Block122Part003SupportExplicit : Finset ℕ :=
  ([5077] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block122Part003 : ℚ :=
  (402748890625 : ℚ) / 415004992452970272

def SurrogateDiagonalTailChunk000Sub000Block122Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5077
    = surrogateDiagTailX0RatChunk000Sub000Block122Part003

theorem surrogateDiagonalTailChunk000Sub000Block122Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block122Part003CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block122Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block122Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block122Part003CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block122Part003SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block122Part003] using hcert

def TailChunk000Sub000Block122Part004SupportExplicit : Finset ℕ :=
  ([5078] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block122Part004 : ℚ :=
  (805653961975 : ℚ) / 103751248113242568

def SurrogateDiagonalTailChunk000Sub000Block122Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5078
    = surrogateDiagTailX0RatChunk000Sub000Block122Part004

theorem surrogateDiagonalTailChunk000Sub000Block122Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block122Part004CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block122Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block122Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block122Part004CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block122Part004SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block122Part004] using hcert

def TailChunk000Sub000Block122Part005SupportExplicit : Finset ℕ :=
  ([5079] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block122Part005 : ℚ :=
  (35806625 : ℚ) / 10927987043328

def SurrogateDiagonalTailChunk000Sub000Block122Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5079
    = surrogateDiagTailX0RatChunk000Sub000Block122Part005

theorem surrogateDiagonalTailChunk000Sub000Block122Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block122Part005CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block122Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block122Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block122Part005CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block122Part005SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block122Part005] using hcert

def TailChunk000Sub000Block122Part006SupportExplicit : Finset ℕ :=
  ([5081] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block122Part006 : ℚ :=
  (645414025 : ℚ) / 666103475016192

def SurrogateDiagonalTailChunk000Sub000Block122Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5081
    = surrogateDiagTailX0RatChunk000Sub000Block122Part006

theorem surrogateDiagonalTailChunk000Sub000Block122Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block122Part006CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block122Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block122Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block122Part006CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block122Part006SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block122Part006] using hcert

def TailChunk000Sub000Block122Part007SupportExplicit : Finset ℕ :=
  ([5083] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block122Part007 : ℚ :=
  (222933878125 : ℚ) / 132669547109941248

def SurrogateDiagonalTailChunk000Sub000Block122Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5083
    = surrogateDiagTailX0RatChunk000Sub000Block122Part007

theorem surrogateDiagonalTailChunk000Sub000Block122Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block122Part007CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block122Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block122Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block122Part007CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block122Part007SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block122Part007] using hcert

def TailChunk000Sub000Block122Part008SupportExplicit : Finset ℕ :=
  ([5086] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block122Part008 : ℚ :=
  (808194453775 : ℚ) / 104406862176235848

def SurrogateDiagonalTailChunk000Sub000Block122Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5086
    = surrogateDiagTailX0RatChunk000Sub000Block122Part008

theorem surrogateDiagonalTailChunk000Sub000Block122Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block122Part008CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block122Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block122Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block122Part008CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block122Part008SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block122Part008] using hcert

def TailChunk000Sub000Block122Part009SupportExplicit : Finset ℕ :=
  ([5087] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block122Part009 : ℚ :=
  (404337015625 : ℚ) / 418285000159987602

def SurrogateDiagonalTailChunk000Sub000Block122Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5087
    = surrogateDiagTailX0RatChunk000Sub000Block122Part009

theorem surrogateDiagonalTailChunk000Sub000Block122Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block122Part009CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block122Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block122Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block122Part009CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block122Part009SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block122Part009] using hcert

def TailChunk000Sub000Block122Part010SupportExplicit : Finset ℕ :=
  ([5089] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block122Part010 : ℚ :=
  (25661544475 : ℚ) / 16671880295877312

def SurrogateDiagonalTailChunk000Sub000Block122Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5089
    = surrogateDiagTailX0RatChunk000Sub000Block122Part010

theorem surrogateDiagonalTailChunk000Sub000Block122Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block122Part010CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block122Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block122Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block122Part010CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block122Part010SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block122Part010] using hcert

def TailChunk000Sub000Block122Part011SupportExplicit : Finset ℕ :=
  ([5090] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block122Part011 : ℚ :=
  (161634445375 : ℚ) / 10657655600259072

def SurrogateDiagonalTailChunk000Sub000Block122Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5090
    = surrogateDiagTailX0RatChunk000Sub000Block122Part011

theorem surrogateDiagonalTailChunk000Sub000Block122Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block122Part011CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block122Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block122Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block122Part011CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block122Part011SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block122Part011] using hcert

def TailChunk000Sub000Block122Part012SupportExplicit : Finset ℕ :=
  ([5091] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block122Part012 : ℚ :=
  (107928075 : ℚ) / 33095076020224

def SurrogateDiagonalTailChunk000Sub000Block122Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5091
    = surrogateDiagTailX0RatChunk000Sub000Block122Part012

theorem surrogateDiagonalTailChunk000Sub000Block122Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block122Part012CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block122Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block122Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block122Part012CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block122Part012SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block122Part012] using hcert

def TailChunk000Sub000Block122Part013SupportExplicit : Finset ℕ :=
  ([5093] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block122Part013 : ℚ :=
  (267425929 : ℚ) / 207124785473760

def SurrogateDiagonalTailChunk000Sub000Block122Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5093
    = surrogateDiagTailX0RatChunk000Sub000Block122Part013

theorem surrogateDiagonalTailChunk000Sub000Block122Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block122Part013CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block122Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block122Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block122Part013CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block122Part013SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block122Part013] using hcert

def TailChunk000Sub000Block122Part014SupportExplicit : Finset ℕ :=
  ([5095] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block122Part014 : ℚ :=
  (648457040375 : ℚ) / 343738312468030464

def SurrogateDiagonalTailChunk000Sub000Block122Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5095
    = surrogateDiagTailX0RatChunk000Sub000Block122Part014

theorem surrogateDiagonalTailChunk000Sub000Block122Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block122Part014CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block122Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block122Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block122Part014CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block122Part014SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block122Part014] using hcert

def TailChunk000Sub000Block122Part015SupportExplicit : Finset ℕ :=
  ([5097] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block122Part015 : ℚ :=
  (36060875 : ℚ) / 11083820407488

def SurrogateDiagonalTailChunk000Sub000Block122Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5097
    = surrogateDiagTailX0RatChunk000Sub000Block122Part015

theorem surrogateDiagonalTailChunk000Sub000Block122Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block122Part015CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block122Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block122Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block122Part015CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block122Part015SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block122Part015] using hcert

def TailChunk000Sub000Block122Part016SupportExplicit : Finset ℕ :=
  ([5098] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block122Part016 : ℚ :=
  (812012689975 : ℚ) / 105396103076654208

def SurrogateDiagonalTailChunk000Sub000Block122Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5098
    = surrogateDiagTailX0RatChunk000Sub000Block122Part016

theorem surrogateDiagonalTailChunk000Sub000Block122Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block122Part016CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block122Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block122Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block122Part016CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block122Part016SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block122Part016] using hcert

def TailChunk000Sub000Block122Part017SupportExplicit : Finset ℕ :=
  ([5099] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block122Part017 : ℚ :=
  (406246890625 : ℚ) / 422246629987519602

def SurrogateDiagonalTailChunk000Sub000Block122Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5099
    = surrogateDiagTailX0RatChunk000Sub000Block122Part017

theorem surrogateDiagonalTailChunk000Sub000Block122Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block122Part017CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block122Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block122Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block122Part017CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block122Part017SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block122Part017] using hcert

def TailChunk000Sub000Block122Part018SupportExplicit : Finset ℕ :=
  ([5101] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block122Part018 : ℚ :=
  (26020201 : ℚ) / 27066216160800

def SurrogateDiagonalTailChunk000Sub000Block122Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5101
    = surrogateDiagTailX0RatChunk000Sub000Block122Part018

theorem surrogateDiagonalTailChunk000Sub000Block122Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block122Part018CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block122Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block122Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block122Part018CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block122Part018SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block122Part018] using hcert

def TailChunk000Sub000Block122Part019SupportExplicit : Finset ℕ :=
  ([5102] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block122Part019 : ℚ :=
  (6507601 : ℚ) / 1691638510050

def SurrogateDiagonalTailChunk000Sub000Block122Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5102
    = surrogateDiagTailX0RatChunk000Sub000Block122Part019

theorem surrogateDiagonalTailChunk000Sub000Block122Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block122Part019CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block122Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block122Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block122Part019CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block122Part019SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block122Part019] using hcert

def TailChunk000Sub000Block122Part020SupportExplicit : Finset ℕ :=
  ([5105] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block122Part020 : ℚ :=
  (5208040399 : ℚ) / 2771580534865920

def SurrogateDiagonalTailChunk000Sub000Block122Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5105
    = surrogateDiagTailX0RatChunk000Sub000Block122Part020

theorem surrogateDiagonalTailChunk000Sub000Block122Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block122Part020CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block122Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block122Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block122Part020CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block122Part020SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block122Part020] using hcert

def TailChunk000Sub000Block122Part021SupportExplicit : Finset ℕ :=
  ([5106] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block122Part021 : ℚ :=
  (504764113525 : ℚ) / 15741552708845568

def SurrogateDiagonalTailChunk000Sub000Block122Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5106
    = surrogateDiagTailX0RatChunk000Sub000Block122Part021

theorem surrogateDiagonalTailChunk000Sub000Block122Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block122Part021CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block122Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block122Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block122Part021CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block122Part021SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block122Part021] using hcert

def TailChunk000Sub000Block122Part022SupportExplicit : Finset ℕ :=
  ([5107] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block122Part022 : ℚ :=
  (407522640625 : ℚ) / 424903305273130962

def SurrogateDiagonalTailChunk000Sub000Block122Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5107
    = surrogateDiagTailX0RatChunk000Sub000Block122Part022

theorem surrogateDiagonalTailChunk000Sub000Block122Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block122Part022CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block122Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block122Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block122Part022CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block122Part022SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block122Part022] using hcert

def TailChunk000Sub000Block122Part023SupportExplicit : Finset ℕ :=
  ([5109] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block122Part023 : ℚ :=
  (19841244803 : ℚ) / 4738874753433600

def SurrogateDiagonalTailChunk000Sub000Block122Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5109
    = surrogateDiagTailX0RatChunk000Sub000Block122Part023

theorem surrogateDiagonalTailChunk000Sub000Block122Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block122Part023CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block122Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block122Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block122Part023CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block122Part023SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block122Part023] using hcert

def TailChunk000Sub000Block122Part024SupportExplicit : Finset ℕ :=
  ([5110] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block122Part024 : ℚ :=
  (551182124425 : ℚ) / 22294709170864128

def SurrogateDiagonalTailChunk000Sub000Block122Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5110
    = surrogateDiagTailX0RatChunk000Sub000Block122Part024

theorem surrogateDiagonalTailChunk000Sub000Block122Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block122Part024CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block122Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block122Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block122Part024CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block122Part024SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block122Part024] using hcert

def surrogateDiagonalTailChunk000Sub000Block122HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block122Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block122Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block122Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block122Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block122Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block122Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block122Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block122Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block122Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block122Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block122Head : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block122Part000
    + surrogateDiagTailX0RatChunk000Sub000Block122Part001
    + surrogateDiagTailX0RatChunk000Sub000Block122Part002
    + surrogateDiagTailX0RatChunk000Sub000Block122Part003
    + surrogateDiagTailX0RatChunk000Sub000Block122Part004
    + surrogateDiagTailX0RatChunk000Sub000Block122Part005
    + surrogateDiagTailX0RatChunk000Sub000Block122Part006
    + surrogateDiagTailX0RatChunk000Sub000Block122Part007
    + surrogateDiagTailX0RatChunk000Sub000Block122Part008
    + surrogateDiagTailX0RatChunk000Sub000Block122Part009

def surrogateDiagonalTailChunk000Sub000Block122MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block122Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block122Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block122Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block122Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block122Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block122Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block122Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block122Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block122Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block122Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block122Mid : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block122Part010
    + surrogateDiagTailX0RatChunk000Sub000Block122Part011
    + surrogateDiagTailX0RatChunk000Sub000Block122Part012
    + surrogateDiagTailX0RatChunk000Sub000Block122Part013
    + surrogateDiagTailX0RatChunk000Sub000Block122Part014
    + surrogateDiagTailX0RatChunk000Sub000Block122Part015
    + surrogateDiagTailX0RatChunk000Sub000Block122Part016
    + surrogateDiagTailX0RatChunk000Sub000Block122Part017
    + surrogateDiagTailX0RatChunk000Sub000Block122Part018
    + surrogateDiagTailX0RatChunk000Sub000Block122Part019

def surrogateDiagonalTailChunk000Sub000Block122TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block122Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block122Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block122Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block122Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block122Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block122Tail : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block122Part020
    + surrogateDiagTailX0RatChunk000Sub000Block122Part021
    + surrogateDiagTailX0RatChunk000Sub000Block122Part022
    + surrogateDiagTailX0RatChunk000Sub000Block122Part023
    + surrogateDiagTailX0RatChunk000Sub000Block122Part024

def surrogateDiagonalTailChunk000Sub000Block122Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub000Block122HeadSum X0
    + surrogateDiagonalTailChunk000Sub000Block122MidSum X0
    + surrogateDiagonalTailChunk000Sub000Block122TailSum X0

def surrogateDiagTailX0RatChunk000Sub000Block122 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block122Part000
    + surrogateDiagTailX0RatChunk000Sub000Block122Part001
    + surrogateDiagTailX0RatChunk000Sub000Block122Part002
    + surrogateDiagTailX0RatChunk000Sub000Block122Part003
    + surrogateDiagTailX0RatChunk000Sub000Block122Part004
    + surrogateDiagTailX0RatChunk000Sub000Block122Part005
    + surrogateDiagTailX0RatChunk000Sub000Block122Part006
    + surrogateDiagTailX0RatChunk000Sub000Block122Part007
    + surrogateDiagTailX0RatChunk000Sub000Block122Part008
    + surrogateDiagTailX0RatChunk000Sub000Block122Part009
    + surrogateDiagTailX0RatChunk000Sub000Block122Part010
    + surrogateDiagTailX0RatChunk000Sub000Block122Part011
    + surrogateDiagTailX0RatChunk000Sub000Block122Part012
    + surrogateDiagTailX0RatChunk000Sub000Block122Part013
    + surrogateDiagTailX0RatChunk000Sub000Block122Part014
    + surrogateDiagTailX0RatChunk000Sub000Block122Part015
    + surrogateDiagTailX0RatChunk000Sub000Block122Part016
    + surrogateDiagTailX0RatChunk000Sub000Block122Part017
    + surrogateDiagTailX0RatChunk000Sub000Block122Part018
    + surrogateDiagTailX0RatChunk000Sub000Block122Part019
    + surrogateDiagTailX0RatChunk000Sub000Block122Part020
    + surrogateDiagTailX0RatChunk000Sub000Block122Part021
    + surrogateDiagTailX0RatChunk000Sub000Block122Part022
    + surrogateDiagTailX0RatChunk000Sub000Block122Part023
    + surrogateDiagTailX0RatChunk000Sub000Block122Part024

theorem surrogateDiagTailX0RatChunk000Sub000Block122_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk000Sub000Block122Head + surrogateDiagTailX0RatChunk000Sub000Block122Mid + surrogateDiagTailX0RatChunk000Sub000Block122Tail =
      surrogateDiagTailX0RatChunk000Sub000Block122 := by
  unfold surrogateDiagTailX0RatChunk000Sub000Block122Head surrogateDiagTailX0RatChunk000Sub000Block122Mid surrogateDiagTailX0RatChunk000Sub000Block122Tail surrogateDiagTailX0RatChunk000Sub000Block122
  ring

def SurrogateDiagonalTailChunk000Sub000Block122HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block122HeadSum X0 = surrogateDiagTailX0RatChunk000Sub000Block122Head

def SurrogateDiagonalTailChunk000Sub000Block122MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block122MidSum X0 = surrogateDiagTailX0RatChunk000Sub000Block122Mid

def SurrogateDiagonalTailChunk000Sub000Block122TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block122TailSum X0 = surrogateDiagTailX0RatChunk000Sub000Block122Tail

theorem surrogateDiagonalTailChunk000Sub000Block122_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk000Sub000Block122HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk000Sub000Block122MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk000Sub000Block122TailCertificateAt X0) :
    surrogateDiagonalTailChunk000Sub000Block122Sum X0 = surrogateDiagTailX0RatChunk000Sub000Block122 := by
  unfold SurrogateDiagonalTailChunk000Sub000Block122HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk000Sub000Block122MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk000Sub000Block122TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk000Sub000Block122Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk000Sub000Block122_eq_head_add_mid_add_tail

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

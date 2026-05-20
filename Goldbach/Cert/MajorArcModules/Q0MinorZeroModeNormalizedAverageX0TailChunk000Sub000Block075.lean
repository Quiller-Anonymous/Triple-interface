import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0TailPilot25

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

open scoped BigOperators

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

/- Generated direct-term certificate blocks for tail chunk 000, subchunk 000, blocks [75,76). -/

/- Block 075 covers tail-support indices [1875,1900) and q from 3131 to 3169. -/

def TailChunk000Sub000Block075Part000SupportExplicit : Finset ℕ :=
  ([3131] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block075Part000 : ℚ :=
  (5822287163 : ℚ) / 1012702500000000

def SurrogateDiagonalTailChunk000Sub000Block075Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3131
    = surrogateDiagTailX0RatChunk000Sub000Block075Part000

theorem surrogateDiagonalTailChunk000Sub000Block075Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block075Part000CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block075Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block075Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block075Part000CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block075Part000SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block075Part000] using hcert

def TailChunk000Sub000Block075Part001SupportExplicit : Finset ℕ :=
  ([3133] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block075Part001 : ℚ :=
  (22182761387 : ℚ) / 3440541538713600

def SurrogateDiagonalTailChunk000Sub000Block075Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3133
    = surrogateDiagTailX0RatChunk000Sub000Block075Part001

theorem surrogateDiagonalTailChunk000Sub000Block075Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block075Part001CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block075Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block075Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block075Part001CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block075Part001SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block075Part001] using hcert

def TailChunk000Sub000Block075Part002SupportExplicit : Finset ℕ :=
  ([3134] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block075Part002 : ℚ :=
  (51135558425 : ℚ) / 1670903544646152

def SurrogateDiagonalTailChunk000Sub000Block075Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3134
    = surrogateDiagTailX0RatChunk000Sub000Block075Part002

theorem surrogateDiagonalTailChunk000Sub000Block075Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block075Part002CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block075Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block075Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block075Part002CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block075Part002SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block075Part002] using hcert

def TailChunk000Sub000Block075Part003SupportExplicit : Finset ℕ :=
  ([3135] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block075Part003 : ℚ :=
  (3283589009 : ℚ) / 71677948723200

def SurrogateDiagonalTailChunk000Sub000Block075Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3135
    = surrogateDiagTailX0RatChunk000Sub000Block075Part003

theorem surrogateDiagonalTailChunk000Sub000Block075Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block075Part003CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block075Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block075Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block075Part003CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block075Part003SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block075Part003] using hcert

def TailChunk000Sub000Block075Part004SupportExplicit : Finset ℕ :=
  ([3137] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block075Part004 : ℚ :=
  (153762015625 : ℚ) / 60460409397706752

def SurrogateDiagonalTailChunk000Sub000Block075Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3137
    = surrogateDiagTailX0RatChunk000Sub000Block075Part004

theorem surrogateDiagonalTailChunk000Sub000Block075Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block075Part004CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block075Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block075Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block075Part004CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block075Part004SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block075Part004] using hcert

def TailChunk000Sub000Block075Part005SupportExplicit : Finset ℕ :=
  ([3138] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block075Part005 : ℚ :=
  (5119475 : ℚ) / 49498353504

def SurrogateDiagonalTailChunk000Sub000Block075Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3138
    = surrogateDiagTailX0RatChunk000Sub000Block075Part005

theorem surrogateDiagonalTailChunk000Sub000Block075Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block075Part005CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block075Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block075Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block075Part005CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block075Part005SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block075Part005] using hcert

def TailChunk000Sub000Block075Part006SupportExplicit : Finset ℕ :=
  ([3139] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block075Part006 : ℚ :=
  (151603079125 : ℚ) / 52274996796137472

def SurrogateDiagonalTailChunk000Sub000Block075Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3139
    = surrogateDiagTailX0RatChunk000Sub000Block075Part006

theorem surrogateDiagonalTailChunk000Sub000Block075Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block075Part006CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block075Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block075Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block075Part006CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block075Part006SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block075Part006] using hcert

def TailChunk000Sub000Block075Part007SupportExplicit : Finset ℕ :=
  ([3142] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block075Part007 : ℚ :=
  (6167634459 : ℚ) / 202564905213400

def SurrogateDiagonalTailChunk000Sub000Block075Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3142
    = surrogateDiagTailX0RatChunk000Sub000Block075Part007

theorem surrogateDiagonalTailChunk000Sub000Block075Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block075Part007CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block075Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block075Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block075Part007CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block075Part007SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block075Part007] using hcert

def TailChunk000Sub000Block075Part008SupportExplicit : Finset ℕ :=
  ([3143] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block075Part008 : ℚ :=
  (18092848625 : ℚ) / 4079377893556224

def SurrogateDiagonalTailChunk000Sub000Block075Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3143
    = surrogateDiagTailX0RatChunk000Sub000Block075Part008

theorem surrogateDiagonalTailChunk000Sub000Block075Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block075Part008CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block075Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block075Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block075Part008CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block075Part008SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block075Part008] using hcert

def TailChunk000Sub000Block075Part009SupportExplicit : Finset ℕ :=
  ([3145] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block075Part009 : ℚ :=
  (94242463175 : ℚ) / 7829143412539392

def SurrogateDiagonalTailChunk000Sub000Block075Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3145
    = surrogateDiagTailX0RatChunk000Sub000Block075Part009

theorem surrogateDiagonalTailChunk000Sub000Block075Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block075Part009CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block075Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block075Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block075Part009CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block075Part009SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block075Part009] using hcert

def TailChunk000Sub000Block075Part010SupportExplicit : Finset ℕ :=
  ([3147] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block075Part010 : ℚ :=
  (755845824175 : ℚ) / 48260517230051328

def SurrogateDiagonalTailChunk000Sub000Block075Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3147
    = surrogateDiagTailX0RatChunk000Sub000Block075Part010

theorem surrogateDiagonalTailChunk000Sub000Block075Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block075Part010CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block075Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block075Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block075Part010CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block075Part010SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block075Part010] using hcert

def TailChunk000Sub000Block075Part011SupportExplicit : Finset ℕ :=
  ([3149] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block075Part011 : ℚ :=
  (107846179775 : ℚ) / 19312622104710528

def SurrogateDiagonalTailChunk000Sub000Block075Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3149
    = surrogateDiagTailX0RatChunk000Sub000Block075Part011

theorem surrogateDiagonalTailChunk000Sub000Block075Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block075Part011CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block075Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block075Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block075Part011CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block075Part011SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block075Part011] using hcert

def TailChunk000Sub000Block075Part012SupportExplicit : Finset ℕ :=
  ([3151] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block075Part012 : ℚ :=
  (291620625775 : ℚ) / 50097173593792512

def SurrogateDiagonalTailChunk000Sub000Block075Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3151
    = surrogateDiagTailX0RatChunk000Sub000Block075Part012

theorem surrogateDiagonalTailChunk000Sub000Block075Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block075Part012CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block075Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block075Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block075Part012CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block075Part012SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block075Part012] using hcert

def TailChunk000Sub000Block075Part013SupportExplicit : Finset ℕ :=
  ([3153] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block075Part013 : ℚ :=
  (6069848789 : ℚ) / 389039792400000

def SurrogateDiagonalTailChunk000Sub000Block075Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3153
    = surrogateDiagTailX0RatChunk000Sub000Block075Part013

theorem surrogateDiagonalTailChunk000Sub000Block075Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block075Part013CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block075Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block075Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block075Part013CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block075Part013SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block075Part013] using hcert

def TailChunk000Sub000Block075Part014SupportExplicit : Finset ℕ :=
  ([3154] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block075Part014 : ℚ :=
  (219040830575 : ℚ) / 5933928283066944

def SurrogateDiagonalTailChunk000Sub000Block075Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3154
    = surrogateDiagTailX0RatChunk000Sub000Block075Part014

theorem surrogateDiagonalTailChunk000Sub000Block075Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block075Part014CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block075Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block075Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block075Part014CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block075Part014SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block075Part014] using hcert

def TailChunk000Sub000Block075Part015SupportExplicit : Finset ℕ :=
  ([3155] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block075Part015 : ℚ :=
  (37762204807 : ℚ) / 4033564567603200

def SurrogateDiagonalTailChunk000Sub000Block075Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3155
    = surrogateDiagTailX0RatChunk000Sub000Block075Part015

theorem surrogateDiagonalTailChunk000Sub000Block075Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block075Part015CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block075Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block075Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block075Part015CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block075Part015SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block075Part015] using hcert

def TailChunk000Sub000Block075Part016SupportExplicit : Finset ℕ :=
  ([3157] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block075Part016 : ℚ :=
  (21824421367 : ℚ) / 3318423552000000

def SurrogateDiagonalTailChunk000Sub000Block075Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3157
    = surrogateDiagTailX0RatChunk000Sub000Block075Part016

theorem surrogateDiagonalTailChunk000Sub000Block075Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block075Part016CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block075Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block075Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block075Part016CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block075Part016SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block075Part016] using hcert

def TailChunk000Sub000Block075Part017SupportExplicit : Finset ℕ :=
  ([3158] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block075Part017 : ℚ :=
  (51921743825 : ℚ) / 1722710675200392

def SurrogateDiagonalTailChunk000Sub000Block075Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3158
    = surrogateDiagTailX0RatChunk000Sub000Block075Part017

theorem surrogateDiagonalTailChunk000Sub000Block075Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block075Part017CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block075Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block075Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block075Part017CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block075Part017SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block075Part017] using hcert

def TailChunk000Sub000Block075Part018SupportExplicit : Finset ℕ :=
  ([3161] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block075Part018 : ℚ :=
  (76637410475 : ℚ) / 26137498398068736

def SurrogateDiagonalTailChunk000Sub000Block075Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3161
    = surrogateDiagTailX0RatChunk000Sub000Block075Part018

theorem surrogateDiagonalTailChunk000Sub000Block075Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block075Part018CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block075Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block075Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block075Part018CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block075Part018SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block075Part018] using hcert

def TailChunk000Sub000Block075Part019SupportExplicit : Finset ℕ :=
  ([3162] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block075Part019 : ℚ :=
  (801145487 : ℚ) / 5663442862080

def SurrogateDiagonalTailChunk000Sub000Block075Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3162
    = surrogateDiagTailX0RatChunk000Sub000Block075Part019

theorem surrogateDiagonalTailChunk000Sub000Block075Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block075Part019CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block075Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block075Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block075Part019CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block075Part019SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block075Part019] using hcert

def TailChunk000Sub000Block075Part020SupportExplicit : Finset ℕ :=
  ([3163] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block075Part020 : ℚ :=
  (156321390625 : ℚ) / 62490547537595442

def SurrogateDiagonalTailChunk000Sub000Block075Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3163
    = surrogateDiagTailX0RatChunk000Sub000Block075Part020

theorem surrogateDiagonalTailChunk000Sub000Block075Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block075Part020CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block075Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block075Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block075Part020CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block075Part020SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block075Part020] using hcert

def TailChunk000Sub000Block075Part021SupportExplicit : Finset ℕ :=
  ([3165] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block075Part021 : ℚ :=
  (655190887 : ℚ) / 22132041523200

def SurrogateDiagonalTailChunk000Sub000Block075Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3165
    = surrogateDiagTailX0RatChunk000Sub000Block075Part021

theorem surrogateDiagonalTailChunk000Sub000Block075Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block075Part021CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block075Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block075Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block075Part021CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block075Part021SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block075Part021] using hcert

def TailChunk000Sub000Block075Part022SupportExplicit : Finset ℕ :=
  ([3166] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block075Part022 : ℚ :=
  (313048183325 : ℚ) / 7831100182075044

def SurrogateDiagonalTailChunk000Sub000Block075Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3166
    = surrogateDiagTailX0RatChunk000Sub000Block075Part022

theorem surrogateDiagonalTailChunk000Sub000Block075Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block075Part022CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block075Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block075Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block075Part022CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block075Part022SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block075Part022] using hcert

def TailChunk000Sub000Block075Part023SupportExplicit : Finset ℕ :=
  ([3167] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block075Part023 : ℚ :=
  (1253485377775 : ℚ) / 251229423050282568

def SurrogateDiagonalTailChunk000Sub000Block075Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3167
    = surrogateDiagTailX0RatChunk000Sub000Block075Part023

theorem surrogateDiagonalTailChunk000Sub000Block075Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block075Part023CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block075Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block075Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block075Part023CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block075Part023SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block075Part023] using hcert

def TailChunk000Sub000Block075Part024SupportExplicit : Finset ℕ :=
  ([3169] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block075Part024 : ℚ :=
  (1255069060975 : ℚ) / 251864843341529088

def SurrogateDiagonalTailChunk000Sub000Block075Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3169
    = surrogateDiagTailX0RatChunk000Sub000Block075Part024

theorem surrogateDiagonalTailChunk000Sub000Block075Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block075Part024CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block075Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block075Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block075Part024CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block075Part024SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block075Part024] using hcert

def surrogateDiagonalTailChunk000Sub000Block075HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block075Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block075Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block075Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block075Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block075Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block075Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block075Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block075Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block075Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block075Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block075Head : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block075Part000
    + surrogateDiagTailX0RatChunk000Sub000Block075Part001
    + surrogateDiagTailX0RatChunk000Sub000Block075Part002
    + surrogateDiagTailX0RatChunk000Sub000Block075Part003
    + surrogateDiagTailX0RatChunk000Sub000Block075Part004
    + surrogateDiagTailX0RatChunk000Sub000Block075Part005
    + surrogateDiagTailX0RatChunk000Sub000Block075Part006
    + surrogateDiagTailX0RatChunk000Sub000Block075Part007
    + surrogateDiagTailX0RatChunk000Sub000Block075Part008
    + surrogateDiagTailX0RatChunk000Sub000Block075Part009

def surrogateDiagonalTailChunk000Sub000Block075MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block075Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block075Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block075Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block075Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block075Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block075Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block075Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block075Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block075Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block075Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block075Mid : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block075Part010
    + surrogateDiagTailX0RatChunk000Sub000Block075Part011
    + surrogateDiagTailX0RatChunk000Sub000Block075Part012
    + surrogateDiagTailX0RatChunk000Sub000Block075Part013
    + surrogateDiagTailX0RatChunk000Sub000Block075Part014
    + surrogateDiagTailX0RatChunk000Sub000Block075Part015
    + surrogateDiagTailX0RatChunk000Sub000Block075Part016
    + surrogateDiagTailX0RatChunk000Sub000Block075Part017
    + surrogateDiagTailX0RatChunk000Sub000Block075Part018
    + surrogateDiagTailX0RatChunk000Sub000Block075Part019

def surrogateDiagonalTailChunk000Sub000Block075TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block075Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block075Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block075Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block075Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block075Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block075Tail : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block075Part020
    + surrogateDiagTailX0RatChunk000Sub000Block075Part021
    + surrogateDiagTailX0RatChunk000Sub000Block075Part022
    + surrogateDiagTailX0RatChunk000Sub000Block075Part023
    + surrogateDiagTailX0RatChunk000Sub000Block075Part024

def surrogateDiagonalTailChunk000Sub000Block075Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub000Block075HeadSum X0
    + surrogateDiagonalTailChunk000Sub000Block075MidSum X0
    + surrogateDiagonalTailChunk000Sub000Block075TailSum X0

def surrogateDiagTailX0RatChunk000Sub000Block075 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block075Part000
    + surrogateDiagTailX0RatChunk000Sub000Block075Part001
    + surrogateDiagTailX0RatChunk000Sub000Block075Part002
    + surrogateDiagTailX0RatChunk000Sub000Block075Part003
    + surrogateDiagTailX0RatChunk000Sub000Block075Part004
    + surrogateDiagTailX0RatChunk000Sub000Block075Part005
    + surrogateDiagTailX0RatChunk000Sub000Block075Part006
    + surrogateDiagTailX0RatChunk000Sub000Block075Part007
    + surrogateDiagTailX0RatChunk000Sub000Block075Part008
    + surrogateDiagTailX0RatChunk000Sub000Block075Part009
    + surrogateDiagTailX0RatChunk000Sub000Block075Part010
    + surrogateDiagTailX0RatChunk000Sub000Block075Part011
    + surrogateDiagTailX0RatChunk000Sub000Block075Part012
    + surrogateDiagTailX0RatChunk000Sub000Block075Part013
    + surrogateDiagTailX0RatChunk000Sub000Block075Part014
    + surrogateDiagTailX0RatChunk000Sub000Block075Part015
    + surrogateDiagTailX0RatChunk000Sub000Block075Part016
    + surrogateDiagTailX0RatChunk000Sub000Block075Part017
    + surrogateDiagTailX0RatChunk000Sub000Block075Part018
    + surrogateDiagTailX0RatChunk000Sub000Block075Part019
    + surrogateDiagTailX0RatChunk000Sub000Block075Part020
    + surrogateDiagTailX0RatChunk000Sub000Block075Part021
    + surrogateDiagTailX0RatChunk000Sub000Block075Part022
    + surrogateDiagTailX0RatChunk000Sub000Block075Part023
    + surrogateDiagTailX0RatChunk000Sub000Block075Part024

theorem surrogateDiagTailX0RatChunk000Sub000Block075_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk000Sub000Block075Head + surrogateDiagTailX0RatChunk000Sub000Block075Mid + surrogateDiagTailX0RatChunk000Sub000Block075Tail =
      surrogateDiagTailX0RatChunk000Sub000Block075 := by
  unfold surrogateDiagTailX0RatChunk000Sub000Block075Head surrogateDiagTailX0RatChunk000Sub000Block075Mid surrogateDiagTailX0RatChunk000Sub000Block075Tail surrogateDiagTailX0RatChunk000Sub000Block075
  ring

def SurrogateDiagonalTailChunk000Sub000Block075HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block075HeadSum X0 = surrogateDiagTailX0RatChunk000Sub000Block075Head

def SurrogateDiagonalTailChunk000Sub000Block075MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block075MidSum X0 = surrogateDiagTailX0RatChunk000Sub000Block075Mid

def SurrogateDiagonalTailChunk000Sub000Block075TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block075TailSum X0 = surrogateDiagTailX0RatChunk000Sub000Block075Tail

theorem surrogateDiagonalTailChunk000Sub000Block075_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk000Sub000Block075HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk000Sub000Block075MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk000Sub000Block075TailCertificateAt X0) :
    surrogateDiagonalTailChunk000Sub000Block075Sum X0 = surrogateDiagTailX0RatChunk000Sub000Block075 := by
  unfold SurrogateDiagonalTailChunk000Sub000Block075HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk000Sub000Block075MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk000Sub000Block075TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk000Sub000Block075Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk000Sub000Block075_eq_head_add_mid_add_tail

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

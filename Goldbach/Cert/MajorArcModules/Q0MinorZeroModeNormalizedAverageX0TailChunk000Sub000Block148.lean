import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0TailPilot25

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

open scoped BigOperators

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

/- Generated direct-term certificate blocks for tail chunk 000, subchunk 000, blocks [148,149). -/

/- Block 148 covers tail-support indices [3700,3725) and q from 6135 to 6178. -/

def TailChunk000Sub000Block148Part000SupportExplicit : Finset ℕ :=
  ([6135] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block148Part000 : ℚ :=
  (38246061025 : ℚ) / 10511475806306304

def SurrogateDiagonalTailChunk000Sub000Block148Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6135
    = surrogateDiagTailX0RatChunk000Sub000Block148Part000

theorem surrogateDiagonalTailChunk000Sub000Block148Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block148Part000CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block148Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block148Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block148Part000CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block148Part000SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block148Part000] using hcert

def TailChunk000Sub000Block148Part001SupportExplicit : Finset ℕ :=
  ([6139] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block148Part001 : ℚ :=
  (1920657411775 : ℚ) / 1908307183337883648

def SurrogateDiagonalTailChunk000Sub000Block148Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6139
    = surrogateDiagTailX0RatChunk000Sub000Block148Part001

theorem surrogateDiagonalTailChunk000Sub000Block148Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block148Part001CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block148Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block148Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block148Part001CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block148Part001SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block148Part001] using hcert

def TailChunk000Sub000Block148Part002SupportExplicit : Finset ℕ :=
  ([6141] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block148Part002 : ℚ :=
  (25786837575 : ℚ) / 11709194391617536

def SurrogateDiagonalTailChunk000Sub000Block148Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6141
    = surrogateDiagTailX0RatChunk000Sub000Block148Part002

theorem surrogateDiagonalTailChunk000Sub000Block148Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block148Part002CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block148Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block148Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block148Part002CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block148Part002SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block148Part002] using hcert

def TailChunk000Sub000Block148Part003SupportExplicit : Finset ℕ :=
  ([6142] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block148Part003 : ℚ :=
  (8788624175 : ℚ) / 1483482070766736

def SurrogateDiagonalTailChunk000Sub000Block148Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6142
    = surrogateDiagTailX0RatChunk000Sub000Block148Part003

theorem surrogateDiagonalTailChunk000Sub000Block148Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block148Part003CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block148Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block148Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block148Part003CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block148Part003SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block148Part003] using hcert

def TailChunk000Sub000Block148Part004SupportExplicit : Finset ℕ :=
  ([6143] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block148Part004 : ℚ :=
  (589632015625 : ℚ) / 889623232505497362

def SurrogateDiagonalTailChunk000Sub000Block148Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6143
    = surrogateDiagTailX0RatChunk000Sub000Block148Part004

theorem surrogateDiagonalTailChunk000Sub000Block148Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block148Part004CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block148Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block148Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block148Part004CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block148Part004SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block148Part004] using hcert

def TailChunk000Sub000Block148Part005SupportExplicit : Finset ℕ :=
  ([6145] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block148Part005 : ℚ :=
  (896160225425 : ℚ) / 727830575169552384

def SurrogateDiagonalTailChunk000Sub000Block148Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6145
    = surrogateDiagTailX0RatChunk000Sub000Block148Part005

theorem surrogateDiagonalTailChunk000Sub000Block148Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block148Part005CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block148Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block148Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block148Part005CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block148Part005SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block148Part005] using hcert

def TailChunk000Sub000Block148Part006SupportExplicit : Finset ℕ :=
  ([6146] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block148Part006 : ℚ :=
  (492628562225 : ℚ) / 59634599479308864

def SurrogateDiagonalTailChunk000Sub000Block148Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6146
    = surrogateDiagTailX0RatChunk000Sub000Block148Part006

theorem surrogateDiagonalTailChunk000Sub000Block148Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block148Part006CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block148Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block148Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block148Part006CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block148Part006SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block148Part006] using hcert

def TailChunk000Sub000Block148Part007SupportExplicit : Finset ℕ :=
  ([6149] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block148Part007 : ℚ :=
  (1861597501 : ℚ) / 1613425827041280

def SurrogateDiagonalTailChunk000Sub000Block148Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6149
    = surrogateDiagTailX0RatChunk000Sub000Block148Part007

theorem surrogateDiagonalTailChunk000Sub000Block148Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block148Part007CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block148Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block148Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block148Part007CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block148Part007SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block148Part007] using hcert

def TailChunk000Sub000Block148Part008SupportExplicit : Finset ℕ :=
  ([6151] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block148Part008 : ℚ :=
  (37834801 : ℚ) / 57233104582050

def SurrogateDiagonalTailChunk000Sub000Block148Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6151
    = surrogateDiagTailX0RatChunk000Sub000Block148Part008

theorem surrogateDiagonalTailChunk000Sub000Block148Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block148Part008CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block148Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block148Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block148Part008CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block148Part008SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block148Part008] using hcert

def TailChunk000Sub000Block148Part009SupportExplicit : Finset ℕ :=
  ([6153] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block148Part009 : ℚ :=
  (327399839275 : ℚ) / 94237391769772032

def SurrogateDiagonalTailChunk000Sub000Block148Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6153
    = surrogateDiagTailX0RatChunk000Sub000Block148Part009

theorem surrogateDiagonalTailChunk000Sub000Block148Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block148Part009CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block148Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block148Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block148Part009CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block148Part009SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block148Part009] using hcert

def TailChunk000Sub000Block148Part010SupportExplicit : Finset ℕ :=
  ([6154] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block148Part010 : ℚ :=
  (1824364369 : ℚ) / 286711794892800

def SurrogateDiagonalTailChunk000Sub000Block148Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6154
    = surrogateDiagTailX0RatChunk000Sub000Block148Part010

theorem surrogateDiagonalTailChunk000Sub000Block148Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block148Part010CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block148Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block148Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block148Part010CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block148Part010SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block148Part010] using hcert

def TailChunk000Sub000Block148Part011SupportExplicit : Finset ℕ :=
  ([6155] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block148Part011 : ℚ :=
  (5993864357 : ℚ) / 4883891591001600

def SurrogateDiagonalTailChunk000Sub000Block148Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6155
    = surrogateDiagTailX0RatChunk000Sub000Block148Part011

theorem surrogateDiagonalTailChunk000Sub000Block148Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block148Part011CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block148Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block148Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block148Part011CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block148Part011SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block148Part011] using hcert

def TailChunk000Sub000Block148Part012SupportExplicit : Finset ℕ :=
  ([6157] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block148Part012 : ℚ :=
  (91549433767 : ℚ) / 127906196940163200

def SurrogateDiagonalTailChunk000Sub000Block148Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6157
    = surrogateDiagTailX0RatChunk000Sub000Block148Part012

theorem surrogateDiagonalTailChunk000Sub000Block148Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block148Part012CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block148Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block148Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block148Part012CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block148Part012SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block148Part012] using hcert

def TailChunk000Sub000Block148Part013SupportExplicit : Finset ℕ :=
  ([6158] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block148Part013 : ℚ :=
  (1184793118975 : ℚ) / 224440548231459528

def SurrogateDiagonalTailChunk000Sub000Block148Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6158
    = surrogateDiagTailX0RatChunk000Sub000Block148Part013

theorem surrogateDiagonalTailChunk000Sub000Block148Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block148Part013CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block148Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block148Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block148Part013CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block148Part013SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block148Part013] using hcert

def TailChunk000Sub000Block148Part014SupportExplicit : Finset ℕ :=
  ([6159] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block148Part014 : ℚ :=
  (263428826075 : ℚ) / 354671483625022464

def SurrogateDiagonalTailChunk000Sub000Block148Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6159
    = surrogateDiagTailX0RatChunk000Sub000Block148Part014

theorem surrogateDiagonalTailChunk000Sub000Block148Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block148Part014CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block148Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block148Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block148Part014CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block148Part014SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block148Part014] using hcert

def TailChunk000Sub000Block148Part015SupportExplicit : Finset ℕ :=
  ([6161] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block148Part015 : ℚ :=
  (993908117 : ℚ) / 64812960000000000

def SurrogateDiagonalTailChunk000Sub000Block148Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6161
    = surrogateDiagTailX0RatChunk000Sub000Block148Part015

theorem surrogateDiagonalTailChunk000Sub000Block148Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block148Part015CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block148Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block148Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block148Part015CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block148Part015SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block148Part015] using hcert

def TailChunk000Sub000Block148Part016SupportExplicit : Finset ℕ :=
  ([6162] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block148Part016 : ℚ :=
  (490382183725 : ℚ) / 30707908402249728

def SurrogateDiagonalTailChunk000Sub000Block148Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6162
    = surrogateDiagTailX0RatChunk000Sub000Block148Part016

theorem surrogateDiagonalTailChunk000Sub000Block148Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block148Part016CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block148Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block148Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block148Part016CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block148Part016SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block148Part016] using hcert

def TailChunk000Sub000Block148Part017SupportExplicit : Finset ℕ :=
  ([6163] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block148Part017 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub000Block148Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6163
    = surrogateDiagTailX0RatChunk000Sub000Block148Part017

theorem surrogateDiagonalTailChunk000Sub000Block148Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block148Part017CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block148Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block148Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block148Part017CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block148Part017SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block148Part017] using hcert

def TailChunk000Sub000Block148Part018SupportExplicit : Finset ℕ :=
  ([6166] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block148Part018 : ℚ :=
  (148513890625 : ℚ) / 56402376737313522

def SurrogateDiagonalTailChunk000Sub000Block148Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6166
    = surrogateDiagTailX0RatChunk000Sub000Block148Part018

theorem surrogateDiagonalTailChunk000Sub000Block148Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block148Part018CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block148Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block148Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block148Part018CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block148Part018SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block148Part018] using hcert

def TailChunk000Sub000Block148Part019SupportExplicit : Finset ℕ :=
  ([6167] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block148Part019 : ℚ :=
  (81106567 : ℚ) / 539833769164800

def SurrogateDiagonalTailChunk000Sub000Block148Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6167
    = surrogateDiagTailX0RatChunk000Sub000Block148Part019

theorem surrogateDiagonalTailChunk000Sub000Block148Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block148Part019CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block148Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block148Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block148Part019CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block148Part019SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block148Part019] using hcert

def TailChunk000Sub000Block148Part020SupportExplicit : Finset ℕ :=
  ([6169] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block148Part020 : ℚ :=
  (62506151 : ℚ) / 2767069812101760

def SurrogateDiagonalTailChunk000Sub000Block148Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6169
    = surrogateDiagTailX0RatChunk000Sub000Block148Part020

theorem surrogateDiagonalTailChunk000Sub000Block148Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block148Part020CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block148Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block148Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block148Part020CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block148Part020SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block148Part020] using hcert

def TailChunk000Sub000Block148Part021SupportExplicit : Finset ℕ :=
  ([6170] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block148Part021 : ℚ :=
  (34173993325 : ℚ) / 5760626132287488

def SurrogateDiagonalTailChunk000Sub000Block148Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6170
    = surrogateDiagTailX0RatChunk000Sub000Block148Part021

theorem surrogateDiagonalTailChunk000Sub000Block148Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block148Part021CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block148Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block148Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block148Part021CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block148Part021SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block148Part021] using hcert

def TailChunk000Sub000Block148Part022SupportExplicit : Finset ℕ :=
  ([6173] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block148Part022 : ℚ :=
  (595405140625 : ℚ) / 907132103870905632

def SurrogateDiagonalTailChunk000Sub000Block148Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6173
    = surrogateDiagTailX0RatChunk000Sub000Block148Part022

theorem surrogateDiagonalTailChunk000Sub000Block148Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block148Part022CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block148Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block148Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block148Part022CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block148Part022SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block148Part022] using hcert

def TailChunk000Sub000Block148Part023SupportExplicit : Finset ℕ :=
  ([6177] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block148Part023 : ℚ :=
  (8564223931 : ℚ) / 3373906774425600

def SurrogateDiagonalTailChunk000Sub000Block148Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6177
    = surrogateDiagTailX0RatChunk000Sub000Block148Part023

theorem surrogateDiagonalTailChunk000Sub000Block148Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block148Part023CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block148Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block148Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block148Part023CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block148Part023SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block148Part023] using hcert

def TailChunk000Sub000Block148Part024SupportExplicit : Finset ℕ :=
  ([6178] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block148Part024 : ℚ :=
  (1192501576975 : ℚ) / 227371499290656768

def SurrogateDiagonalTailChunk000Sub000Block148Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6178
    = surrogateDiagTailX0RatChunk000Sub000Block148Part024

theorem surrogateDiagonalTailChunk000Sub000Block148Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block148Part024CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block148Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block148Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block148Part024CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block148Part024SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block148Part024] using hcert

def surrogateDiagonalTailChunk000Sub000Block148HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block148Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block148Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block148Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block148Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block148Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block148Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block148Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block148Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block148Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block148Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block148Head : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block148Part000
    + surrogateDiagTailX0RatChunk000Sub000Block148Part001
    + surrogateDiagTailX0RatChunk000Sub000Block148Part002
    + surrogateDiagTailX0RatChunk000Sub000Block148Part003
    + surrogateDiagTailX0RatChunk000Sub000Block148Part004
    + surrogateDiagTailX0RatChunk000Sub000Block148Part005
    + surrogateDiagTailX0RatChunk000Sub000Block148Part006
    + surrogateDiagTailX0RatChunk000Sub000Block148Part007
    + surrogateDiagTailX0RatChunk000Sub000Block148Part008
    + surrogateDiagTailX0RatChunk000Sub000Block148Part009

def surrogateDiagonalTailChunk000Sub000Block148MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block148Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block148Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block148Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block148Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block148Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block148Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block148Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block148Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block148Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block148Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block148Mid : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block148Part010
    + surrogateDiagTailX0RatChunk000Sub000Block148Part011
    + surrogateDiagTailX0RatChunk000Sub000Block148Part012
    + surrogateDiagTailX0RatChunk000Sub000Block148Part013
    + surrogateDiagTailX0RatChunk000Sub000Block148Part014
    + surrogateDiagTailX0RatChunk000Sub000Block148Part015
    + surrogateDiagTailX0RatChunk000Sub000Block148Part016
    + surrogateDiagTailX0RatChunk000Sub000Block148Part017
    + surrogateDiagTailX0RatChunk000Sub000Block148Part018
    + surrogateDiagTailX0RatChunk000Sub000Block148Part019

def surrogateDiagonalTailChunk000Sub000Block148TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block148Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block148Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block148Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block148Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block148Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block148Tail : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block148Part020
    + surrogateDiagTailX0RatChunk000Sub000Block148Part021
    + surrogateDiagTailX0RatChunk000Sub000Block148Part022
    + surrogateDiagTailX0RatChunk000Sub000Block148Part023
    + surrogateDiagTailX0RatChunk000Sub000Block148Part024

def surrogateDiagonalTailChunk000Sub000Block148Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub000Block148HeadSum X0
    + surrogateDiagonalTailChunk000Sub000Block148MidSum X0
    + surrogateDiagonalTailChunk000Sub000Block148TailSum X0

def surrogateDiagTailX0RatChunk000Sub000Block148 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block148Part000
    + surrogateDiagTailX0RatChunk000Sub000Block148Part001
    + surrogateDiagTailX0RatChunk000Sub000Block148Part002
    + surrogateDiagTailX0RatChunk000Sub000Block148Part003
    + surrogateDiagTailX0RatChunk000Sub000Block148Part004
    + surrogateDiagTailX0RatChunk000Sub000Block148Part005
    + surrogateDiagTailX0RatChunk000Sub000Block148Part006
    + surrogateDiagTailX0RatChunk000Sub000Block148Part007
    + surrogateDiagTailX0RatChunk000Sub000Block148Part008
    + surrogateDiagTailX0RatChunk000Sub000Block148Part009
    + surrogateDiagTailX0RatChunk000Sub000Block148Part010
    + surrogateDiagTailX0RatChunk000Sub000Block148Part011
    + surrogateDiagTailX0RatChunk000Sub000Block148Part012
    + surrogateDiagTailX0RatChunk000Sub000Block148Part013
    + surrogateDiagTailX0RatChunk000Sub000Block148Part014
    + surrogateDiagTailX0RatChunk000Sub000Block148Part015
    + surrogateDiagTailX0RatChunk000Sub000Block148Part016
    + surrogateDiagTailX0RatChunk000Sub000Block148Part017
    + surrogateDiagTailX0RatChunk000Sub000Block148Part018
    + surrogateDiagTailX0RatChunk000Sub000Block148Part019
    + surrogateDiagTailX0RatChunk000Sub000Block148Part020
    + surrogateDiagTailX0RatChunk000Sub000Block148Part021
    + surrogateDiagTailX0RatChunk000Sub000Block148Part022
    + surrogateDiagTailX0RatChunk000Sub000Block148Part023
    + surrogateDiagTailX0RatChunk000Sub000Block148Part024

theorem surrogateDiagTailX0RatChunk000Sub000Block148_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk000Sub000Block148Head + surrogateDiagTailX0RatChunk000Sub000Block148Mid + surrogateDiagTailX0RatChunk000Sub000Block148Tail =
      surrogateDiagTailX0RatChunk000Sub000Block148 := by
  unfold surrogateDiagTailX0RatChunk000Sub000Block148Head surrogateDiagTailX0RatChunk000Sub000Block148Mid surrogateDiagTailX0RatChunk000Sub000Block148Tail surrogateDiagTailX0RatChunk000Sub000Block148
  ring

def SurrogateDiagonalTailChunk000Sub000Block148HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block148HeadSum X0 = surrogateDiagTailX0RatChunk000Sub000Block148Head

def SurrogateDiagonalTailChunk000Sub000Block148MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block148MidSum X0 = surrogateDiagTailX0RatChunk000Sub000Block148Mid

def SurrogateDiagonalTailChunk000Sub000Block148TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block148TailSum X0 = surrogateDiagTailX0RatChunk000Sub000Block148Tail

theorem surrogateDiagonalTailChunk000Sub000Block148_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk000Sub000Block148HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk000Sub000Block148MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk000Sub000Block148TailCertificateAt X0) :
    surrogateDiagonalTailChunk000Sub000Block148Sum X0 = surrogateDiagTailX0RatChunk000Sub000Block148 := by
  unfold SurrogateDiagonalTailChunk000Sub000Block148HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk000Sub000Block148MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk000Sub000Block148TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk000Sub000Block148Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk000Sub000Block148_eq_head_add_mid_add_tail

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

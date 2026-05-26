import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0TailPilot25

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

open scoped BigOperators

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

/- Generated direct-term certificate blocks for tail chunk 001, subchunk 000, blocks [0,10). -/

/-- Block 000 covers tail-support indices [10000,10025) and q from 16498 to 16537. -/

def TailChunk001Sub000Block000Part000SupportExplicit : Finset ℕ :=
  ([16498] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block000Part000 : ℚ :=
  (85863784075 : ℚ) / 220286406252036096

def SurrogateDiagonalTailChunk001Sub000Block000Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16498
    = surrogateDiagTailX0RatChunk001Sub000Block000Part000

theorem surrogateDiagonalTailChunk001Sub000Block000Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block000Part000CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block000Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block000Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block000Part000CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block000Part000SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block000Part000] using hcert

def TailChunk001Sub000Block000Part001SupportExplicit : Finset ℕ :=
  ([16499] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block000Part001 : ℚ :=
  (347789018375 : ℚ) / 49923268286673429504

def SurrogateDiagonalTailChunk001Sub000Block000Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16499
    = surrogateDiagTailX0RatChunk001Sub000Block000Part001

theorem surrogateDiagonalTailChunk001Sub000Block000Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block000Part001CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block000Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block000Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block000Part001CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block000Part001SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block000Part001] using hcert

def TailChunk001Sub000Block000Part002SupportExplicit : Finset ℕ :=
  ([16501] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block000Part002 : ℚ :=
  (13565510375 : ℚ) / 11426791193728253952

def SurrogateDiagonalTailChunk001Sub000Block000Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16501
    = surrogateDiagTailX0RatChunk001Sub000Block000Part002

theorem surrogateDiagonalTailChunk001Sub000Block000Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block000Part002CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block000Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block000Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block000Part002CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block000Part002SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block000Part002] using hcert

def TailChunk001Sub000Block000Part003SupportExplicit : Finset ℕ :=
  ([16502] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block000Part003 : ℚ :=
  (113014424075 : ℚ) / 283365033870279168

def SurrogateDiagonalTailChunk001Sub000Block000Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16502
    = surrogateDiagTailX0RatChunk001Sub000Block000Part003

theorem surrogateDiagonalTailChunk001Sub000Block000Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block000Part003CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block000Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block000Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block000Part003CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block000Part003SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block000Part003] using hcert

def TailChunk001Sub000Block000Part004SupportExplicit : Finset ℕ :=
  ([16503] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block000Part004 : ℚ :=
  (37825001 : ℚ) / 732196410000000

def SurrogateDiagonalTailChunk001Sub000Block000Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16503
    = surrogateDiagTailX0RatChunk001Sub000Block000Part004

theorem surrogateDiagonalTailChunk001Sub000Block000Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block000Part004CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block000Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block000Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block000Part004CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block000Part004SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block000Part004] using hcert

def TailChunk001Sub000Block000Part005SupportExplicit : Finset ℕ :=
  ([16505] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block000Part005 : ℚ :=
  (5455006199 : ℚ) / 607312990310400000

def SurrogateDiagonalTailChunk001Sub000Block000Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16505
    = surrogateDiagTailX0RatChunk001Sub000Block000Part005

theorem surrogateDiagonalTailChunk001Sub000Block000Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block000Part005CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block000Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block000Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block000Part005CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block000Part005SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block000Part005] using hcert

def TailChunk001Sub000Block000Part006SupportExplicit : Finset ℕ :=
  ([16507] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block000Part006 : ℚ :=
  (2383220253 : ℚ) / 967169221767987200

def SurrogateDiagonalTailChunk001Sub000Block000Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16507
    = surrogateDiagTailX0RatChunk001Sub000Block000Part006

theorem surrogateDiagonalTailChunk001Sub000Block000Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block000Part006CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block000Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block000Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block000Part006CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block000Part006SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block000Part006] using hcert

def TailChunk001Sub000Block000Part007SupportExplicit : Finset ℕ :=
  ([16509] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block000Part007 : ℚ :=
  (135187521425 : ℚ) / 2618792871489289152

def SurrogateDiagonalTailChunk001Sub000Block000Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16509
    = surrogateDiagTailX0RatChunk001Sub000Block000Part007

theorem surrogateDiagonalTailChunk001Sub000Block000Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block000Part007CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block000Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block000Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block000Part007CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block000Part007SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block000Part007] using hcert

def TailChunk001Sub000Block000Part008SupportExplicit : Finset ℕ :=
  ([16510] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block000Part008 : ℚ :=
  (2727082194625 : ℚ) / 3345599794952798208

def SurrogateDiagonalTailChunk001Sub000Block000Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16510
    = surrogateDiagTailX0RatChunk001Sub000Block000Part008

theorem surrogateDiagonalTailChunk001Sub000Block000Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block000Part008CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block000Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block000Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block000Part008CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block000Part008SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block000Part008] using hcert

def TailChunk001Sub000Block000Part009SupportExplicit : Finset ℕ :=
  ([16511] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block000Part009 : ℚ :=
  (2248132849 : ℚ) / 323872471429977600

def SurrogateDiagonalTailChunk001Sub000Block000Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16511
    = surrogateDiagTailX0RatChunk001Sub000Block000Part009

theorem surrogateDiagonalTailChunk001Sub000Block000Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block000Part009CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block000Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block000Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block000Part009CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block000Part009SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block000Part009] using hcert

def TailChunk001Sub000Block000Part010SupportExplicit : Finset ℕ :=
  ([16514] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block000Part010 : ℚ :=
  (3988592721775 : ℚ) / 9621652966937666688

def SurrogateDiagonalTailChunk001Sub000Block000Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16514
    = surrogateDiagTailX0RatChunk001Sub000Block000Part010

theorem surrogateDiagonalTailChunk001Sub000Block000Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block000Part010CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block000Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block000Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block000Part010CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block000Part010SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block000Part010] using hcert

def TailChunk001Sub000Block000Part011SupportExplicit : Finset ℕ :=
  ([16517] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block000Part011 : ℚ :=
  (43244539625 : ℚ) / 86878643992383127104

def SurrogateDiagonalTailChunk001Sub000Block000Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16517
    = surrogateDiagTailX0RatChunk001Sub000Block000Part011

theorem surrogateDiagonalTailChunk001Sub000Block000Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block000Part011CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block000Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block000Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block000Part011CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block000Part011SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block000Part011] using hcert

def TailChunk001Sub000Block000Part012SupportExplicit : Finset ℕ :=
  ([16518] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block000Part012 : ℚ :=
  (1183861771925 : ℚ) / 1147388688611672064

def SurrogateDiagonalTailChunk001Sub000Block000Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16518
    = surrogateDiagTailX0RatChunk001Sub000Block000Part012

theorem surrogateDiagonalTailChunk001Sub000Block000Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block000Part012CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block000Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block000Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block000Part012CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block000Part012SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block000Part012] using hcert

def TailChunk001Sub000Block000Part013SupportExplicit : Finset ℕ :=
  ([16519] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block000Part013 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block000Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16519
    = surrogateDiagTailX0RatChunk001Sub000Block000Part013

theorem surrogateDiagonalTailChunk001Sub000Block000Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block000Part013CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block000Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block000Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block000Part013CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block000Part013SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block000Part013] using hcert

def TailChunk001Sub000Block000Part014SupportExplicit : Finset ℕ :=
  ([16521] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block000Part014 : ℚ :=
  (947688649925 : ℚ) / 18384917023220933184

def SurrogateDiagonalTailChunk001Sub000Block000Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16521
    = surrogateDiagTailX0RatChunk001Sub000Block000Part014

theorem surrogateDiagonalTailChunk001Sub000Block000Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block000Part014CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block000Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block000Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block000Part014CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block000Part014SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block000Part014] using hcert

def TailChunk001Sub000Block000Part015SupportExplicit : Finset ℕ :=
  ([16522] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block000Part015 : ℚ :=
  (4973756249 : ℚ) / 10548984375000000

def SurrogateDiagonalTailChunk001Sub000Block000Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16522
    = surrogateDiagTailX0RatChunk001Sub000Block000Part015

theorem surrogateDiagonalTailChunk001Sub000Block000Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block000Part015CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block000Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block000Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block000Part015CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block000Part015SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block000Part015] using hcert

def TailChunk001Sub000Block000Part016SupportExplicit : Finset ℕ :=
  ([16523] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block000Part016 : ℚ :=
  (24689394451 : ℚ) / 4300676923392000000

def SurrogateDiagonalTailChunk001Sub000Block000Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16523
    = surrogateDiagTailX0RatChunk001Sub000Block000Part016

theorem surrogateDiagonalTailChunk001Sub000Block000Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block000Part016CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block000Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block000Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block000Part016CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block000Part016SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block000Part016] using hcert

def TailChunk001Sub000Block000Part017SupportExplicit : Finset ℕ :=
  ([16526] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block000Part017 : ℚ :=
  (1066830765625 : ℚ) / 2912779638999121842

def SurrogateDiagonalTailChunk001Sub000Block000Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16526
    = surrogateDiagTailX0RatChunk001Sub000Block000Part017

theorem surrogateDiagonalTailChunk001Sub000Block000Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block000Part017CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block000Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block000Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block000Part017CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block000Part017SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block000Part017] using hcert

def TailChunk001Sub000Block000Part018SupportExplicit : Finset ℕ :=
  ([16527] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block000Part018 : ℚ :=
  (1818506028325 : ℚ) / 19789828346647922688

def SurrogateDiagonalTailChunk001Sub000Block000Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16527
    = surrogateDiagTailX0RatChunk001Sub000Block000Part018

theorem surrogateDiagonalTailChunk001Sub000Block000Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block000Part018CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block000Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block000Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block000Part018CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block000Part018SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block000Part018] using hcert

def TailChunk001Sub000Block000Part019SupportExplicit : Finset ℕ :=
  ([16529] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block000Part019 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block000Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16529
    = surrogateDiagTailX0RatChunk001Sub000Block000Part019

theorem surrogateDiagonalTailChunk001Sub000Block000Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block000Part019CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block000Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block000Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block000Part019CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block000Part019SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block000Part019] using hcert

def TailChunk001Sub000Block000Part020SupportExplicit : Finset ℕ :=
  ([16530] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block000Part020 : ℚ :=
  (1580535370675 : ℚ) / 660859218756108288

def SurrogateDiagonalTailChunk001Sub000Block000Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16530
    = surrogateDiagTailX0RatChunk001Sub000Block000Part020

theorem surrogateDiagonalTailChunk001Sub000Block000Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block000Part020CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block000Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block000Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block000Part020CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block000Part020SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block000Part020] using hcert

def TailChunk001Sub000Block000Part021SupportExplicit : Finset ℕ :=
  ([16531] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block000Part021 : ℚ :=
  (401965633 : ℚ) / 688885285507200000

def SurrogateDiagonalTailChunk001Sub000Block000Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16531
    = surrogateDiagTailX0RatChunk001Sub000Block000Part021

theorem surrogateDiagonalTailChunk001Sub000Block000Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block000Part021CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block000Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block000Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block000Part021CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block000Part021SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block000Part021] using hcert

def TailChunk001Sub000Block000Part022SupportExplicit : Finset ℕ :=
  ([16534] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block000Part022 : ℚ :=
  (7547486651 : ℚ) / 13961991711974400

def SurrogateDiagonalTailChunk001Sub000Block000Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16534
    = surrogateDiagTailX0RatChunk001Sub000Block000Part022

theorem surrogateDiagonalTailChunk001Sub000Block000Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block000Part022CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block000Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block000Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block000Part022CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block000Part022SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block000Part022] using hcert

def TailChunk001Sub000Block000Part023SupportExplicit : Finset ℕ :=
  ([16535] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block000Part023 : ℚ :=
  (684353024125 : ℚ) / 76467734067913279488

def SurrogateDiagonalTailChunk001Sub000Block000Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16535
    = surrogateDiagTailX0RatChunk001Sub000Block000Part023

theorem surrogateDiagonalTailChunk001Sub000Block000Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block000Part023CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block000Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block000Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block000Part023CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block000Part023SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block000Part023] using hcert

def TailChunk001Sub000Block000Part024SupportExplicit : Finset ℕ :=
  ([16537] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block000Part024 : ℚ :=
  (29016957725 : ℚ) / 19459217493221667216

def SurrogateDiagonalTailChunk001Sub000Block000Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16537
    = surrogateDiagTailX0RatChunk001Sub000Block000Part024

theorem surrogateDiagonalTailChunk001Sub000Block000Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block000Part024CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block000Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block000Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block000Part024CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block000Part024SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block000Part024] using hcert

def surrogateDiagonalTailChunk001Sub000Block000HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block000Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block000Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block000Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block000Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block000Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block000Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block000Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block000Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block000Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block000Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block000Head : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block000Part000
    + surrogateDiagTailX0RatChunk001Sub000Block000Part001
    + surrogateDiagTailX0RatChunk001Sub000Block000Part002
    + surrogateDiagTailX0RatChunk001Sub000Block000Part003
    + surrogateDiagTailX0RatChunk001Sub000Block000Part004
    + surrogateDiagTailX0RatChunk001Sub000Block000Part005
    + surrogateDiagTailX0RatChunk001Sub000Block000Part006
    + surrogateDiagTailX0RatChunk001Sub000Block000Part007
    + surrogateDiagTailX0RatChunk001Sub000Block000Part008
    + surrogateDiagTailX0RatChunk001Sub000Block000Part009

def surrogateDiagonalTailChunk001Sub000Block000MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block000Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block000Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block000Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block000Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block000Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block000Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block000Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block000Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block000Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block000Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block000Mid : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block000Part010
    + surrogateDiagTailX0RatChunk001Sub000Block000Part011
    + surrogateDiagTailX0RatChunk001Sub000Block000Part012
    + surrogateDiagTailX0RatChunk001Sub000Block000Part013
    + surrogateDiagTailX0RatChunk001Sub000Block000Part014
    + surrogateDiagTailX0RatChunk001Sub000Block000Part015
    + surrogateDiagTailX0RatChunk001Sub000Block000Part016
    + surrogateDiagTailX0RatChunk001Sub000Block000Part017
    + surrogateDiagTailX0RatChunk001Sub000Block000Part018
    + surrogateDiagTailX0RatChunk001Sub000Block000Part019

def surrogateDiagonalTailChunk001Sub000Block000TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block000Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block000Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block000Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block000Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block000Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block000Tail : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block000Part020
    + surrogateDiagTailX0RatChunk001Sub000Block000Part021
    + surrogateDiagTailX0RatChunk001Sub000Block000Part022
    + surrogateDiagTailX0RatChunk001Sub000Block000Part023
    + surrogateDiagTailX0RatChunk001Sub000Block000Part024

def surrogateDiagonalTailChunk001Sub000Block000Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk001Sub000Block000HeadSum X0
    + surrogateDiagonalTailChunk001Sub000Block000MidSum X0
    + surrogateDiagonalTailChunk001Sub000Block000TailSum X0

def surrogateDiagTailX0RatChunk001Sub000Block000 : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block000Part000
    + surrogateDiagTailX0RatChunk001Sub000Block000Part001
    + surrogateDiagTailX0RatChunk001Sub000Block000Part002
    + surrogateDiagTailX0RatChunk001Sub000Block000Part003
    + surrogateDiagTailX0RatChunk001Sub000Block000Part004
    + surrogateDiagTailX0RatChunk001Sub000Block000Part005
    + surrogateDiagTailX0RatChunk001Sub000Block000Part006
    + surrogateDiagTailX0RatChunk001Sub000Block000Part007
    + surrogateDiagTailX0RatChunk001Sub000Block000Part008
    + surrogateDiagTailX0RatChunk001Sub000Block000Part009
    + surrogateDiagTailX0RatChunk001Sub000Block000Part010
    + surrogateDiagTailX0RatChunk001Sub000Block000Part011
    + surrogateDiagTailX0RatChunk001Sub000Block000Part012
    + surrogateDiagTailX0RatChunk001Sub000Block000Part013
    + surrogateDiagTailX0RatChunk001Sub000Block000Part014
    + surrogateDiagTailX0RatChunk001Sub000Block000Part015
    + surrogateDiagTailX0RatChunk001Sub000Block000Part016
    + surrogateDiagTailX0RatChunk001Sub000Block000Part017
    + surrogateDiagTailX0RatChunk001Sub000Block000Part018
    + surrogateDiagTailX0RatChunk001Sub000Block000Part019
    + surrogateDiagTailX0RatChunk001Sub000Block000Part020
    + surrogateDiagTailX0RatChunk001Sub000Block000Part021
    + surrogateDiagTailX0RatChunk001Sub000Block000Part022
    + surrogateDiagTailX0RatChunk001Sub000Block000Part023
    + surrogateDiagTailX0RatChunk001Sub000Block000Part024

theorem surrogateDiagTailX0RatChunk001Sub000Block000_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk001Sub000Block000Head + surrogateDiagTailX0RatChunk001Sub000Block000Mid + surrogateDiagTailX0RatChunk001Sub000Block000Tail =
      surrogateDiagTailX0RatChunk001Sub000Block000 := by
  unfold surrogateDiagTailX0RatChunk001Sub000Block000Head surrogateDiagTailX0RatChunk001Sub000Block000Mid surrogateDiagTailX0RatChunk001Sub000Block000Tail surrogateDiagTailX0RatChunk001Sub000Block000
  ring

def SurrogateDiagonalTailChunk001Sub000Block000HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block000HeadSum X0 = surrogateDiagTailX0RatChunk001Sub000Block000Head

def SurrogateDiagonalTailChunk001Sub000Block000MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block000MidSum X0 = surrogateDiagTailX0RatChunk001Sub000Block000Mid

def SurrogateDiagonalTailChunk001Sub000Block000TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block000TailSum X0 = surrogateDiagTailX0RatChunk001Sub000Block000Tail

theorem surrogateDiagonalTailChunk001Sub000Block000_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk001Sub000Block000HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk001Sub000Block000MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk001Sub000Block000TailCertificateAt X0) :
    surrogateDiagonalTailChunk001Sub000Block000Sum X0 = surrogateDiagTailX0RatChunk001Sub000Block000 := by
  unfold SurrogateDiagonalTailChunk001Sub000Block000HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk001Sub000Block000MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk001Sub000Block000TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk001Sub000Block000Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk001Sub000Block000_eq_head_add_mid_add_tail

/-- Block 001 covers tail-support indices [10025,10050) and q from 16538 to 16581. -/

def TailChunk001Sub000Block001Part000SupportExplicit : Finset ℕ :=
  ([16538] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block001Part000 : ℚ :=
  (1068380640625 : ℚ) / 2921250094011523872

def SurrogateDiagonalTailChunk001Sub000Block001Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16538
    = surrogateDiagTailX0RatChunk001Sub000Block001Part000

theorem surrogateDiagonalTailChunk001Sub000Block001Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block001Part000CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block001Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block001Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block001Part000CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block001Part000SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block001Part000] using hcert

def TailChunk001Sub000Block001Part001SupportExplicit : Finset ℕ :=
  ([16539] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block001Part001 : ℚ :=
  (209665429225 : ℚ) / 3582293761520566272

def SurrogateDiagonalTailChunk001Sub000Block001Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16539
    = surrogateDiagTailX0RatChunk001Sub000Block001Part001

theorem surrogateDiagonalTailChunk001Sub000Block001Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block001Part001CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block001Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block001Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block001Part001CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block001Part001SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block001Part001] using hcert

def TailChunk001Sub000Block001Part002SupportExplicit : Finset ℕ :=
  ([16541] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block001Part002 : ℚ :=
  (929569054375 : ℚ) / 77024366778812203008

def SurrogateDiagonalTailChunk001Sub000Block001Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16541
    = surrogateDiagTailX0RatChunk001Sub000Block001Part002

theorem surrogateDiagonalTailChunk001Sub000Block001Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block001Part002CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block001Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block001Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block001Part002CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block001Part002SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block001Part002] using hcert

def TailChunk001Sub000Block001Part003SupportExplicit : Finset ℕ :=
  ([16543] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block001Part003 : ℚ :=
  (1908939503 : ℚ) / 3478571657904537600

def SurrogateDiagonalTailChunk001Sub000Block001Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16543
    = surrogateDiagTailX0RatChunk001Sub000Block001Part003

theorem surrogateDiagonalTailChunk001Sub000Block001Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block001Part003CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block001Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block001Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block001Part003CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block001Part003SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block001Part003] using hcert

def TailChunk001Sub000Block001Part004SupportExplicit : Finset ℕ :=
  ([16545] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block001Part004 : ℚ :=
  (104524780675 : ℚ) / 944046099603867648

def SurrogateDiagonalTailChunk001Sub000Block001Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16545
    = surrogateDiagTailX0RatChunk001Sub000Block001Part004

theorem surrogateDiagonalTailChunk001Sub000Block001Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block001Part004CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block001Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block001Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block001Part004CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block001Part004SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block001Part004] using hcert

def TailChunk001Sub000Block001Part005SupportExplicit : Finset ℕ :=
  ([16546] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block001Part005 : ℚ :=
  (1069414515625 : ℚ) / 2926907318390956032

def SurrogateDiagonalTailChunk001Sub000Block001Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16546
    = surrogateDiagTailX0RatChunk001Sub000Block001Part005

theorem surrogateDiagonalTailChunk001Sub000Block001Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block001Part005CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block001Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block001Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block001Part005CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block001Part005SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block001Part005] using hcert

def TailChunk001Sub000Block001Part006SupportExplicit : Finset ℕ :=
  ([16547] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block001Part006 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block001Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16547
    = surrogateDiagTailX0RatChunk001Sub000Block001Part006

theorem surrogateDiagonalTailChunk001Sub000Block001Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block001Part006CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block001Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block001Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block001Part006CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block001Part006SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block001Part006] using hcert

def TailChunk001Sub000Block001Part007SupportExplicit : Finset ℕ :=
  ([16549] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block001Part007 : ℚ :=
  (633382407175 : ℚ) / 103280327322735771648

def SurrogateDiagonalTailChunk001Sub000Block001Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16549
    = surrogateDiagTailX0RatChunk001Sub000Block001Part007

theorem surrogateDiagonalTailChunk001Sub000Block001Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block001Part007CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block001Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block001Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block001Part007CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block001Part007SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block001Part007] using hcert

def TailChunk001Sub000Block001Part008SupportExplicit : Finset ℕ :=
  ([16553] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block001Part008 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block001Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16553
    = surrogateDiagTailX0RatChunk001Sub000Block001Part008

theorem surrogateDiagonalTailChunk001Sub000Block001Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block001Part008CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block001Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block001Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block001Part008CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block001Part008SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block001Part008] using hcert

def TailChunk001Sub000Block001Part009SupportExplicit : Finset ℕ :=
  ([16554] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block001Part009 : ℚ :=
  (89983937941 : ℚ) / 77736062759731200

def SurrogateDiagonalTailChunk001Sub000Block001Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16554
    = surrogateDiagTailX0RatChunk001Sub000Block001Part009

theorem surrogateDiagonalTailChunk001Sub000Block001Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block001Part009CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block001Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block001Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block001Part009CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block001Part009SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block001Part009] using hcert

def TailChunk001Sub000Block001Part010SupportExplicit : Finset ℕ :=
  ([16555] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block001Part010 : ℚ :=
  (2246643769 : ℚ) / 49171072824115200

def SurrogateDiagonalTailChunk001Sub000Block001Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16555
    = surrogateDiagTailX0RatChunk001Sub000Block001Part010

theorem surrogateDiagonalTailChunk001Sub000Block001Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block001Part010CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block001Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block001Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block001Part010CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block001Part010SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block001Part010] using hcert

def TailChunk001Sub000Block001Part011SupportExplicit : Finset ℕ :=
  ([16557] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block001Part011 : ℚ :=
  (951822649775 : ℚ) / 18545717089917155904

def SurrogateDiagonalTailChunk001Sub000Block001Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16557
    = surrogateDiagTailX0RatChunk001Sub000Block001Part011

theorem surrogateDiagonalTailChunk001Sub000Block001Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block001Part011CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block001Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block001Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block001Part011CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block001Part011SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block001Part011] using hcert

def TailChunk001Sub000Block001Part012SupportExplicit : Finset ℕ :=
  ([16558] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block001Part012 : ℚ :=
  (4761077825 : ℚ) / 285694505605545984

def SurrogateDiagonalTailChunk001Sub000Block001Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16558
    = surrogateDiagTailX0RatChunk001Sub000Block001Part012

theorem surrogateDiagonalTailChunk001Sub000Block001Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block001Part012CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block001Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block001Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block001Part012CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block001Part012SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block001Part012] using hcert

def TailChunk001Sub000Block001Part013SupportExplicit : Finset ℕ :=
  ([16559] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block001Part013 : ℚ :=
  (3823906973 : ℚ) / 3244803506263065600

def SurrogateDiagonalTailChunk001Sub000Block001Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16559
    = surrogateDiagTailX0RatChunk001Sub000Block001Part013

theorem surrogateDiagonalTailChunk001Sub000Block001Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block001Part013CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block001Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block001Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block001Part013CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block001Part013SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block001Part013] using hcert

def TailChunk001Sub000Block001Part014SupportExplicit : Finset ℕ :=
  ([16561] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block001Part014 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block001Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16561
    = surrogateDiagTailX0RatChunk001Sub000Block001Part014

theorem surrogateDiagonalTailChunk001Sub000Block001Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block001Part014CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block001Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block001Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block001Part014CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block001Part014SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block001Part014] using hcert

def TailChunk001Sub000Block001Part015SupportExplicit : Finset ℕ :=
  ([16563] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block001Part015 : ℚ :=
  (3810050099 : ℚ) / 74290477217218560

def SurrogateDiagonalTailChunk001Sub000Block001Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16563
    = surrogateDiagTailX0RatChunk001Sub000Block001Part015

theorem surrogateDiagonalTailChunk001Sub000Block001Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block001Part015CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block001Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block001Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block001Part015CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block001Part015SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block001Part015] using hcert

def TailChunk001Sub000Block001Part016SupportExplicit : Finset ℕ :=
  ([16565] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block001Part016 : ℚ :=
  (457381299175 : ℚ) / 25674788926270734336

def SurrogateDiagonalTailChunk001Sub000Block001Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16565
    = surrogateDiagTailX0RatChunk001Sub000Block001Part016

theorem surrogateDiagonalTailChunk001Sub000Block001Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block001Part016CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block001Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block001Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block001Part016CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block001Part016SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block001Part016] using hcert

def TailChunk001Sub000Block001Part017SupportExplicit : Finset ℕ :=
  ([16566] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block001Part017 : ℚ :=
  (21501259807 : ℚ) / 62512500000000000

def SurrogateDiagonalTailChunk001Sub000Block001Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16566
    = surrogateDiagTailX0RatChunk001Sub000Block001Part017

theorem surrogateDiagonalTailChunk001Sub000Block001Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block001Part017CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block001Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block001Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block001Part017CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block001Part017SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block001Part017] using hcert

def TailChunk001Sub000Block001Part018SupportExplicit : Finset ℕ :=
  ([16567] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block001Part018 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block001Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16567
    = surrogateDiagTailX0RatChunk001Sub000Block001Part018

theorem surrogateDiagonalTailChunk001Sub000Block001Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block001Part018CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block001Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block001Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block001Part018CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block001Part018SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block001Part018] using hcert

def TailChunk001Sub000Block001Part019SupportExplicit : Finset ℕ :=
  ([16570] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block001Part019 : ℚ :=
  (257616258725 : ℚ) / 2407011461837881344

def SurrogateDiagonalTailChunk001Sub000Block001Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16570
    = surrogateDiagTailX0RatChunk001Sub000Block001Part019

theorem surrogateDiagonalTailChunk001Sub000Block001Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block001Part019CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block001Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block001Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block001Part019CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block001Part019SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block001Part019] using hcert

def TailChunk001Sub000Block001Part020SupportExplicit : Finset ℕ :=
  ([16571] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block001Part020 : ℚ :=
  (92279803075 : ℚ) / 175303505718166192128

def SurrogateDiagonalTailChunk001Sub000Block001Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16571
    = surrogateDiagTailX0RatChunk001Sub000Block001Part020

theorem surrogateDiagonalTailChunk001Sub000Block001Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block001Part020CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block001Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block001Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block001Part020CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block001Part020SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block001Part020] using hcert

def TailChunk001Sub000Block001Part021SupportExplicit : Finset ℕ :=
  ([16573] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block001Part021 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block001Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16573
    = surrogateDiagTailX0RatChunk001Sub000Block001Part021

theorem surrogateDiagonalTailChunk001Sub000Block001Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block001Part021CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block001Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block001Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block001Part021CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block001Part021SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block001Part021] using hcert

def TailChunk001Sub000Block001Part022SupportExplicit : Finset ℕ :=
  ([16574] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block001Part022 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block001Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16574
    = surrogateDiagTailX0RatChunk001Sub000Block001Part022

theorem surrogateDiagonalTailChunk001Sub000Block001Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block001Part022CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block001Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block001Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block001Part022CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block001Part022SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block001Part022] using hcert

def TailChunk001Sub000Block001Part023SupportExplicit : Finset ℕ :=
  ([16579] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block001Part023 : ℚ :=
  (4243083427 : ℚ) / 6957143315809075200

def SurrogateDiagonalTailChunk001Sub000Block001Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16579
    = surrogateDiagTailX0RatChunk001Sub000Block001Part023

theorem surrogateDiagonalTailChunk001Sub000Block001Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block001Part023CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block001Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block001Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block001Part023CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block001Part023SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block001Part023] using hcert

def TailChunk001Sub000Block001Part024SupportExplicit : Finset ℕ :=
  ([16581] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block001Part024 : ℚ :=
  (954583649675 : ℚ) / 18653501576904035904

def SurrogateDiagonalTailChunk001Sub000Block001Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16581
    = surrogateDiagTailX0RatChunk001Sub000Block001Part024

theorem surrogateDiagonalTailChunk001Sub000Block001Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block001Part024CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block001Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block001Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block001Part024CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block001Part024SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block001Part024] using hcert

def surrogateDiagonalTailChunk001Sub000Block001HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block001Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block001Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block001Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block001Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block001Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block001Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block001Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block001Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block001Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block001Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block001Head : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block001Part000
    + surrogateDiagTailX0RatChunk001Sub000Block001Part001
    + surrogateDiagTailX0RatChunk001Sub000Block001Part002
    + surrogateDiagTailX0RatChunk001Sub000Block001Part003
    + surrogateDiagTailX0RatChunk001Sub000Block001Part004
    + surrogateDiagTailX0RatChunk001Sub000Block001Part005
    + surrogateDiagTailX0RatChunk001Sub000Block001Part006
    + surrogateDiagTailX0RatChunk001Sub000Block001Part007
    + surrogateDiagTailX0RatChunk001Sub000Block001Part008
    + surrogateDiagTailX0RatChunk001Sub000Block001Part009

def surrogateDiagonalTailChunk001Sub000Block001MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block001Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block001Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block001Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block001Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block001Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block001Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block001Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block001Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block001Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block001Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block001Mid : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block001Part010
    + surrogateDiagTailX0RatChunk001Sub000Block001Part011
    + surrogateDiagTailX0RatChunk001Sub000Block001Part012
    + surrogateDiagTailX0RatChunk001Sub000Block001Part013
    + surrogateDiagTailX0RatChunk001Sub000Block001Part014
    + surrogateDiagTailX0RatChunk001Sub000Block001Part015
    + surrogateDiagTailX0RatChunk001Sub000Block001Part016
    + surrogateDiagTailX0RatChunk001Sub000Block001Part017
    + surrogateDiagTailX0RatChunk001Sub000Block001Part018
    + surrogateDiagTailX0RatChunk001Sub000Block001Part019

def surrogateDiagonalTailChunk001Sub000Block001TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block001Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block001Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block001Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block001Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block001Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block001Tail : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block001Part020
    + surrogateDiagTailX0RatChunk001Sub000Block001Part021
    + surrogateDiagTailX0RatChunk001Sub000Block001Part022
    + surrogateDiagTailX0RatChunk001Sub000Block001Part023
    + surrogateDiagTailX0RatChunk001Sub000Block001Part024

def surrogateDiagonalTailChunk001Sub000Block001Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk001Sub000Block001HeadSum X0
    + surrogateDiagonalTailChunk001Sub000Block001MidSum X0
    + surrogateDiagonalTailChunk001Sub000Block001TailSum X0

def surrogateDiagTailX0RatChunk001Sub000Block001 : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block001Part000
    + surrogateDiagTailX0RatChunk001Sub000Block001Part001
    + surrogateDiagTailX0RatChunk001Sub000Block001Part002
    + surrogateDiagTailX0RatChunk001Sub000Block001Part003
    + surrogateDiagTailX0RatChunk001Sub000Block001Part004
    + surrogateDiagTailX0RatChunk001Sub000Block001Part005
    + surrogateDiagTailX0RatChunk001Sub000Block001Part006
    + surrogateDiagTailX0RatChunk001Sub000Block001Part007
    + surrogateDiagTailX0RatChunk001Sub000Block001Part008
    + surrogateDiagTailX0RatChunk001Sub000Block001Part009
    + surrogateDiagTailX0RatChunk001Sub000Block001Part010
    + surrogateDiagTailX0RatChunk001Sub000Block001Part011
    + surrogateDiagTailX0RatChunk001Sub000Block001Part012
    + surrogateDiagTailX0RatChunk001Sub000Block001Part013
    + surrogateDiagTailX0RatChunk001Sub000Block001Part014
    + surrogateDiagTailX0RatChunk001Sub000Block001Part015
    + surrogateDiagTailX0RatChunk001Sub000Block001Part016
    + surrogateDiagTailX0RatChunk001Sub000Block001Part017
    + surrogateDiagTailX0RatChunk001Sub000Block001Part018
    + surrogateDiagTailX0RatChunk001Sub000Block001Part019
    + surrogateDiagTailX0RatChunk001Sub000Block001Part020
    + surrogateDiagTailX0RatChunk001Sub000Block001Part021
    + surrogateDiagTailX0RatChunk001Sub000Block001Part022
    + surrogateDiagTailX0RatChunk001Sub000Block001Part023
    + surrogateDiagTailX0RatChunk001Sub000Block001Part024

theorem surrogateDiagTailX0RatChunk001Sub000Block001_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk001Sub000Block001Head + surrogateDiagTailX0RatChunk001Sub000Block001Mid + surrogateDiagTailX0RatChunk001Sub000Block001Tail =
      surrogateDiagTailX0RatChunk001Sub000Block001 := by
  unfold surrogateDiagTailX0RatChunk001Sub000Block001Head surrogateDiagTailX0RatChunk001Sub000Block001Mid surrogateDiagTailX0RatChunk001Sub000Block001Tail surrogateDiagTailX0RatChunk001Sub000Block001
  ring

def SurrogateDiagonalTailChunk001Sub000Block001HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block001HeadSum X0 = surrogateDiagTailX0RatChunk001Sub000Block001Head

def SurrogateDiagonalTailChunk001Sub000Block001MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block001MidSum X0 = surrogateDiagTailX0RatChunk001Sub000Block001Mid

def SurrogateDiagonalTailChunk001Sub000Block001TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block001TailSum X0 = surrogateDiagTailX0RatChunk001Sub000Block001Tail

theorem surrogateDiagonalTailChunk001Sub000Block001_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk001Sub000Block001HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk001Sub000Block001MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk001Sub000Block001TailCertificateAt X0) :
    surrogateDiagonalTailChunk001Sub000Block001Sum X0 = surrogateDiagTailX0RatChunk001Sub000Block001 := by
  unfold SurrogateDiagonalTailChunk001Sub000Block001HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk001Sub000Block001MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk001Sub000Block001TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk001Sub000Block001Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk001Sub000Block001_eq_head_add_mid_add_tail

/-- Block 002 covers tail-support indices [10050,10075) and q from 16582 to 16621. -/

def TailChunk001Sub000Block002Part000SupportExplicit : Finset ℕ :=
  ([16582] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block002Part000 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block002Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16582
    = surrogateDiagTailX0RatChunk001Sub000Block002Part000

theorem surrogateDiagonalTailChunk001Sub000Block002Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block002Part000CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block002Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block002Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block002Part000CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block002Part000SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block002Part000] using hcert

def TailChunk001Sub000Block002Part001SupportExplicit : Finset ℕ :=
  ([16583] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block002Part001 : ℚ :=
  (859643273725 : ℚ) / 82171888987218167808

def SurrogateDiagonalTailChunk001Sub000Block002Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16583
    = surrogateDiagTailX0RatChunk001Sub000Block002Part001

theorem surrogateDiagonalTailChunk001Sub000Block002Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block002Part001CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block002Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block002Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block002Part001CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block002Part001SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block002Part001] using hcert

def TailChunk001Sub000Block002Part002SupportExplicit : Finset ℕ :=
  ([16585] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block002Part002 : ℚ :=
  (1904256391 : ℚ) / 87279859956695040

def SurrogateDiagonalTailChunk001Sub000Block002Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16585
    = surrogateDiagTailX0RatChunk001Sub000Block002Part002

theorem surrogateDiagonalTailChunk001Sub000Block002Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block002Part002CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block002Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block002Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block002Part002CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block002Part002SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block002Part002] using hcert

def TailChunk001Sub000Block002Part003SupportExplicit : Finset ℕ :=
  ([16586] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block002Part003 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block002Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16586
    = surrogateDiagTailX0RatChunk001Sub000Block002Part003

theorem surrogateDiagonalTailChunk001Sub000Block002Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block002Part003CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block002Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block002Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block002Part003CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block002Part003SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block002Part003] using hcert

def TailChunk001Sub000Block002Part004SupportExplicit : Finset ℕ :=
  ([16589] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block002Part004 : ℚ :=
  (113409593875 : ℚ) / 173244162346005823488

def SurrogateDiagonalTailChunk001Sub000Block002Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16589
    = surrogateDiagTailX0RatChunk001Sub000Block002Part004

theorem surrogateDiagonalTailChunk001Sub000Block002Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block002Part004CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block002Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block002Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block002Part004CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block002Part004SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block002Part004] using hcert

def TailChunk001Sub000Block002Part005SupportExplicit : Finset ℕ :=
  ([16590] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block002Part005 : ℚ :=
  (861004289875 : ℚ) / 491326534435995648

def SurrogateDiagonalTailChunk001Sub000Block002Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16590
    = surrogateDiagTailX0RatChunk001Sub000Block002Part005

theorem surrogateDiagonalTailChunk001Sub000Block002Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block002Part005CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block002Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block002Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block002Part005CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block002Part005SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block002Part005] using hcert

def TailChunk001Sub000Block002Part006SupportExplicit : Finset ℕ :=
  ([16591] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block002Part006 : ℚ :=
  (10205096775 : ℚ) / 14323448585182511104

def SurrogateDiagonalTailChunk001Sub000Block002Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16591
    = surrogateDiagTailX0RatChunk001Sub000Block002Part006

theorem surrogateDiagonalTailChunk001Sub000Block002Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block002Part006CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block002Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block002Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block002Part006CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block002Part006SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block002Part006] using hcert

def TailChunk001Sub000Block002Part007SupportExplicit : Finset ℕ :=
  ([16593] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block002Part007 : ℚ :=
  (1092532171 : ℚ) / 21380079613690560

def SurrogateDiagonalTailChunk001Sub000Block002Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16593
    = surrogateDiagTailX0RatChunk001Sub000Block002Part007

theorem surrogateDiagonalTailChunk001Sub000Block002Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block002Part007CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block002Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block002Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block002Part007CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block002Part007SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block002Part007] using hcert

def TailChunk001Sub000Block002Part008SupportExplicit : Finset ℕ :=
  ([16594] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block002Part008 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block002Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16594
    = surrogateDiagTailX0RatChunk001Sub000Block002Part008

theorem surrogateDiagonalTailChunk001Sub000Block002Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block002Part008CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block002Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block002Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block002Part008CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block002Part008SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block002Part008] using hcert

def TailChunk001Sub000Block002Part009SupportExplicit : Finset ℕ :=
  ([16595] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block002Part009 : ℚ :=
  (459038467075 : ℚ) / 25861344300720101376

def SurrogateDiagonalTailChunk001Sub000Block002Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16595
    = surrogateDiagTailX0RatChunk001Sub000Block002Part009

theorem surrogateDiagonalTailChunk001Sub000Block002Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block002Part009CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block002Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block002Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block002Part009CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block002Part009SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block002Part009] using hcert

def TailChunk001Sub000Block002Part010SupportExplicit : Finset ℕ :=
  ([16597] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block002Part010 : ℚ :=
  (14076937667 : ℚ) / 2044820733898305600

def SurrogateDiagonalTailChunk001Sub000Block002Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16597
    = surrogateDiagTailX0RatChunk001Sub000Block002Part010

theorem surrogateDiagonalTailChunk001Sub000Block002Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block002Part010CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block002Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block002Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block002Part010CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block002Part010SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block002Part010] using hcert

def TailChunk001Sub000Block002Part011SupportExplicit : Finset ℕ :=
  ([16598] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block002Part011 : ℚ :=
  (72802967575 : ℚ) / 10573747500097732608

def SurrogateDiagonalTailChunk001Sub000Block002Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16598
    = surrogateDiagTailX0RatChunk001Sub000Block002Part011

theorem surrogateDiagonalTailChunk001Sub000Block002Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block002Part011CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block002Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block002Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block002Part011CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block002Part011SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block002Part011] using hcert

def TailChunk001Sub000Block002Part012SupportExplicit : Finset ℕ :=
  ([16599] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block002Part012 : ℚ :=
  (24653593101 : ℚ) / 338766491835750400

def SurrogateDiagonalTailChunk001Sub000Block002Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16599
    = surrogateDiagTailX0RatChunk001Sub000Block002Part012

theorem surrogateDiagonalTailChunk001Sub000Block002Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block002Part012CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block002Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block002Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block002Part012CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block002Part012SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block002Part012] using hcert

def TailChunk001Sub000Block002Part013SupportExplicit : Finset ℕ :=
  ([16601] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block002Part013 : ℚ :=
  (68425458775 : ℚ) / 22908850085318934528

def SurrogateDiagonalTailChunk001Sub000Block002Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16601
    = surrogateDiagTailX0RatChunk001Sub000Block002Part013

theorem surrogateDiagonalTailChunk001Sub000Block002Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block002Part013CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block002Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block002Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block002Part013CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block002Part013SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block002Part013] using hcert

def TailChunk001Sub000Block002Part014SupportExplicit : Finset ℕ :=
  ([16602] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block002Part014 : ℚ :=
  (478389039725 : ℚ) / 1170915483700206144

def SurrogateDiagonalTailChunk001Sub000Block002Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16602
    = surrogateDiagTailX0RatChunk001Sub000Block002Part014

theorem surrogateDiagonalTailChunk001Sub000Block002Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block002Part014CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block002Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block002Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block002Part014CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block002Part014SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block002Part014] using hcert

def TailChunk001Sub000Block002Part015SupportExplicit : Finset ℕ :=
  ([16603] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block002Part015 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block002Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16603
    = surrogateDiagTailX0RatChunk001Sub000Block002Part015

theorem surrogateDiagonalTailChunk001Sub000Block002Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block002Part015CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block002Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block002Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block002Part015CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block002Part015SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block002Part015] using hcert

def TailChunk001Sub000Block002Part016SupportExplicit : Finset ℕ :=
  ([16607] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block002Part016 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block002Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16607
    = surrogateDiagTailX0RatChunk001Sub000Block002Part016

theorem surrogateDiagonalTailChunk001Sub000Block002Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block002Part016CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block002Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block002Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block002Part016CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block002Part016SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block002Part016] using hcert

def TailChunk001Sub000Block002Part017SupportExplicit : Finset ℕ :=
  ([16609] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block002Part017 : ℚ :=
  (302440486525 : ℚ) / 148698319418680147968

def SurrogateDiagonalTailChunk001Sub000Block002Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16609
    = surrogateDiagTailX0RatChunk001Sub000Block002Part017

theorem surrogateDiagonalTailChunk001Sub000Block002Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block002Part017CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block002Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block002Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block002Part017CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block002Part017SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block002Part017] using hcert

def TailChunk001Sub000Block002Part018SupportExplicit : Finset ℕ :=
  ([16610] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block002Part018 : ℚ :=
  (482380451 : ℚ) / 2592518400000000

def SurrogateDiagonalTailChunk001Sub000Block002Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16610
    = surrogateDiagTailX0RatChunk001Sub000Block002Part018

theorem surrogateDiagonalTailChunk001Sub000Block002Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block002Part018CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block002Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block002Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block002Part018CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block002Part018SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block002Part018] using hcert

def TailChunk001Sub000Block002Part019SupportExplicit : Finset ℕ :=
  ([16613] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block002Part019 : ℚ :=
  (21278300125 : ℚ) / 24168565714509103104

def SurrogateDiagonalTailChunk001Sub000Block002Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16613
    = surrogateDiagTailX0RatChunk001Sub000Block002Part019

theorem surrogateDiagonalTailChunk001Sub000Block002Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block002Part019CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block002Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block002Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block002Part019CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block002Part019SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block002Part019] using hcert

def TailChunk001Sub000Block002Part020SupportExplicit : Finset ℕ :=
  ([16615] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block002Part020 : ℚ :=
  (230327007375 : ℚ) / 25986278103920121856

def SurrogateDiagonalTailChunk001Sub000Block002Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16615
    = surrogateDiagTailX0RatChunk001Sub000Block002Part020

theorem surrogateDiagonalTailChunk001Sub000Block002Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block002Part020CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block002Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block002Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block002Part020CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block002Part020SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block002Part020] using hcert

def TailChunk001Sub000Block002Part021SupportExplicit : Finset ℕ :=
  ([16617] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block002Part021 : ℚ :=
  (76142315467 : ℚ) / 1281897681486643200

def SurrogateDiagonalTailChunk001Sub000Block002Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16617
    = surrogateDiagTailX0RatChunk001Sub000Block002Part021

theorem surrogateDiagonalTailChunk001Sub000Block002Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block002Part021CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block002Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block002Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block002Part021CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block002Part021SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block002Part021] using hcert

def TailChunk001Sub000Block002Part022SupportExplicit : Finset ℕ :=
  ([16618] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block002Part022 : ℚ :=
  (353312454325 : ℚ) / 6411661951354915968

def SurrogateDiagonalTailChunk001Sub000Block002Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16618
    = surrogateDiagTailX0RatChunk001Sub000Block002Part022

theorem surrogateDiagonalTailChunk001Sub000Block002Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block002Part022CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block002Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block002Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block002Part022CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block002Part022SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block002Part022] using hcert

def TailChunk001Sub000Block002Part023SupportExplicit : Finset ℕ :=
  ([16619] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block002Part023 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block002Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16619
    = surrogateDiagTailX0RatChunk001Sub000Block002Part023

theorem surrogateDiagonalTailChunk001Sub000Block002Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block002Part023CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block002Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block002Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block002Part023CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block002Part023SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block002Part023] using hcert

def TailChunk001Sub000Block002Part024SupportExplicit : Finset ℕ :=
  ([16621] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block002Part024 : ℚ :=
  (7637467023 : ℚ) / 1733298593734000000

def SurrogateDiagonalTailChunk001Sub000Block002Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16621
    = surrogateDiagTailX0RatChunk001Sub000Block002Part024

theorem surrogateDiagonalTailChunk001Sub000Block002Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block002Part024CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block002Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block002Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block002Part024CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block002Part024SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block002Part024] using hcert

def surrogateDiagonalTailChunk001Sub000Block002HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block002Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block002Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block002Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block002Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block002Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block002Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block002Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block002Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block002Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block002Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block002Head : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block002Part000
    + surrogateDiagTailX0RatChunk001Sub000Block002Part001
    + surrogateDiagTailX0RatChunk001Sub000Block002Part002
    + surrogateDiagTailX0RatChunk001Sub000Block002Part003
    + surrogateDiagTailX0RatChunk001Sub000Block002Part004
    + surrogateDiagTailX0RatChunk001Sub000Block002Part005
    + surrogateDiagTailX0RatChunk001Sub000Block002Part006
    + surrogateDiagTailX0RatChunk001Sub000Block002Part007
    + surrogateDiagTailX0RatChunk001Sub000Block002Part008
    + surrogateDiagTailX0RatChunk001Sub000Block002Part009

def surrogateDiagonalTailChunk001Sub000Block002MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block002Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block002Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block002Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block002Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block002Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block002Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block002Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block002Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block002Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block002Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block002Mid : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block002Part010
    + surrogateDiagTailX0RatChunk001Sub000Block002Part011
    + surrogateDiagTailX0RatChunk001Sub000Block002Part012
    + surrogateDiagTailX0RatChunk001Sub000Block002Part013
    + surrogateDiagTailX0RatChunk001Sub000Block002Part014
    + surrogateDiagTailX0RatChunk001Sub000Block002Part015
    + surrogateDiagTailX0RatChunk001Sub000Block002Part016
    + surrogateDiagTailX0RatChunk001Sub000Block002Part017
    + surrogateDiagTailX0RatChunk001Sub000Block002Part018
    + surrogateDiagTailX0RatChunk001Sub000Block002Part019

def surrogateDiagonalTailChunk001Sub000Block002TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block002Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block002Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block002Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block002Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block002Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block002Tail : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block002Part020
    + surrogateDiagTailX0RatChunk001Sub000Block002Part021
    + surrogateDiagTailX0RatChunk001Sub000Block002Part022
    + surrogateDiagTailX0RatChunk001Sub000Block002Part023
    + surrogateDiagTailX0RatChunk001Sub000Block002Part024

def surrogateDiagonalTailChunk001Sub000Block002Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk001Sub000Block002HeadSum X0
    + surrogateDiagonalTailChunk001Sub000Block002MidSum X0
    + surrogateDiagonalTailChunk001Sub000Block002TailSum X0

def surrogateDiagTailX0RatChunk001Sub000Block002 : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block002Part000
    + surrogateDiagTailX0RatChunk001Sub000Block002Part001
    + surrogateDiagTailX0RatChunk001Sub000Block002Part002
    + surrogateDiagTailX0RatChunk001Sub000Block002Part003
    + surrogateDiagTailX0RatChunk001Sub000Block002Part004
    + surrogateDiagTailX0RatChunk001Sub000Block002Part005
    + surrogateDiagTailX0RatChunk001Sub000Block002Part006
    + surrogateDiagTailX0RatChunk001Sub000Block002Part007
    + surrogateDiagTailX0RatChunk001Sub000Block002Part008
    + surrogateDiagTailX0RatChunk001Sub000Block002Part009
    + surrogateDiagTailX0RatChunk001Sub000Block002Part010
    + surrogateDiagTailX0RatChunk001Sub000Block002Part011
    + surrogateDiagTailX0RatChunk001Sub000Block002Part012
    + surrogateDiagTailX0RatChunk001Sub000Block002Part013
    + surrogateDiagTailX0RatChunk001Sub000Block002Part014
    + surrogateDiagTailX0RatChunk001Sub000Block002Part015
    + surrogateDiagTailX0RatChunk001Sub000Block002Part016
    + surrogateDiagTailX0RatChunk001Sub000Block002Part017
    + surrogateDiagTailX0RatChunk001Sub000Block002Part018
    + surrogateDiagTailX0RatChunk001Sub000Block002Part019
    + surrogateDiagTailX0RatChunk001Sub000Block002Part020
    + surrogateDiagTailX0RatChunk001Sub000Block002Part021
    + surrogateDiagTailX0RatChunk001Sub000Block002Part022
    + surrogateDiagTailX0RatChunk001Sub000Block002Part023
    + surrogateDiagTailX0RatChunk001Sub000Block002Part024

theorem surrogateDiagTailX0RatChunk001Sub000Block002_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk001Sub000Block002Head + surrogateDiagTailX0RatChunk001Sub000Block002Mid + surrogateDiagTailX0RatChunk001Sub000Block002Tail =
      surrogateDiagTailX0RatChunk001Sub000Block002 := by
  unfold surrogateDiagTailX0RatChunk001Sub000Block002Head surrogateDiagTailX0RatChunk001Sub000Block002Mid surrogateDiagTailX0RatChunk001Sub000Block002Tail surrogateDiagTailX0RatChunk001Sub000Block002
  ring

def SurrogateDiagonalTailChunk001Sub000Block002HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block002HeadSum X0 = surrogateDiagTailX0RatChunk001Sub000Block002Head

def SurrogateDiagonalTailChunk001Sub000Block002MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block002MidSum X0 = surrogateDiagTailX0RatChunk001Sub000Block002Mid

def SurrogateDiagonalTailChunk001Sub000Block002TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block002TailSum X0 = surrogateDiagTailX0RatChunk001Sub000Block002Tail

theorem surrogateDiagonalTailChunk001Sub000Block002_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk001Sub000Block002HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk001Sub000Block002MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk001Sub000Block002TailCertificateAt X0) :
    surrogateDiagonalTailChunk001Sub000Block002Sum X0 = surrogateDiagTailX0RatChunk001Sub000Block002 := by
  unfold SurrogateDiagonalTailChunk001Sub000Block002HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk001Sub000Block002MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk001Sub000Block002TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk001Sub000Block002Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk001Sub000Block002_eq_head_add_mid_add_tail

/-- Block 003 covers tail-support indices [10075,10100) and q from 16622 to 16661. -/

def TailChunk001Sub000Block003Part000SupportExplicit : Finset ℕ :=
  ([16622] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block003Part000 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block003Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16622
    = surrogateDiagTailX0RatChunk001Sub000Block003Part000

theorem surrogateDiagonalTailChunk001Sub000Block003Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block003Part000CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block003Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block003Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block003Part000CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block003Part000SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block003Part000] using hcert

def TailChunk001Sub000Block003Part001SupportExplicit : Finset ℕ :=
  ([16626] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block003Part001 : ℚ :=
  (315457025225 : ℚ) / 601957147613331456

def SurrogateDiagonalTailChunk001Sub000Block003Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16626
    = surrogateDiagTailX0RatChunk001Sub000Block003Part001

theorem surrogateDiagonalTailChunk001Sub000Block003Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block003Part001CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block003Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block003Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block003Part001CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block003Part001SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block003Part001] using hcert

def TailChunk001Sub000Block003Part002SupportExplicit : Finset ℕ :=
  ([16627] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block003Part002 : ℚ :=
  (205914492425 : ℚ) / 69158451835665736704

def SurrogateDiagonalTailChunk001Sub000Block003Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16627
    = surrogateDiagTailX0RatChunk001Sub000Block003Part002

theorem surrogateDiagonalTailChunk001Sub000Block003Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block003Part002CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block003Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block003Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block003Part002CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block003Part002SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block003Part002] using hcert

def TailChunk001Sub000Block003Part003SupportExplicit : Finset ℕ :=
  ([16629] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block003Part003 : ℚ :=
  (235020167 : ℚ) / 3838817914060800

def SurrogateDiagonalTailChunk001Sub000Block003Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16629
    = surrogateDiagTailX0RatChunk001Sub000Block003Part003

theorem surrogateDiagonalTailChunk001Sub000Block003Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block003Part003CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block003Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block003Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block003Part003CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block003Part003SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block003Part003] using hcert

def TailChunk001Sub000Block003Part004SupportExplicit : Finset ℕ :=
  ([16630] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block003Part004 : ℚ :=
  (8108808925 : ℚ) / 76315179139191072

def SurrogateDiagonalTailChunk001Sub000Block003Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16630
    = surrogateDiagTailX0RatChunk001Sub000Block003Part004

theorem surrogateDiagonalTailChunk001Sub000Block003Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block003Part004CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block003Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block003Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block003Part004CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block003Part004SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block003Part004] using hcert

def TailChunk001Sub000Block003Part005SupportExplicit : Finset ℕ :=
  ([16631] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block003Part005 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block003Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16631
    = surrogateDiagTailX0RatChunk001Sub000Block003Part005

theorem surrogateDiagonalTailChunk001Sub000Block003Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block003Part005CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block003Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block003Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block003Part005CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block003Part005SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block003Part005] using hcert

def TailChunk001Sub000Block003Part006SupportExplicit : Finset ℕ :=
  ([16633] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block003Part006 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block003Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16633
    = surrogateDiagTailX0RatChunk001Sub000Block003Part006

theorem surrogateDiagonalTailChunk001Sub000Block003Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block003Part006CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block003Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block003Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block003Part006CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block003Part006SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block003Part006] using hcert

def TailChunk001Sub000Block003Part007SupportExplicit : Finset ℕ :=
  ([16634] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block003Part007 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block003Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16634
    = surrogateDiagTailX0RatChunk001Sub000Block003Part007

theorem surrogateDiagonalTailChunk001Sub000Block003Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block003Part007CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block003Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block003Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block003Part007CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block003Part007SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block003Part007] using hcert

def TailChunk001Sub000Block003Part008SupportExplicit : Finset ℕ :=
  ([16635] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block003Part008 : ℚ :=
  (1767481609525 : ℚ) / 15436393765635883008

def SurrogateDiagonalTailChunk001Sub000Block003Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16635
    = surrogateDiagTailX0RatChunk001Sub000Block003Part008

theorem surrogateDiagonalTailChunk001Sub000Block003Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block003Part008CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block003Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block003Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block003Part008CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block003Part008SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block003Part008] using hcert

def TailChunk001Sub000Block003Part009SupportExplicit : Finset ℕ :=
  ([16637] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block003Part009 : ℚ :=
  (1577100347 : ℚ) / 3600082425478593600

def SurrogateDiagonalTailChunk001Sub000Block003Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16637
    = surrogateDiagTailX0RatChunk001Sub000Block003Part009

theorem surrogateDiagonalTailChunk001Sub000Block003Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block003Part009CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block003Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block003Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block003Part009CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block003Part009SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block003Part009] using hcert

def TailChunk001Sub000Block003Part010SupportExplicit : Finset ℕ :=
  ([16638] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block003Part010 : ℚ :=
  (238389607825 : ℚ) / 506792467367588352

def SurrogateDiagonalTailChunk001Sub000Block003Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16638
    = surrogateDiagTailX0RatChunk001Sub000Block003Part010

theorem surrogateDiagonalTailChunk001Sub000Block003Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block003Part010CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block003Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block003Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block003Part010CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block003Part010SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block003Part010] using hcert

def TailChunk001Sub000Block003Part011SupportExplicit : Finset ℕ :=
  ([16639] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block003Part011 : ℚ :=
  (353702835875 : ℚ) / 51640163661367885824

def SurrogateDiagonalTailChunk001Sub000Block003Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16639
    = surrogateDiagTailX0RatChunk001Sub000Block003Part011

theorem surrogateDiagonalTailChunk001Sub000Block003Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block003Part011CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block003Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block003Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block003Part011CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block003Part011SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block003Part011] using hcert

def TailChunk001Sub000Block003Part012SupportExplicit : Finset ℕ :=
  ([16642] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block003Part012 : ℚ :=
  (21574946425 : ℚ) / 3609253382208454656

def SurrogateDiagonalTailChunk001Sub000Block003Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16642
    = surrogateDiagTailX0RatChunk001Sub000Block003Part012

theorem surrogateDiagonalTailChunk001Sub000Block003Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block003Part012CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block003Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block003Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block003Part012CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block003Part012SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block003Part012] using hcert

def TailChunk001Sub000Block003Part013SupportExplicit : Finset ℕ :=
  ([16643] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block003Part013 : ℚ :=
  (27506191849 : ℚ) / 3930949543998259200

def SurrogateDiagonalTailChunk001Sub000Block003Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16643
    = surrogateDiagTailX0RatChunk001Sub000Block003Part013

theorem surrogateDiagonalTailChunk001Sub000Block003Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block003Part013CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block003Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block003Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block003Part013CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block003Part013SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block003Part013] using hcert

def TailChunk001Sub000Block003Part014SupportExplicit : Finset ℕ :=
  ([16645] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block003Part014 : ℚ :=
  (231158257125 : ℚ) / 26174526859358765056

def SurrogateDiagonalTailChunk001Sub000Block003Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16645
    = surrogateDiagTailX0RatChunk001Sub000Block003Part014

theorem surrogateDiagonalTailChunk001Sub000Block003Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block003Part014CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block003Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block003Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block003Part014CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block003Part014SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block003Part014] using hcert

def TailChunk001Sub000Block003Part015SupportExplicit : Finset ℕ :=
  ([16646] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block003Part015 : ℚ :=
  (17435618269 : ℚ) / 203968894677811200

def SurrogateDiagonalTailChunk001Sub000Block003Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16646
    = surrogateDiagTailX0RatChunk001Sub000Block003Part015

theorem surrogateDiagonalTailChunk001Sub000Block003Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block003Part015CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block003Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block003Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block003Part015CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block003Part015SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block003Part015] using hcert

def TailChunk001Sub000Block003Part016SupportExplicit : Finset ℕ :=
  ([16647] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block003Part016 : ℚ :=
  (953944751 : ℚ) / 16266041424973440

def SurrogateDiagonalTailChunk001Sub000Block003Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16647
    = surrogateDiagTailX0RatChunk001Sub000Block003Part016

theorem surrogateDiagonalTailChunk001Sub000Block003Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block003Part016CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block003Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block003Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block003Part016CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block003Part016SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block003Part016] using hcert

def TailChunk001Sub000Block003Part017SupportExplicit : Finset ℕ :=
  ([16649] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block003Part017 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block003Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16649
    = surrogateDiagTailX0RatChunk001Sub000Block003Part017

theorem surrogateDiagonalTailChunk001Sub000Block003Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block003Part017CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block003Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block003Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block003Part017CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block003Part017SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block003Part017] using hcert

def TailChunk001Sub000Block003Part018SupportExplicit : Finset ℕ :=
  ([16651] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block003Part018 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block003Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16651
    = surrogateDiagTailX0RatChunk001Sub000Block003Part018

theorem surrogateDiagonalTailChunk001Sub000Block003Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block003Part018CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block003Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block003Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block003Part018CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block003Part018SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block003Part018] using hcert

def TailChunk001Sub000Block003Part019SupportExplicit : Finset ℕ :=
  ([16653] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block003Part019 : ℚ :=
  (26258187943 : ℚ) / 557367729271603200

def SurrogateDiagonalTailChunk001Sub000Block003Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16653
    = surrogateDiagTailX0RatChunk001Sub000Block003Part019

theorem surrogateDiagonalTailChunk001Sub000Block003Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block003Part019CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block003Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block003Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block003Part019CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block003Part019SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block003Part019] using hcert

def TailChunk001Sub000Block003Part020SupportExplicit : Finset ℕ :=
  ([16654] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block003Part020 : ℚ :=
  (1444991713 : ℚ) / 46674104282265600

def SurrogateDiagonalTailChunk001Sub000Block003Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16654
    = surrogateDiagTailX0RatChunk001Sub000Block003Part020

theorem surrogateDiagonalTailChunk001Sub000Block003Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block003Part020CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block003Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block003Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block003Part020CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block003Part020SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block003Part020] using hcert

def TailChunk001Sub000Block003Part021SupportExplicit : Finset ℕ :=
  ([16655] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block003Part021 : ℚ :=
  (150120437 : ℚ) / 17018920953169920

def SurrogateDiagonalTailChunk001Sub000Block003Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16655
    = surrogateDiagTailX0RatChunk001Sub000Block003Part021

theorem surrogateDiagonalTailChunk001Sub000Block003Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block003Part021CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block003Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block003Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block003Part021CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block003Part021SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block003Part021] using hcert

def TailChunk001Sub000Block003Part022SupportExplicit : Finset ℕ :=
  ([16657] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block003Part022 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block003Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16657
    = surrogateDiagTailX0RatChunk001Sub000Block003Part022

theorem surrogateDiagonalTailChunk001Sub000Block003Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block003Part022CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block003Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block003Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block003Part022CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block003Part022SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block003Part022] using hcert

def TailChunk001Sub000Block003Part023SupportExplicit : Finset ℕ :=
  ([16658] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block003Part023 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block003Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16658
    = surrogateDiagTailX0RatChunk001Sub000Block003Part023

theorem surrogateDiagonalTailChunk001Sub000Block003Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block003Part023CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block003Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block003Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block003Part023CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block003Part023SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block003Part023] using hcert

def TailChunk001Sub000Block003Part024SupportExplicit : Finset ℕ :=
  ([16661] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block003Part024 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block003Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16661
    = surrogateDiagTailX0RatChunk001Sub000Block003Part024

theorem surrogateDiagonalTailChunk001Sub000Block003Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block003Part024CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block003Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block003Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block003Part024CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block003Part024SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block003Part024] using hcert

def surrogateDiagonalTailChunk001Sub000Block003HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block003Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block003Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block003Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block003Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block003Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block003Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block003Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block003Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block003Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block003Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block003Head : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block003Part000
    + surrogateDiagTailX0RatChunk001Sub000Block003Part001
    + surrogateDiagTailX0RatChunk001Sub000Block003Part002
    + surrogateDiagTailX0RatChunk001Sub000Block003Part003
    + surrogateDiagTailX0RatChunk001Sub000Block003Part004
    + surrogateDiagTailX0RatChunk001Sub000Block003Part005
    + surrogateDiagTailX0RatChunk001Sub000Block003Part006
    + surrogateDiagTailX0RatChunk001Sub000Block003Part007
    + surrogateDiagTailX0RatChunk001Sub000Block003Part008
    + surrogateDiagTailX0RatChunk001Sub000Block003Part009

def surrogateDiagonalTailChunk001Sub000Block003MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block003Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block003Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block003Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block003Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block003Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block003Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block003Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block003Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block003Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block003Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block003Mid : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block003Part010
    + surrogateDiagTailX0RatChunk001Sub000Block003Part011
    + surrogateDiagTailX0RatChunk001Sub000Block003Part012
    + surrogateDiagTailX0RatChunk001Sub000Block003Part013
    + surrogateDiagTailX0RatChunk001Sub000Block003Part014
    + surrogateDiagTailX0RatChunk001Sub000Block003Part015
    + surrogateDiagTailX0RatChunk001Sub000Block003Part016
    + surrogateDiagTailX0RatChunk001Sub000Block003Part017
    + surrogateDiagTailX0RatChunk001Sub000Block003Part018
    + surrogateDiagTailX0RatChunk001Sub000Block003Part019

def surrogateDiagonalTailChunk001Sub000Block003TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block003Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block003Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block003Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block003Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block003Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block003Tail : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block003Part020
    + surrogateDiagTailX0RatChunk001Sub000Block003Part021
    + surrogateDiagTailX0RatChunk001Sub000Block003Part022
    + surrogateDiagTailX0RatChunk001Sub000Block003Part023
    + surrogateDiagTailX0RatChunk001Sub000Block003Part024

def surrogateDiagonalTailChunk001Sub000Block003Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk001Sub000Block003HeadSum X0
    + surrogateDiagonalTailChunk001Sub000Block003MidSum X0
    + surrogateDiagonalTailChunk001Sub000Block003TailSum X0

def surrogateDiagTailX0RatChunk001Sub000Block003 : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block003Part000
    + surrogateDiagTailX0RatChunk001Sub000Block003Part001
    + surrogateDiagTailX0RatChunk001Sub000Block003Part002
    + surrogateDiagTailX0RatChunk001Sub000Block003Part003
    + surrogateDiagTailX0RatChunk001Sub000Block003Part004
    + surrogateDiagTailX0RatChunk001Sub000Block003Part005
    + surrogateDiagTailX0RatChunk001Sub000Block003Part006
    + surrogateDiagTailX0RatChunk001Sub000Block003Part007
    + surrogateDiagTailX0RatChunk001Sub000Block003Part008
    + surrogateDiagTailX0RatChunk001Sub000Block003Part009
    + surrogateDiagTailX0RatChunk001Sub000Block003Part010
    + surrogateDiagTailX0RatChunk001Sub000Block003Part011
    + surrogateDiagTailX0RatChunk001Sub000Block003Part012
    + surrogateDiagTailX0RatChunk001Sub000Block003Part013
    + surrogateDiagTailX0RatChunk001Sub000Block003Part014
    + surrogateDiagTailX0RatChunk001Sub000Block003Part015
    + surrogateDiagTailX0RatChunk001Sub000Block003Part016
    + surrogateDiagTailX0RatChunk001Sub000Block003Part017
    + surrogateDiagTailX0RatChunk001Sub000Block003Part018
    + surrogateDiagTailX0RatChunk001Sub000Block003Part019
    + surrogateDiagTailX0RatChunk001Sub000Block003Part020
    + surrogateDiagTailX0RatChunk001Sub000Block003Part021
    + surrogateDiagTailX0RatChunk001Sub000Block003Part022
    + surrogateDiagTailX0RatChunk001Sub000Block003Part023
    + surrogateDiagTailX0RatChunk001Sub000Block003Part024

theorem surrogateDiagTailX0RatChunk001Sub000Block003_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk001Sub000Block003Head + surrogateDiagTailX0RatChunk001Sub000Block003Mid + surrogateDiagTailX0RatChunk001Sub000Block003Tail =
      surrogateDiagTailX0RatChunk001Sub000Block003 := by
  unfold surrogateDiagTailX0RatChunk001Sub000Block003Head surrogateDiagTailX0RatChunk001Sub000Block003Mid surrogateDiagTailX0RatChunk001Sub000Block003Tail surrogateDiagTailX0RatChunk001Sub000Block003
  ring

def SurrogateDiagonalTailChunk001Sub000Block003HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block003HeadSum X0 = surrogateDiagTailX0RatChunk001Sub000Block003Head

def SurrogateDiagonalTailChunk001Sub000Block003MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block003MidSum X0 = surrogateDiagTailX0RatChunk001Sub000Block003Mid

def SurrogateDiagonalTailChunk001Sub000Block003TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block003TailSum X0 = surrogateDiagTailX0RatChunk001Sub000Block003Tail

theorem surrogateDiagonalTailChunk001Sub000Block003_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk001Sub000Block003HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk001Sub000Block003MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk001Sub000Block003TailCertificateAt X0) :
    surrogateDiagonalTailChunk001Sub000Block003Sum X0 = surrogateDiagTailX0RatChunk001Sub000Block003 := by
  unfold SurrogateDiagonalTailChunk001Sub000Block003HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk001Sub000Block003MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk001Sub000Block003TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk001Sub000Block003Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk001Sub000Block003_eq_head_add_mid_add_tail

/-- Block 004 covers tail-support indices [10100,10125) and q from 16662 to 16701. -/

def TailChunk001Sub000Block004Part000SupportExplicit : Finset ℕ :=
  ([16662] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block004Part000 : ℚ :=
  (120565279525 : ℚ) / 593970255726845952

def SurrogateDiagonalTailChunk001Sub000Block004Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16662
    = surrogateDiagTailX0RatChunk001Sub000Block004Part000

theorem surrogateDiagonalTailChunk001Sub000Block004Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block004Part000CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block004Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block004Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block004Part000CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block004Part000SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block004Part000] using hcert

def TailChunk001Sub000Block004Part001SupportExplicit : Finset ℕ :=
  ([16663] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block004Part001 : ℚ :=
  (61308933325 : ℚ) / 38643220462592143872

def SurrogateDiagonalTailChunk001Sub000Block004Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16663
    = surrogateDiagTailX0RatChunk001Sub000Block004Part001

theorem surrogateDiagonalTailChunk001Sub000Block004Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block004Part001CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block004Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block004Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block004Part001CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block004Part001SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block004Part001] using hcert

def TailChunk001Sub000Block004Part002SupportExplicit : Finset ℕ :=
  ([16665] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block004Part002 : ℚ :=
  (18599499 : ℚ) / 273121280000000

def SurrogateDiagonalTailChunk001Sub000Block004Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16665
    = surrogateDiagTailX0RatChunk001Sub000Block004Part002

theorem surrogateDiagonalTailChunk001Sub000Block004Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block004Part002CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block004Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block004Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block004Part002CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block004Part002SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block004Part002] using hcert

def TailChunk001Sub000Block004Part003SupportExplicit : Finset ℕ :=
  ([16666] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block004Part003 : ℚ :=
  (152281283 : ℚ) / 7249206863462400

def SurrogateDiagonalTailChunk001Sub000Block004Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16666
    = surrogateDiagTailX0RatChunk001Sub000Block004Part003

theorem surrogateDiagonalTailChunk001Sub000Block004Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block004Part003CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block004Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block004Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block004Part003CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block004Part003SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block004Part003] using hcert

def TailChunk001Sub000Block004Part004SupportExplicit : Finset ℕ :=
  ([16667] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block004Part004 : ℚ :=
  (19223397829 : ℚ) / 148539394290470400

def SurrogateDiagonalTailChunk001Sub000Block004Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16667
    = surrogateDiagTailX0RatChunk001Sub000Block004Part004

theorem surrogateDiagonalTailChunk001Sub000Block004Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block004Part004CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block004Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block004Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block004Part004CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block004Part004SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block004Part004] using hcert

def TailChunk001Sub000Block004Part005SupportExplicit : Finset ℕ :=
  ([16669] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block004Part005 : ℚ :=
  (674319291091 : ℚ) / 7200164850957187200

def SurrogateDiagonalTailChunk001Sub000Block004Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16669
    = surrogateDiagTailX0RatChunk001Sub000Block004Part005

theorem surrogateDiagonalTailChunk001Sub000Block004Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block004Part005CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block004Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block004Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block004Part005CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block004Part005SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block004Part005] using hcert

def TailChunk001Sub000Block004Part006SupportExplicit : Finset ℕ :=
  ([16670] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block004Part006 : ℚ :=
  (148773167325 : ℚ) / 234826723089000448

def SurrogateDiagonalTailChunk001Sub000Block004Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16670
    = surrogateDiagTailX0RatChunk001Sub000Block004Part006

theorem surrogateDiagonalTailChunk001Sub000Block004Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block004Part006CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block004Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block004Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block004Part006CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block004Part006SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block004Part006] using hcert

def TailChunk001Sub000Block004Part007SupportExplicit : Finset ℕ :=
  ([16671] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block004Part007 : ℚ :=
  (7717908444325 : ℚ) / 38123765523918931968

def SurrogateDiagonalTailChunk001Sub000Block004Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16671
    = surrogateDiagTailX0RatChunk001Sub000Block004Part007

theorem surrogateDiagonalTailChunk001Sub000Block004Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block004Part007CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block004Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block004Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block004Part007CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block004Part007SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block004Part007] using hcert

def TailChunk001Sub000Block004Part008SupportExplicit : Finset ℕ :=
  ([16673] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block004Part008 : ℚ :=
  (4343577015625 : ℚ) / 48296724086322757632

def SurrogateDiagonalTailChunk001Sub000Block004Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16673
    = surrogateDiagTailX0RatChunk001Sub000Block004Part008

theorem surrogateDiagonalTailChunk001Sub000Block004Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block004Part008CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block004Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block004Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block004Part008CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block004Part008SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block004Part008] using hcert

def TailChunk001Sub000Block004Part009SupportExplicit : Finset ℕ :=
  ([16674] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block004Part009 : ℚ :=
  (1993688602525 : ℚ) / 1275065769416491008

def SurrogateDiagonalTailChunk001Sub000Block004Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16674
    = surrogateDiagTailX0RatChunk001Sub000Block004Part009

theorem surrogateDiagonalTailChunk001Sub000Block004Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block004Part009CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block004Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block004Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block004Part009CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block004Part009SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block004Part009] using hcert

def TailChunk001Sub000Block004Part010SupportExplicit : Finset ℕ :=
  ([16678] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block004Part010 : ℚ :=
  (33047186861 : ℚ) / 83587443157002240

def SurrogateDiagonalTailChunk001Sub000Block004Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16678
    = surrogateDiagTailX0RatChunk001Sub000Block004Part010

theorem surrogateDiagonalTailChunk001Sub000Block004Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block004Part010CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block004Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block004Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block004Part010CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block004Part010SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block004Part010] using hcert

def TailChunk001Sub000Block004Part011SupportExplicit : Finset ℕ :=
  ([16679] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block004Part011 : ℚ :=
  (3776244069025 : ℚ) / 35014179391536148992

def SurrogateDiagonalTailChunk001Sub000Block004Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16679
    = surrogateDiagTailX0RatChunk001Sub000Block004Part011

theorem surrogateDiagonalTailChunk001Sub000Block004Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block004Part011CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block004Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block004Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block004Part011CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block004Part011SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block004Part011] using hcert

def TailChunk001Sub000Block004Part012SupportExplicit : Finset ℕ :=
  ([16681] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block004Part012 : ℚ :=
  (13123670455225 : ℚ) / 104327521259179678848

def SurrogateDiagonalTailChunk001Sub000Block004Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16681
    = surrogateDiagTailX0RatChunk001Sub000Block004Part012

theorem surrogateDiagonalTailChunk001Sub000Block004Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block004Part012CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block004Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block004Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block004Part012CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block004Part012SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block004Part012] using hcert

def TailChunk001Sub000Block004Part013SupportExplicit : Finset ℕ :=
  ([16682] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block004Part013 : ℚ :=
  (4023020805325 : ℚ) / 9660805115648035968

def SurrogateDiagonalTailChunk001Sub000Block004Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16682
    = surrogateDiagTailX0RatChunk001Sub000Block004Part013

theorem surrogateDiagonalTailChunk001Sub000Block004Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block004Part013CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block004Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block004Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block004Part013CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block004Part013SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block004Part013] using hcert

def TailChunk001Sub000Block004Part014SupportExplicit : Finset ℕ :=
  ([16683] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block004Part014 : ℚ :=
  (336885366925 : ℚ) / 1560110329829551104

def SurrogateDiagonalTailChunk001Sub000Block004Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16683
    = surrogateDiagTailX0RatChunk001Sub000Block004Part014

theorem surrogateDiagonalTailChunk001Sub000Block004Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block004Part014CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block004Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block004Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block004Part014CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block004Part014SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block004Part014] using hcert

def TailChunk001Sub000Block004Part015SupportExplicit : Finset ℕ :=
  ([16685] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block004Part015 : ℚ :=
  (74350471821 : ℚ) / 458774269029171200

def SurrogateDiagonalTailChunk001Sub000Block004Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16685
    = surrogateDiagTailX0RatChunk001Sub000Block004Part015

theorem surrogateDiagonalTailChunk001Sub000Block004Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block004Part015CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block004Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block004Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block004Part015CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block004Part015SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block004Part015] using hcert

def TailChunk001Sub000Block004Part016SupportExplicit : Finset ℕ :=
  ([16687] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block004Part016 : ℚ :=
  (537310984183 : ℚ) / 4300676923392000000

def SurrogateDiagonalTailChunk001Sub000Block004Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16687
    = surrogateDiagTailX0RatChunk001Sub000Block004Part016

theorem surrogateDiagonalTailChunk001Sub000Block004Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block004Part016CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block004Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block004Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block004Part016CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block004Part016SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block004Part016] using hcert

def TailChunk001Sub000Block004Part017SupportExplicit : Finset ℕ :=
  ([16689] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block004Part017 : ℚ :=
  (7734585443725 : ℚ) / 38288713971245378688

def SurrogateDiagonalTailChunk001Sub000Block004Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16689
    = surrogateDiagTailX0RatChunk001Sub000Block004Part017

theorem surrogateDiagonalTailChunk001Sub000Block004Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block004Part017CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block004Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block004Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block004Part017CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block004Part017SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block004Part017] using hcert

def TailChunk001Sub000Block004Part018SupportExplicit : Finset ℕ :=
  ([16690] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block004Part018 : ℚ :=
  (1878667775 : ℚ) / 2972455828291584

def SurrogateDiagonalTailChunk001Sub000Block004Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16690
    = surrogateDiagTailX0RatChunk001Sub000Block004Part018

theorem surrogateDiagonalTailChunk001Sub000Block004Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block004Part018CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block004Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block004Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block004Part018CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block004Part018SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block004Part018] using hcert

def TailChunk001Sub000Block004Part019SupportExplicit : Finset ℕ :=
  ([16691] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block004Part019 : ℚ :=
  (6964737025 : ℚ) / 77609019547379442

def SurrogateDiagonalTailChunk001Sub000Block004Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16691
    = surrogateDiagTailX0RatChunk001Sub000Block004Part019

theorem surrogateDiagonalTailChunk001Sub000Block004Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block004Part019CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block004Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block004Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block004Part019CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block004Part019SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block004Part019] using hcert

def TailChunk001Sub000Block004Part020SupportExplicit : Finset ℕ :=
  ([16693] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block004Part020 : ℚ :=
  (4354003890625 : ℚ) / 48528891552269505312

def SurrogateDiagonalTailChunk001Sub000Block004Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16693
    = surrogateDiagTailX0RatChunk001Sub000Block004Part020

theorem surrogateDiagonalTailChunk001Sub000Block004Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block004Part020CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block004Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block004Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block004Part020CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block004Part020SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block004Part020] using hcert

def TailChunk001Sub000Block004Part021SupportExplicit : Finset ℕ :=
  ([16694] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block004Part021 : ℚ :=
  (159291451303 : ℚ) / 377877558735667200

def SurrogateDiagonalTailChunk001Sub000Block004Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16694
    = surrogateDiagTailX0RatChunk001Sub000Block004Part021

theorem surrogateDiagonalTailChunk001Sub000Block004Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block004Part021CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block004Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block004Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block004Part021CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block004Part021SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block004Part021] using hcert

def TailChunk001Sub000Block004Part022SupportExplicit : Finset ℕ :=
  ([16697] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block004Part022 : ℚ :=
  (207704544475 : ℚ) / 2209277387835182208

def SurrogateDiagonalTailChunk001Sub000Block004Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16697
    = surrogateDiagTailX0RatChunk001Sub000Block004Part022

theorem surrogateDiagonalTailChunk001Sub000Block004Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block004Part022CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block004Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block004Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block004Part022CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block004Part022SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block004Part022] using hcert

def TailChunk001Sub000Block004Part023SupportExplicit : Finset ℕ :=
  ([16699] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block004Part023 : ℚ :=
  (4357134390625 : ℚ) / 48598704727902113202

def SurrogateDiagonalTailChunk001Sub000Block004Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16699
    = surrogateDiagTailX0RatChunk001Sub000Block004Part023

theorem surrogateDiagonalTailChunk001Sub000Block004Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block004Part023CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block004Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block004Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block004Part023CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block004Part023SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block004Part023] using hcert

def TailChunk001Sub000Block004Part024SupportExplicit : Finset ℕ :=
  ([16701] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block004Part024 : ℚ :=
  (3541358303375 : ℚ) / 15266457466703069184

def SurrogateDiagonalTailChunk001Sub000Block004Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16701
    = surrogateDiagTailX0RatChunk001Sub000Block004Part024

theorem surrogateDiagonalTailChunk001Sub000Block004Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block004Part024CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block004Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block004Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block004Part024CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block004Part024SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block004Part024] using hcert

def surrogateDiagonalTailChunk001Sub000Block004HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block004Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block004Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block004Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block004Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block004Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block004Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block004Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block004Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block004Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block004Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block004Head : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block004Part000
    + surrogateDiagTailX0RatChunk001Sub000Block004Part001
    + surrogateDiagTailX0RatChunk001Sub000Block004Part002
    + surrogateDiagTailX0RatChunk001Sub000Block004Part003
    + surrogateDiagTailX0RatChunk001Sub000Block004Part004
    + surrogateDiagTailX0RatChunk001Sub000Block004Part005
    + surrogateDiagTailX0RatChunk001Sub000Block004Part006
    + surrogateDiagTailX0RatChunk001Sub000Block004Part007
    + surrogateDiagTailX0RatChunk001Sub000Block004Part008
    + surrogateDiagTailX0RatChunk001Sub000Block004Part009

def surrogateDiagonalTailChunk001Sub000Block004MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block004Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block004Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block004Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block004Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block004Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block004Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block004Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block004Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block004Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block004Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block004Mid : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block004Part010
    + surrogateDiagTailX0RatChunk001Sub000Block004Part011
    + surrogateDiagTailX0RatChunk001Sub000Block004Part012
    + surrogateDiagTailX0RatChunk001Sub000Block004Part013
    + surrogateDiagTailX0RatChunk001Sub000Block004Part014
    + surrogateDiagTailX0RatChunk001Sub000Block004Part015
    + surrogateDiagTailX0RatChunk001Sub000Block004Part016
    + surrogateDiagTailX0RatChunk001Sub000Block004Part017
    + surrogateDiagTailX0RatChunk001Sub000Block004Part018
    + surrogateDiagTailX0RatChunk001Sub000Block004Part019

def surrogateDiagonalTailChunk001Sub000Block004TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block004Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block004Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block004Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block004Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block004Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block004Tail : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block004Part020
    + surrogateDiagTailX0RatChunk001Sub000Block004Part021
    + surrogateDiagTailX0RatChunk001Sub000Block004Part022
    + surrogateDiagTailX0RatChunk001Sub000Block004Part023
    + surrogateDiagTailX0RatChunk001Sub000Block004Part024

def surrogateDiagonalTailChunk001Sub000Block004Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk001Sub000Block004HeadSum X0
    + surrogateDiagonalTailChunk001Sub000Block004MidSum X0
    + surrogateDiagonalTailChunk001Sub000Block004TailSum X0

def surrogateDiagTailX0RatChunk001Sub000Block004 : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block004Part000
    + surrogateDiagTailX0RatChunk001Sub000Block004Part001
    + surrogateDiagTailX0RatChunk001Sub000Block004Part002
    + surrogateDiagTailX0RatChunk001Sub000Block004Part003
    + surrogateDiagTailX0RatChunk001Sub000Block004Part004
    + surrogateDiagTailX0RatChunk001Sub000Block004Part005
    + surrogateDiagTailX0RatChunk001Sub000Block004Part006
    + surrogateDiagTailX0RatChunk001Sub000Block004Part007
    + surrogateDiagTailX0RatChunk001Sub000Block004Part008
    + surrogateDiagTailX0RatChunk001Sub000Block004Part009
    + surrogateDiagTailX0RatChunk001Sub000Block004Part010
    + surrogateDiagTailX0RatChunk001Sub000Block004Part011
    + surrogateDiagTailX0RatChunk001Sub000Block004Part012
    + surrogateDiagTailX0RatChunk001Sub000Block004Part013
    + surrogateDiagTailX0RatChunk001Sub000Block004Part014
    + surrogateDiagTailX0RatChunk001Sub000Block004Part015
    + surrogateDiagTailX0RatChunk001Sub000Block004Part016
    + surrogateDiagTailX0RatChunk001Sub000Block004Part017
    + surrogateDiagTailX0RatChunk001Sub000Block004Part018
    + surrogateDiagTailX0RatChunk001Sub000Block004Part019
    + surrogateDiagTailX0RatChunk001Sub000Block004Part020
    + surrogateDiagTailX0RatChunk001Sub000Block004Part021
    + surrogateDiagTailX0RatChunk001Sub000Block004Part022
    + surrogateDiagTailX0RatChunk001Sub000Block004Part023
    + surrogateDiagTailX0RatChunk001Sub000Block004Part024

theorem surrogateDiagTailX0RatChunk001Sub000Block004_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk001Sub000Block004Head + surrogateDiagTailX0RatChunk001Sub000Block004Mid + surrogateDiagTailX0RatChunk001Sub000Block004Tail =
      surrogateDiagTailX0RatChunk001Sub000Block004 := by
  unfold surrogateDiagTailX0RatChunk001Sub000Block004Head surrogateDiagTailX0RatChunk001Sub000Block004Mid surrogateDiagTailX0RatChunk001Sub000Block004Tail surrogateDiagTailX0RatChunk001Sub000Block004
  ring

def SurrogateDiagonalTailChunk001Sub000Block004HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block004HeadSum X0 = surrogateDiagTailX0RatChunk001Sub000Block004Head

def SurrogateDiagonalTailChunk001Sub000Block004MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block004MidSum X0 = surrogateDiagTailX0RatChunk001Sub000Block004Mid

def SurrogateDiagonalTailChunk001Sub000Block004TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block004TailSum X0 = surrogateDiagTailX0RatChunk001Sub000Block004Tail

theorem surrogateDiagonalTailChunk001Sub000Block004_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk001Sub000Block004HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk001Sub000Block004MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk001Sub000Block004TailCertificateAt X0) :
    surrogateDiagonalTailChunk001Sub000Block004Sum X0 = surrogateDiagTailX0RatChunk001Sub000Block004 := by
  unfold SurrogateDiagonalTailChunk001Sub000Block004HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk001Sub000Block004MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk001Sub000Block004TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk001Sub000Block004Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk001Sub000Block004_eq_head_add_mid_add_tail

/-- Block 005 covers tail-support indices [10125,10150) and q from 16702 to 16741. -/

def TailChunk001Sub000Block005Part000SupportExplicit : Finset ℕ :=
  ([16702] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block005Part000 : ℚ :=
  (192542258975 : ℚ) / 363466489931513856

def SurrogateDiagonalTailChunk001Sub000Block005Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16702
    = surrogateDiagTailX0RatChunk001Sub000Block005Part000

theorem surrogateDiagonalTailChunk001Sub000Block005Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block005Part000CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block005Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block005Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block005Part000CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block005Part000SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block005Part000] using hcert

def TailChunk001Sub000Block005Part001SupportExplicit : Finset ℕ :=
  ([16703] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block005Part001 : ℚ :=
  (4359222015625 : ℚ) / 48645288673496246802

def SurrogateDiagonalTailChunk001Sub000Block005Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16703
    = surrogateDiagTailX0RatChunk001Sub000Block005Part001

theorem surrogateDiagonalTailChunk001Sub000Block005Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block005Part001CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block005Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block005Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block005Part001CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block005Part001SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block005Part001] using hcert

def TailChunk001Sub000Block005Part002SupportExplicit : Finset ℕ :=
  ([16705] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block005Part002 : ℚ :=
  (1705816337575 : ℚ) / 9501680420077436928

def SurrogateDiagonalTailChunk001Sub000Block005Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16705
    = surrogateDiagTailX0RatChunk001Sub000Block005Part002

theorem surrogateDiagonalTailChunk001Sub000Block005Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block005Part002CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block005Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block005Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block005Part002CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block005Part002SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block005Part002] using hcert

def TailChunk001Sub000Block005Part003SupportExplicit : Finset ℕ :=
  ([16706] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block005Part003 : ℚ :=
  (1090197015625 : ℚ) / 3041787075053617152

def SurrogateDiagonalTailChunk001Sub000Block005Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16706
    = surrogateDiagTailX0RatChunk001Sub000Block005Part003

theorem surrogateDiagonalTailChunk001Sub000Block005Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block005Part003CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block005Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block005Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block005Part003CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block005Part003SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block005Part003] using hcert

def TailChunk001Sub000Block005Part004SupportExplicit : Finset ℕ :=
  ([16707] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block005Part004 : ℚ :=
  (7751280443125 : ℚ) / 38454197096974123008

def SurrogateDiagonalTailChunk001Sub000Block005Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16707
    = surrogateDiagTailX0RatChunk001Sub000Block005Part004

theorem surrogateDiagonalTailChunk001Sub000Block005Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block005Part004CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block005Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block005Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block005Part004CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block005Part004SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block005Part004] using hcert

def TailChunk001Sub000Block005Part005SupportExplicit : Finset ℕ :=
  ([16710] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block005Part005 : ℚ :=
  (899804765825 : ℚ) / 489390999087611904

def SurrogateDiagonalTailChunk001Sub000Block005Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16710
    = surrogateDiagTailX0RatChunk001Sub000Block005Part005

theorem surrogateDiagonalTailChunk001Sub000Block005Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block005Part005CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block005Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block005Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block005Part005CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block005Part005SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block005Part005] using hcert

def TailChunk001Sub000Block005Part006SupportExplicit : Finset ℕ :=
  ([16711] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block005Part006 : ℚ :=
  (5225547260625 : ℚ) / 50796230581255929856

def SurrogateDiagonalTailChunk001Sub000Block005Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16711
    = surrogateDiagTailX0RatChunk001Sub000Block005Part006

theorem surrogateDiagonalTailChunk001Sub000Block005Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block005Part006CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block005Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block005Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block005Part006CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block005Part006SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block005Part006] using hcert

def TailChunk001Sub000Block005Part007SupportExplicit : Finset ℕ :=
  ([16714] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block005Part007 : ℚ :=
  (33779643857 : ℚ) / 88690577115709440

def SurrogateDiagonalTailChunk001Sub000Block005Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16714
    = surrogateDiagTailX0RatChunk001Sub000Block005Part007

theorem surrogateDiagonalTailChunk001Sub000Block005Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block005Part007CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block005Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block005Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block005Part007CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block005Part007SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block005Part007] using hcert

def TailChunk001Sub000Block005Part008SupportExplicit : Finset ℕ :=
  ([16715] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block005Part008 : ℚ :=
  (11869391584525 : ℚ) / 79853251830184101888

def SurrogateDiagonalTailChunk001Sub000Block005Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16715
    = surrogateDiagTailX0RatChunk001Sub000Block005Part008

theorem surrogateDiagonalTailChunk001Sub000Block005Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block005Part008CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block005Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block005Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block005Part008CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block005Part008SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block005Part008] using hcert

def TailChunk001Sub000Block005Part009SupportExplicit : Finset ℕ :=
  ([16717] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block005Part009 : ℚ :=
  (2116841350475 : ℚ) / 22698974952001437696

def SurrogateDiagonalTailChunk001Sub000Block005Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16717
    = surrogateDiagTailX0RatChunk001Sub000Block005Part009

theorem surrogateDiagonalTailChunk001Sub000Block005Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block005Part009CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block005Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block005Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block005Part009CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block005Part009SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block005Part009] using hcert

def TailChunk001Sub000Block005Part010SupportExplicit : Finset ℕ :=
  ([16718] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block005Part010 : ℚ :=
  (1947095819675 : ℚ) / 4404148555844772864

def SurrogateDiagonalTailChunk001Sub000Block005Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16718
    = surrogateDiagTailX0RatChunk001Sub000Block005Part010

theorem surrogateDiagonalTailChunk001Sub000Block005Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block005Part010CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block005Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block005Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block005Part010CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block005Part010SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block005Part010] using hcert

def TailChunk001Sub000Block005Part011SupportExplicit : Finset ℕ :=
  ([16719] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block005Part011 : ℚ :=
  (7762420442725 : ℚ) / 38564816794268878848

def SurrogateDiagonalTailChunk001Sub000Block005Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16719
    = surrogateDiagTailX0RatChunk001Sub000Block005Part011

theorem surrogateDiagonalTailChunk001Sub000Block005Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block005Part011CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block005Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block005Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block005Part011CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block005Part011SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block005Part011] using hcert

def TailChunk001Sub000Block005Part012SupportExplicit : Finset ℕ :=
  ([16721] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block005Part012 : ℚ :=
  (16150070629975 : ℚ) / 162728666274626483328

def SurrogateDiagonalTailChunk001Sub000Block005Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16721
    = surrogateDiagTailX0RatChunk001Sub000Block005Part012

theorem surrogateDiagonalTailChunk001Sub000Block005Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block005Part012CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block005Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block005Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block005Part012CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block005Part012SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block005Part012] using hcert

def TailChunk001Sub000Block005Part013SupportExplicit : Finset ℕ :=
  ([16723] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block005Part013 : ℚ :=
  (13189858492225 : ℚ) / 105382658470303254528

def SurrogateDiagonalTailChunk001Sub000Block005Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16723
    = surrogateDiagTailX0RatChunk001Sub000Block005Part013

theorem surrogateDiagonalTailChunk001Sub000Block005Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block005Part013CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block005Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block005Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block005Part013CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block005Part013SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block005Part013] using hcert

def TailChunk001Sub000Block005Part014SupportExplicit : Finset ℕ :=
  ([16726] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block005Part014 : ℚ :=
  (1092808890625 : ℚ) / 3056381205401488242

def SurrogateDiagonalTailChunk001Sub000Block005Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16726
    = surrogateDiagTailX0RatChunk001Sub000Block005Part014

theorem surrogateDiagonalTailChunk001Sub000Block005Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block005Part014CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block005Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block005Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block005Part014CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block005Part014SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block005Part014] using hcert

def TailChunk001Sub000Block005Part015SupportExplicit : Finset ℕ :=
  ([16727] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block005Part015 : ℚ :=
  (154862301625 : ℚ) / 1632778102592534016

def SurrogateDiagonalTailChunk001Sub000Block005Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16727
    = surrogateDiagTailX0RatChunk001Sub000Block005Part015

theorem surrogateDiagonalTailChunk001Sub000Block005Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block005Part015CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block005Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block005Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block005Part015CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block005Part015SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block005Part015] using hcert

def TailChunk001Sub000Block005Part016SupportExplicit : Finset ℕ :=
  ([16729] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block005Part016 : ℚ :=
  (4372803765625 : ℚ) / 48948901148645356032

def SurrogateDiagonalTailChunk001Sub000Block005Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16729
    = surrogateDiagTailX0RatChunk001Sub000Block005Part016

theorem surrogateDiagonalTailChunk001Sub000Block005Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block005Part016CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block005Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block005Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block005Part016CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block005Part016SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block005Part016] using hcert

def TailChunk001Sub000Block005Part017SupportExplicit : Finset ℕ :=
  ([16730] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block005Part017 : ℚ :=
  (2521402699525 : ℚ) / 2661825945685229568

def SurrogateDiagonalTailChunk001Sub000Block005Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16730
    = surrogateDiagTailX0RatChunk001Sub000Block005Part017

theorem surrogateDiagonalTailChunk001Sub000Block005Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block005Part017CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block005Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block005Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block005Part017CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block005Part017SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block005Part017] using hcert

def TailChunk001Sub000Block005Part018SupportExplicit : Finset ℕ :=
  ([16733] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block005Part018 : ℚ :=
  (304318708025 : ℚ) / 3132962222251180032

def SurrogateDiagonalTailChunk001Sub000Block005Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16733
    = surrogateDiagTailX0RatChunk001Sub000Block005Part018

theorem surrogateDiagonalTailChunk001Sub000Block005Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block005Part018CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block005Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block005Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block005Part018CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block005Part018SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block005Part018] using hcert

def TailChunk001Sub000Block005Part019SupportExplicit : Finset ℕ :=
  ([16734] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block005Part019 : ℚ :=
  (1215029257475 : ℚ) / 1208614843176428544

def SurrogateDiagonalTailChunk001Sub000Block005Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16734
    = surrogateDiagTailX0RatChunk001Sub000Block005Part019

theorem surrogateDiagonalTailChunk001Sub000Block005Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block005Part019CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block005Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block005Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block005Part019CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block005Part019SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block005Part019] using hcert

def TailChunk001Sub000Block005Part020SupportExplicit : Finset ℕ :=
  ([16735] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block005Part020 : ℚ :=
  (699810390625 : ℚ) / 5014765022560261248

def SurrogateDiagonalTailChunk001Sub000Block005Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16735
    = surrogateDiagTailX0RatChunk001Sub000Block005Part020

theorem surrogateDiagonalTailChunk001Sub000Block005Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block005Part020CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block005Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block005Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block005Part020CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block005Part020SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block005Part020] using hcert

def TailChunk001Sub000Block005Part021SupportExplicit : Finset ℕ :=
  ([16737] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block005Part021 : ℚ :=
  (30265023775 : ℚ) / 104604661301870592

def SurrogateDiagonalTailChunk001Sub000Block005Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16737
    = surrogateDiagTailX0RatChunk001Sub000Block005Part021

theorem surrogateDiagonalTailChunk001Sub000Block005Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block005Part021CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block005Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block005Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block005Part021CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block005Part021SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block005Part021] using hcert

def TailChunk001Sub000Block005Part022SupportExplicit : Finset ℕ :=
  ([16738] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block005Part022 : ℚ :=
  (1094377515625 : ℚ) / 3065162852915945472

def SurrogateDiagonalTailChunk001Sub000Block005Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16738
    = surrogateDiagTailX0RatChunk001Sub000Block005Part022

theorem surrogateDiagonalTailChunk001Sub000Block005Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block005Part022CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block005Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block005Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block005Part022CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block005Part022SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block005Part022] using hcert

def TailChunk001Sub000Block005Part023SupportExplicit : Finset ℕ :=
  ([16739] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block005Part023 : ℚ :=
  (106204975781 : ℚ) / 1049436847256371200

def SurrogateDiagonalTailChunk001Sub000Block005Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16739
    = surrogateDiagTailX0RatChunk001Sub000Block005Part023

theorem surrogateDiagonalTailChunk001Sub000Block005Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block005Part023CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block005Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block005Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block005Part023CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block005Part023SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block005Part023] using hcert

def TailChunk001Sub000Block005Part024SupportExplicit : Finset ℕ :=
  ([16741] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block005Part024 : ℚ :=
  (7006527025 : ℚ) / 78543213303320352

def SurrogateDiagonalTailChunk001Sub000Block005Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16741
    = surrogateDiagTailX0RatChunk001Sub000Block005Part024

theorem surrogateDiagonalTailChunk001Sub000Block005Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block005Part024CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block005Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block005Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block005Part024CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block005Part024SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block005Part024] using hcert

def surrogateDiagonalTailChunk001Sub000Block005HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block005Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block005Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block005Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block005Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block005Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block005Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block005Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block005Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block005Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block005Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block005Head : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block005Part000
    + surrogateDiagTailX0RatChunk001Sub000Block005Part001
    + surrogateDiagTailX0RatChunk001Sub000Block005Part002
    + surrogateDiagTailX0RatChunk001Sub000Block005Part003
    + surrogateDiagTailX0RatChunk001Sub000Block005Part004
    + surrogateDiagTailX0RatChunk001Sub000Block005Part005
    + surrogateDiagTailX0RatChunk001Sub000Block005Part006
    + surrogateDiagTailX0RatChunk001Sub000Block005Part007
    + surrogateDiagTailX0RatChunk001Sub000Block005Part008
    + surrogateDiagTailX0RatChunk001Sub000Block005Part009

def surrogateDiagonalTailChunk001Sub000Block005MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block005Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block005Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block005Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block005Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block005Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block005Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block005Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block005Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block005Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block005Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block005Mid : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block005Part010
    + surrogateDiagTailX0RatChunk001Sub000Block005Part011
    + surrogateDiagTailX0RatChunk001Sub000Block005Part012
    + surrogateDiagTailX0RatChunk001Sub000Block005Part013
    + surrogateDiagTailX0RatChunk001Sub000Block005Part014
    + surrogateDiagTailX0RatChunk001Sub000Block005Part015
    + surrogateDiagTailX0RatChunk001Sub000Block005Part016
    + surrogateDiagTailX0RatChunk001Sub000Block005Part017
    + surrogateDiagTailX0RatChunk001Sub000Block005Part018
    + surrogateDiagTailX0RatChunk001Sub000Block005Part019

def surrogateDiagonalTailChunk001Sub000Block005TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block005Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block005Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block005Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block005Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block005Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block005Tail : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block005Part020
    + surrogateDiagTailX0RatChunk001Sub000Block005Part021
    + surrogateDiagTailX0RatChunk001Sub000Block005Part022
    + surrogateDiagTailX0RatChunk001Sub000Block005Part023
    + surrogateDiagTailX0RatChunk001Sub000Block005Part024

def surrogateDiagonalTailChunk001Sub000Block005Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk001Sub000Block005HeadSum X0
    + surrogateDiagonalTailChunk001Sub000Block005MidSum X0
    + surrogateDiagonalTailChunk001Sub000Block005TailSum X0

def surrogateDiagTailX0RatChunk001Sub000Block005 : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block005Part000
    + surrogateDiagTailX0RatChunk001Sub000Block005Part001
    + surrogateDiagTailX0RatChunk001Sub000Block005Part002
    + surrogateDiagTailX0RatChunk001Sub000Block005Part003
    + surrogateDiagTailX0RatChunk001Sub000Block005Part004
    + surrogateDiagTailX0RatChunk001Sub000Block005Part005
    + surrogateDiagTailX0RatChunk001Sub000Block005Part006
    + surrogateDiagTailX0RatChunk001Sub000Block005Part007
    + surrogateDiagTailX0RatChunk001Sub000Block005Part008
    + surrogateDiagTailX0RatChunk001Sub000Block005Part009
    + surrogateDiagTailX0RatChunk001Sub000Block005Part010
    + surrogateDiagTailX0RatChunk001Sub000Block005Part011
    + surrogateDiagTailX0RatChunk001Sub000Block005Part012
    + surrogateDiagTailX0RatChunk001Sub000Block005Part013
    + surrogateDiagTailX0RatChunk001Sub000Block005Part014
    + surrogateDiagTailX0RatChunk001Sub000Block005Part015
    + surrogateDiagTailX0RatChunk001Sub000Block005Part016
    + surrogateDiagTailX0RatChunk001Sub000Block005Part017
    + surrogateDiagTailX0RatChunk001Sub000Block005Part018
    + surrogateDiagTailX0RatChunk001Sub000Block005Part019
    + surrogateDiagTailX0RatChunk001Sub000Block005Part020
    + surrogateDiagTailX0RatChunk001Sub000Block005Part021
    + surrogateDiagTailX0RatChunk001Sub000Block005Part022
    + surrogateDiagTailX0RatChunk001Sub000Block005Part023
    + surrogateDiagTailX0RatChunk001Sub000Block005Part024

theorem surrogateDiagTailX0RatChunk001Sub000Block005_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk001Sub000Block005Head + surrogateDiagTailX0RatChunk001Sub000Block005Mid + surrogateDiagTailX0RatChunk001Sub000Block005Tail =
      surrogateDiagTailX0RatChunk001Sub000Block005 := by
  unfold surrogateDiagTailX0RatChunk001Sub000Block005Head surrogateDiagTailX0RatChunk001Sub000Block005Mid surrogateDiagTailX0RatChunk001Sub000Block005Tail surrogateDiagTailX0RatChunk001Sub000Block005
  ring

def SurrogateDiagonalTailChunk001Sub000Block005HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block005HeadSum X0 = surrogateDiagTailX0RatChunk001Sub000Block005Head

def SurrogateDiagonalTailChunk001Sub000Block005MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block005MidSum X0 = surrogateDiagTailX0RatChunk001Sub000Block005Mid

def SurrogateDiagonalTailChunk001Sub000Block005TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block005TailSum X0 = surrogateDiagTailX0RatChunk001Sub000Block005Tail

theorem surrogateDiagonalTailChunk001Sub000Block005_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk001Sub000Block005HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk001Sub000Block005MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk001Sub000Block005TailCertificateAt X0) :
    surrogateDiagonalTailChunk001Sub000Block005Sum X0 = surrogateDiagTailX0RatChunk001Sub000Block005 := by
  unfold SurrogateDiagonalTailChunk001Sub000Block005HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk001Sub000Block005MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk001Sub000Block005TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk001Sub000Block005Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk001Sub000Block005_eq_head_add_mid_add_tail

/-- Block 006 covers tail-support indices [10150,10175) and q from 16742 to 16782. -/

def TailChunk001Sub000Block006Part000SupportExplicit : Finset ℕ :=
  ([16742] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block006Part000 : ℚ :=
  (5058932589 : ℚ) / 11122949478400000

def SurrogateDiagonalTailChunk001Sub000Block006Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16742
    = surrogateDiagTailX0RatChunk001Sub000Block006Part000

theorem surrogateDiagonalTailChunk001Sub000Block006Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block006Part000CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block006Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block006Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block006Part000CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block006Part000SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block006Part000] using hcert

def TailChunk001Sub000Block006Part001SupportExplicit : Finset ℕ :=
  ([16743] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block006Part001 : ℚ :=
  (311388977677 : ℚ) / 1551470880065587200

def SurrogateDiagonalTailChunk001Sub000Block006Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16743
    = surrogateDiagTailX0RatChunk001Sub000Block006Part001

theorem surrogateDiagonalTailChunk001Sub000Block006Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block006Part001CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block006Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block006Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block006Part001CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block006Part001SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block006Part001] using hcert

def TailChunk001Sub000Block006Part002SupportExplicit : Finset ℕ :=
  ([16745] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block006Part002 : ℚ :=
  (837977703825 : ℚ) / 5159288268604309504

def SurrogateDiagonalTailChunk001Sub000Block006Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16745
    = surrogateDiagTailX0RatChunk001Sub000Block006Part002

theorem surrogateDiagonalTailChunk001Sub000Block006Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block006Part002CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block006Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block006Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block006Part002CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block006Part002SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block006Part002] using hcert

def TailChunk001Sub000Block006Part003SupportExplicit : Finset ℕ :=
  ([16746] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block006Part003 : ℚ :=
  (77865988837 : ℚ) / 96966930004099200

def SurrogateDiagonalTailChunk001Sub000Block006Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16746
    = surrogateDiagTailX0RatChunk001Sub000Block006Part003

theorem surrogateDiagonalTailChunk001Sub000Block006Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block006Part003CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block006Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block006Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block006Part003CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block006Part003SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block006Part003] using hcert

def TailChunk001Sub000Block006Part004SupportExplicit : Finset ℕ :=
  ([16747] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block006Part004 : ℚ :=
  (4382218890625 : ℚ) / 49159925385299655282

def SurrogateDiagonalTailChunk001Sub000Block006Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16747
    = surrogateDiagTailX0RatChunk001Sub000Block006Part004

theorem surrogateDiagonalTailChunk001Sub000Block006Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block006Part004CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block006Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block006Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block006Part004CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block006Part004SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block006Part004] using hcert

def TailChunk001Sub000Block006Part005SupportExplicit : Finset ℕ :=
  ([16751] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block006Part005 : ℚ :=
  (3398099054875 : ℚ) / 26522628997512241152

def SurrogateDiagonalTailChunk001Sub000Block006Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16751
    = surrogateDiagTailX0RatChunk001Sub000Block006Part005

theorem surrogateDiagonalTailChunk001Sub000Block006Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block006Part005CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block006Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block006Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block006Part005CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block006Part005SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block006Part005] using hcert

def TailChunk001Sub000Block006Part006SupportExplicit : Finset ℕ :=
  ([16753] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block006Part006 : ℚ :=
  (12309838947 : ℚ) / 111816069622509400

def SurrogateDiagonalTailChunk001Sub000Block006Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16753
    = surrogateDiagTailX0RatChunk001Sub000Block006Part006

theorem surrogateDiagonalTailChunk001Sub000Block006Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block006Part006CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block006Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block006Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block006Part006CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block006Part006SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block006Part006] using hcert

def TailChunk001Sub000Block006Part007SupportExplicit : Finset ℕ :=
  ([16754] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block006Part007 : ℚ :=
  (1096470765625 : ℚ) / 3076901136679260672

def SurrogateDiagonalTailChunk001Sub000Block006Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16754
    = surrogateDiagTailX0RatChunk001Sub000Block006Part007

theorem surrogateDiagonalTailChunk001Sub000Block006Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block006Part007CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block006Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block006Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block006Part007CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block006Part007SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block006Part007] using hcert

def TailChunk001Sub000Block006Part008SupportExplicit : Finset ℕ :=
  ([16755] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block006Part008 : ℚ :=
  (5294493819325 : ℚ) / 15887061811871612928

def SurrogateDiagonalTailChunk001Sub000Block006Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16755
    = surrogateDiagTailX0RatChunk001Sub000Block006Part008

theorem surrogateDiagonalTailChunk001Sub000Block006Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block006Part008CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block006Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block006Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block006Part008CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block006Part008SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block006Part008] using hcert

def TailChunk001Sub000Block006Part009SupportExplicit : Finset ℕ :=
  ([16757] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block006Part009 : ℚ :=
  (7623330120425 : ℚ) / 71348574319416705024

def SurrogateDiagonalTailChunk001Sub000Block006Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16757
    = surrogateDiagTailX0RatChunk001Sub000Block006Part009

theorem surrogateDiagonalTailChunk001Sub000Block006Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block006Part009CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block006Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block006Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block006Part009CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block006Part009SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block006Part009] using hcert

def TailChunk001Sub000Block006Part010SupportExplicit : Finset ℕ :=
  ([16759] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block006Part010 : ℚ :=
  (4388501265625 : ℚ) / 49300986773558379762

def SurrogateDiagonalTailChunk001Sub000Block006Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16759
    = surrogateDiagTailX0RatChunk001Sub000Block006Part010

theorem surrogateDiagonalTailChunk001Sub000Block006Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block006Part010CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block006Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block006Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block006Part010CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block006Part010SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block006Part010] using hcert

def TailChunk001Sub000Block006Part011SupportExplicit : Finset ℕ :=
  ([16761] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block006Part011 : ℚ :=
  (59194056113 : ℚ) / 272152211558400000

def SurrogateDiagonalTailChunk001Sub000Block006Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16761
    = surrogateDiagTailX0RatChunk001Sub000Block006Part011

theorem surrogateDiagonalTailChunk001Sub000Block006Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block006Part011CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block006Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block006Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block006Part011CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block006Part011SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block006Part011] using hcert

def TailChunk001Sub000Block006Part012SupportExplicit : Finset ℕ :=
  ([16763] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block006Part012 : ℚ :=
  (4390596390625 : ℚ) / 49348074627676465842

def SurrogateDiagonalTailChunk001Sub000Block006Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16763
    = surrogateDiagTailX0RatChunk001Sub000Block006Part012

theorem surrogateDiagonalTailChunk001Sub000Block006Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block006Part012CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block006Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block006Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block006Part012CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block006Part012SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block006Part012] using hcert

def TailChunk001Sub000Block006Part013SupportExplicit : Finset ℕ :=
  ([16765] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block006Part013 : ℚ :=
  (4294602386375 : ℚ) / 21654762079927025664

def SurrogateDiagonalTailChunk001Sub000Block006Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16765
    = surrogateDiagTailX0RatChunk001Sub000Block006Part013

theorem surrogateDiagonalTailChunk001Sub000Block006Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block006Part013CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block006Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block006Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block006Part013CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block006Part013SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block006Part013] using hcert

def TailChunk001Sub000Block006Part014SupportExplicit : Finset ℕ :=
  ([16766] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block006Part014 : ℚ :=
  (28392910191 : ℚ) / 75368697392000000

def SurrogateDiagonalTailChunk001Sub000Block006Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16766
    = surrogateDiagTailX0RatChunk001Sub000Block006Part014

theorem surrogateDiagonalTailChunk001Sub000Block006Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block006Part014CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block006Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block006Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block006Part014CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block006Part014SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block006Part014] using hcert

def TailChunk001Sub000Block006Part015SupportExplicit : Finset ℕ :=
  ([16769] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block006Part015 : ℚ :=
  (335496893093 : ℚ) / 3547623084628377600

def SurrogateDiagonalTailChunk001Sub000Block006Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16769
    = surrogateDiagTailX0RatChunk001Sub000Block006Part015

theorem surrogateDiagonalTailChunk001Sub000Block006Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block006Part015CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block006Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block006Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block006Part015CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block006Part015SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block006Part015] using hcert

def TailChunk001Sub000Block006Part016SupportExplicit : Finset ℕ :=
  ([16770] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block006Part016 : ℚ :=
  (796910850275 : ℚ) / 330429609378054144

def SurrogateDiagonalTailChunk001Sub000Block006Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16770
    = surrogateDiagTailX0RatChunk001Sub000Block006Part016

theorem surrogateDiagonalTailChunk001Sub000Block006Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block006Part016CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block006Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block006Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block006Part016CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block006Part016SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block006Part016] using hcert

def TailChunk001Sub000Block006Part017SupportExplicit : Finset ℕ :=
  ([16771] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block006Part017 : ℚ :=
  (41397849559 : ℚ) / 430553303442000000

def SurrogateDiagonalTailChunk001Sub000Block006Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16771
    = surrogateDiagTailX0RatChunk001Sub000Block006Part017

theorem surrogateDiagonalTailChunk001Sub000Block006Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block006Part017CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block006Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block006Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block006Part017CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block006Part017SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block006Part017] using hcert

def TailChunk001Sub000Block006Part018SupportExplicit : Finset ℕ :=
  ([16773] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block006Part018 : ℚ :=
  (312505977637 : ℚ) / 1562622467777155200

def SurrogateDiagonalTailChunk001Sub000Block006Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16773
    = surrogateDiagTailX0RatChunk001Sub000Block006Part018

theorem surrogateDiagonalTailChunk001Sub000Block006Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block006Part018CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block006Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block006Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block006Part018CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block006Part018SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block006Part018] using hcert

def TailChunk001Sub000Block006Part019SupportExplicit : Finset ℕ :=
  ([16774] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block006Part019 : ℚ :=
  (1099090140625 : ℚ) / 3091621364632810002

def SurrogateDiagonalTailChunk001Sub000Block006Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16774
    = surrogateDiagTailX0RatChunk001Sub000Block006Part019

theorem surrogateDiagonalTailChunk001Sub000Block006Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block006Part019CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block006Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block006Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block006Part019CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block006Part019SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block006Part019] using hcert

def TailChunk001Sub000Block006Part020SupportExplicit : Finset ℕ :=
  ([16777] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block006Part020 : ℚ :=
  (590900833675 : ℚ) / 5883387530040284544

def SurrogateDiagonalTailChunk001Sub000Block006Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16777
    = surrogateDiagTailX0RatChunk001Sub000Block006Part020

theorem surrogateDiagonalTailChunk001Sub000Block006Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block006Part020CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block006Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block006Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block006Part020CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block006Part020SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block006Part020] using hcert

def TailChunk001Sub000Block006Part021SupportExplicit : Finset ℕ :=
  ([16778] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block006Part021 : ℚ :=
  (1099614390625 : ℚ) / 3094571736714184992

def SurrogateDiagonalTailChunk001Sub000Block006Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16778
    = surrogateDiagTailX0RatChunk001Sub000Block006Part021

theorem surrogateDiagonalTailChunk001Sub000Block006Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block006Part021CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block006Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block006Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block006Part021CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block006Part021SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block006Part021] using hcert

def TailChunk001Sub000Block006Part022SupportExplicit : Finset ℕ :=
  ([16779] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block006Part022 : ℚ :=
  (5383255468975 : ℚ) / 15214689734086361088

def SurrogateDiagonalTailChunk001Sub000Block006Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16779
    = surrogateDiagTailX0RatChunk001Sub000Block006Part022

theorem surrogateDiagonalTailChunk001Sub000Block006Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block006Part022CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block006Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block006Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block006Part022CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block006Part022SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block006Part022] using hcert

def TailChunk001Sub000Block006Part023SupportExplicit : Finset ℕ :=
  ([16781] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block006Part023 : ℚ :=
  (713481110725 : ℚ) / 7744873648128786432

def SurrogateDiagonalTailChunk001Sub000Block006Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16781
    = surrogateDiagTailX0RatChunk001Sub000Block006Part023

theorem surrogateDiagonalTailChunk001Sub000Block006Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block006Part023CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block006Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block006Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block006Part023CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block006Part023SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block006Part023] using hcert

def TailChunk001Sub000Block006Part024SupportExplicit : Finset ℕ :=
  ([16782] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block006Part024 : ℚ :=
  (1222010374175 : ℚ) / 1222546858948813824

def SurrogateDiagonalTailChunk001Sub000Block006Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16782
    = surrogateDiagTailX0RatChunk001Sub000Block006Part024

theorem surrogateDiagonalTailChunk001Sub000Block006Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block006Part024CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block006Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block006Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block006Part024CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block006Part024SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block006Part024] using hcert

def surrogateDiagonalTailChunk001Sub000Block006HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block006Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block006Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block006Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block006Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block006Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block006Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block006Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block006Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block006Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block006Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block006Head : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block006Part000
    + surrogateDiagTailX0RatChunk001Sub000Block006Part001
    + surrogateDiagTailX0RatChunk001Sub000Block006Part002
    + surrogateDiagTailX0RatChunk001Sub000Block006Part003
    + surrogateDiagTailX0RatChunk001Sub000Block006Part004
    + surrogateDiagTailX0RatChunk001Sub000Block006Part005
    + surrogateDiagTailX0RatChunk001Sub000Block006Part006
    + surrogateDiagTailX0RatChunk001Sub000Block006Part007
    + surrogateDiagTailX0RatChunk001Sub000Block006Part008
    + surrogateDiagTailX0RatChunk001Sub000Block006Part009

def surrogateDiagonalTailChunk001Sub000Block006MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block006Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block006Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block006Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block006Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block006Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block006Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block006Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block006Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block006Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block006Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block006Mid : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block006Part010
    + surrogateDiagTailX0RatChunk001Sub000Block006Part011
    + surrogateDiagTailX0RatChunk001Sub000Block006Part012
    + surrogateDiagTailX0RatChunk001Sub000Block006Part013
    + surrogateDiagTailX0RatChunk001Sub000Block006Part014
    + surrogateDiagTailX0RatChunk001Sub000Block006Part015
    + surrogateDiagTailX0RatChunk001Sub000Block006Part016
    + surrogateDiagTailX0RatChunk001Sub000Block006Part017
    + surrogateDiagTailX0RatChunk001Sub000Block006Part018
    + surrogateDiagTailX0RatChunk001Sub000Block006Part019

def surrogateDiagonalTailChunk001Sub000Block006TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block006Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block006Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block006Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block006Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block006Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block006Tail : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block006Part020
    + surrogateDiagTailX0RatChunk001Sub000Block006Part021
    + surrogateDiagTailX0RatChunk001Sub000Block006Part022
    + surrogateDiagTailX0RatChunk001Sub000Block006Part023
    + surrogateDiagTailX0RatChunk001Sub000Block006Part024

def surrogateDiagonalTailChunk001Sub000Block006Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk001Sub000Block006HeadSum X0
    + surrogateDiagonalTailChunk001Sub000Block006MidSum X0
    + surrogateDiagonalTailChunk001Sub000Block006TailSum X0

def surrogateDiagTailX0RatChunk001Sub000Block006 : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block006Part000
    + surrogateDiagTailX0RatChunk001Sub000Block006Part001
    + surrogateDiagTailX0RatChunk001Sub000Block006Part002
    + surrogateDiagTailX0RatChunk001Sub000Block006Part003
    + surrogateDiagTailX0RatChunk001Sub000Block006Part004
    + surrogateDiagTailX0RatChunk001Sub000Block006Part005
    + surrogateDiagTailX0RatChunk001Sub000Block006Part006
    + surrogateDiagTailX0RatChunk001Sub000Block006Part007
    + surrogateDiagTailX0RatChunk001Sub000Block006Part008
    + surrogateDiagTailX0RatChunk001Sub000Block006Part009
    + surrogateDiagTailX0RatChunk001Sub000Block006Part010
    + surrogateDiagTailX0RatChunk001Sub000Block006Part011
    + surrogateDiagTailX0RatChunk001Sub000Block006Part012
    + surrogateDiagTailX0RatChunk001Sub000Block006Part013
    + surrogateDiagTailX0RatChunk001Sub000Block006Part014
    + surrogateDiagTailX0RatChunk001Sub000Block006Part015
    + surrogateDiagTailX0RatChunk001Sub000Block006Part016
    + surrogateDiagTailX0RatChunk001Sub000Block006Part017
    + surrogateDiagTailX0RatChunk001Sub000Block006Part018
    + surrogateDiagTailX0RatChunk001Sub000Block006Part019
    + surrogateDiagTailX0RatChunk001Sub000Block006Part020
    + surrogateDiagTailX0RatChunk001Sub000Block006Part021
    + surrogateDiagTailX0RatChunk001Sub000Block006Part022
    + surrogateDiagTailX0RatChunk001Sub000Block006Part023
    + surrogateDiagTailX0RatChunk001Sub000Block006Part024

theorem surrogateDiagTailX0RatChunk001Sub000Block006_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk001Sub000Block006Head + surrogateDiagTailX0RatChunk001Sub000Block006Mid + surrogateDiagTailX0RatChunk001Sub000Block006Tail =
      surrogateDiagTailX0RatChunk001Sub000Block006 := by
  unfold surrogateDiagTailX0RatChunk001Sub000Block006Head surrogateDiagTailX0RatChunk001Sub000Block006Mid surrogateDiagTailX0RatChunk001Sub000Block006Tail surrogateDiagTailX0RatChunk001Sub000Block006
  ring

def SurrogateDiagonalTailChunk001Sub000Block006HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block006HeadSum X0 = surrogateDiagTailX0RatChunk001Sub000Block006Head

def SurrogateDiagonalTailChunk001Sub000Block006MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block006MidSum X0 = surrogateDiagTailX0RatChunk001Sub000Block006Mid

def SurrogateDiagonalTailChunk001Sub000Block006TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block006TailSum X0 = surrogateDiagTailX0RatChunk001Sub000Block006Tail

theorem surrogateDiagonalTailChunk001Sub000Block006_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk001Sub000Block006HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk001Sub000Block006MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk001Sub000Block006TailCertificateAt X0) :
    surrogateDiagonalTailChunk001Sub000Block006Sum X0 = surrogateDiagTailX0RatChunk001Sub000Block006 := by
  unfold SurrogateDiagonalTailChunk001Sub000Block006HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk001Sub000Block006MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk001Sub000Block006TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk001Sub000Block006Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk001Sub000Block006_eq_head_add_mid_add_tail

/-- Block 007 covers tail-support indices [10175,10200) and q from 16783 to 16826. -/

def TailChunk001Sub000Block007Part000SupportExplicit : Finset ℕ :=
  ([16783] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block007Part000 : ℚ :=
  (152940352423 : ℚ) / 1435855328747020800

def SurrogateDiagonalTailChunk001Sub000Block007Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16783
    = surrogateDiagTailX0RatChunk001Sub000Block007Part000

theorem surrogateDiagonalTailChunk001Sub000Block007Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block007Part000CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block007Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block007Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block007Part000CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block007Part000SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block007Part000] using hcert

def TailChunk001Sub000Block007Part001SupportExplicit : Finset ℕ :=
  ([16786] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block007Part001 : ℚ :=
  (60404058983 : ℚ) / 88177316544921600

def SurrogateDiagonalTailChunk001Sub000Block007Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16786
    = surrogateDiagTailX0RatChunk001Sub000Block007Part001

theorem surrogateDiagonalTailChunk001Sub000Block007Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block007Part001CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block007Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block007Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block007Part001CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block007Part001SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block007Part001] using hcert

def TailChunk001Sub000Block007Part002SupportExplicit : Finset ℕ :=
  ([16787] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block007Part002 : ℚ :=
  (4403177640625 : ℚ) / 49631310488418245202

def SurrogateDiagonalTailChunk001Sub000Block007Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16787
    = surrogateDiagTailX0RatChunk001Sub000Block007Part002

theorem surrogateDiagonalTailChunk001Sub000Block007Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block007Part002CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block007Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block007Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block007Part002CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block007Part002SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block007Part002] using hcert

def TailChunk001Sub000Block007Part003SupportExplicit : Finset ℕ :=
  ([16789] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block007Part003 : ℚ :=
  (1905214283275 : ℚ) / 20713099655104866432

def SurrogateDiagonalTailChunk001Sub000Block007Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16789
    = surrogateDiagTailX0RatChunk001Sub000Block007Part003

theorem surrogateDiagonalTailChunk001Sub000Block007Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block007Part003CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block007Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block007Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block007Part003CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block007Part003SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block007Part003] using hcert

def TailChunk001Sub000Block007Part004SupportExplicit : Finset ℕ :=
  ([16790] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block007Part004 : ℚ :=
  (978185236975 : ℚ) / 1343279164488155136

def SurrogateDiagonalTailChunk001Sub000Block007Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16790
    = surrogateDiagTailX0RatChunk001Sub000Block007Part004

theorem surrogateDiagonalTailChunk001Sub000Block007Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block007Part004CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block007Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block007Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block007Part004CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block007Part004SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block007Part004] using hcert

def TailChunk001Sub000Block007Part005SupportExplicit : Finset ℕ :=
  ([16791] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block007Part005 : ℚ :=
  (1050771707725 : ℚ) / 4774037672001798144

def SurrogateDiagonalTailChunk001Sub000Block007Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16791
    = surrogateDiagTailX0RatChunk001Sub000Block007Part005

theorem surrogateDiagonalTailChunk001Sub000Block007Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block007Part005CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block007Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block007Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block007Part005CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block007Part005SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block007Part005] using hcert

def TailChunk001Sub000Block007Part006SupportExplicit : Finset ℕ :=
  ([16793] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block007Part006 : ℚ :=
  (13300541911225 : ℚ) / 107158981079533603968

def SurrogateDiagonalTailChunk001Sub000Block007Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16793
    = surrogateDiagTailX0RatChunk001Sub000Block007Part006

theorem surrogateDiagonalTailChunk001Sub000Block007Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block007Part006CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block007Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block007Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block007Part006CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block007Part006SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block007Part006] using hcert

def TailChunk001Sub000Block007Part007SupportExplicit : Finset ℕ :=
  ([16795] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block007Part007 : ℚ :=
  (11983302305725 : ℚ) / 81393475155076466688

def SurrogateDiagonalTailChunk001Sub000Block007Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16795
    = surrogateDiagTailX0RatChunk001Sub000Block007Part007

theorem surrogateDiagonalTailChunk001Sub000Block007Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block007Part007CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block007Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block007Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block007Part007CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block007Part007SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block007Part007] using hcert

def TailChunk001Sub000Block007Part008SupportExplicit : Finset ℕ :=
  ([16797] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block007Part008 : ℚ :=
  (6699400999 : ℚ) / 26644139000647680

def SurrogateDiagonalTailChunk001Sub000Block007Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16797
    = surrogateDiagTailX0RatChunk001Sub000Block007Part008

theorem surrogateDiagonalTailChunk001Sub000Block007Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block007Part008CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block007Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block007Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block007Part008CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block007Part008SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block007Part008] using hcert

def TailChunk001Sub000Block007Part009SupportExplicit : Finset ℕ :=
  ([16798] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block007Part009 : ℚ :=
  (3659763625 : ℚ) / 9510823877938704

def SurrogateDiagonalTailChunk001Sub000Block007Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16798
    = surrogateDiagTailX0RatChunk001Sub000Block007Part009

theorem surrogateDiagonalTailChunk001Sub000Block007Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block007Part009CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block007Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block007Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block007Part009CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block007Part009SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block007Part009] using hcert

def TailChunk001Sub000Block007Part010SupportExplicit : Finset ℕ :=
  ([16799] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block007Part010 : ℚ :=
  (17171427231025 : ℚ) / 186960006016737527808

def SurrogateDiagonalTailChunk001Sub000Block007Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16799
    = surrogateDiagTailX0RatChunk001Sub000Block007Part010

theorem surrogateDiagonalTailChunk001Sub000Block007Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block007Part010CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block007Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block007Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block007Part010CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block007Part010SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block007Part010] using hcert

def TailChunk001Sub000Block007Part011SupportExplicit : Finset ℕ :=
  ([16801] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block007Part011 : ℚ :=
  (16987158118825 : ℚ) / 182300795550709874688

def SurrogateDiagonalTailChunk001Sub000Block007Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16801
    = surrogateDiagTailX0RatChunk001Sub000Block007Part011

theorem surrogateDiagonalTailChunk001Sub000Block007Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block007Part011CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block007Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block007Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block007Part011CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block007Part011SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block007Part011] using hcert

def TailChunk001Sub000Block007Part012SupportExplicit : Finset ℕ :=
  ([16802] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block007Part012 : ℚ :=
  (167522565517 : ℚ) / 430553303442000000

def SurrogateDiagonalTailChunk001Sub000Block007Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16802
    = surrogateDiagTailX0RatChunk001Sub000Block007Part012

theorem surrogateDiagonalTailChunk001Sub000Block007Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block007Part012CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block007Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block007Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block007Part012CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block007Part012SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block007Part012] using hcert

def TailChunk001Sub000Block007Part013SupportExplicit : Finset ℕ :=
  ([16805] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block007Part013 : ℚ :=
  (479903175979 : ℚ) / 3263502314844979200

def SurrogateDiagonalTailChunk001Sub000Block007Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16805
    = surrogateDiagTailX0RatChunk001Sub000Block007Part013

theorem surrogateDiagonalTailChunk001Sub000Block007Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block007Part013CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block007Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block007Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block007Part013CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block007Part013SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block007Part013] using hcert

def TailChunk001Sub000Block007Part014SupportExplicit : Finset ℕ :=
  ([16806] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block007Part014 : ℚ :=
  (49020337349 : ℚ) / 49182314496000000

def SurrogateDiagonalTailChunk001Sub000Block007Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16806
    = surrogateDiagTailX0RatChunk001Sub000Block007Part014

theorem surrogateDiagonalTailChunk001Sub000Block007Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block007Part014CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block007Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block007Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block007Part014CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block007Part014SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block007Part014] using hcert

def TailChunk001Sub000Block007Part015SupportExplicit : Finset ℕ :=
  ([16809] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block007Part015 : ℚ :=
  (18355604131 : ℚ) / 75633531720007680

def SurrogateDiagonalTailChunk001Sub000Block007Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16809
    = surrogateDiagTailX0RatChunk001Sub000Block007Part015

theorem surrogateDiagonalTailChunk001Sub000Block007Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block007Part015CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block007Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block007Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block007Part015CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block007Part015SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block007Part015] using hcert

def TailChunk001Sub000Block007Part016SupportExplicit : Finset ℕ :=
  ([16811] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block007Part016 : ℚ :=
  (7065243025 : ℚ) / 79865222141668242

def SurrogateDiagonalTailChunk001Sub000Block007Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16811
    = surrogateDiagTailX0RatChunk001Sub000Block007Part016

theorem surrogateDiagonalTailChunk001Sub000Block007Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block007Part016CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block007Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block007Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block007Part016CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block007Part016SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block007Part016] using hcert

def TailChunk001Sub000Block007Part017SupportExplicit : Finset ℕ :=
  ([16813] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block007Part017 : ℚ :=
  (7079833848275 : ℚ) / 59726171739556675584

def SurrogateDiagonalTailChunk001Sub000Block007Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16813
    = surrogateDiagTailX0RatChunk001Sub000Block007Part017

theorem surrogateDiagonalTailChunk001Sub000Block007Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block007Part017CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block007Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block007Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block007Part017CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block007Part017SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block007Part017] using hcert

def TailChunk001Sub000Block007Part018SupportExplicit : Finset ℕ :=
  ([16814] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block007Part018 : ℚ :=
  (7805359631 : ℚ) / 14932905984000000

def SurrogateDiagonalTailChunk001Sub000Block007Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16814
    = surrogateDiagTailX0RatChunk001Sub000Block007Part018

theorem surrogateDiagonalTailChunk001Sub000Block007Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block007Part018CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block007Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block007Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block007Part018CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block007Part018SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block007Part018] using hcert

def TailChunk001Sub000Block007Part019SupportExplicit : Finset ℕ :=
  ([16815] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block007Part019 : ℚ :=
  (1647722769475 : ℚ) / 4055716100071489536

def SurrogateDiagonalTailChunk001Sub000Block007Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16815
    = surrogateDiagTailX0RatChunk001Sub000Block007Part019

theorem surrogateDiagonalTailChunk001Sub000Block007Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block007Part019CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block007Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block007Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block007Part019CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block007Part019SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block007Part019] using hcert

def TailChunk001Sub000Block007Part020SupportExplicit : Finset ℕ :=
  ([16817] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block007Part020 : ℚ :=
  (38017788491 : ℚ) / 411860480625000000

def SurrogateDiagonalTailChunk001Sub000Block007Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16817
    = surrogateDiagTailX0RatChunk001Sub000Block007Part020

theorem surrogateDiagonalTailChunk001Sub000Block007Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block007Part020CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block007Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block007Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block007Part020CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block007Part020SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block007Part020] using hcert

def TailChunk001Sub000Block007Part021SupportExplicit : Finset ℕ :=
  ([16818] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block007Part021 : ℚ :=
  (76703708675 : ℚ) / 77067165663082404

def SurrogateDiagonalTailChunk001Sub000Block007Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16818
    = surrogateDiagTailX0RatChunk001Sub000Block007Part021

theorem surrogateDiagonalTailChunk001Sub000Block007Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block007Part021CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block007Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block007Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block007Part021CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block007Part021SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block007Part021] using hcert

def TailChunk001Sub000Block007Part022SupportExplicit : Finset ℕ :=
  ([16822] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block007Part022 : ℚ :=
  (657136958875 : ℚ) / 1504979778684423168

def SurrogateDiagonalTailChunk001Sub000Block007Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16822
    = surrogateDiagTailX0RatChunk001Sub000Block007Part022

theorem surrogateDiagonalTailChunk001Sub000Block007Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block007Part022CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block007Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block007Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block007Part022CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block007Part022SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block007Part022] using hcert

def TailChunk001Sub000Block007Part023SupportExplicit : Finset ℕ :=
  ([16823] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block007Part023 : ℚ :=
  (4422083265625 : ℚ) / 50058448160657002482

def SurrogateDiagonalTailChunk001Sub000Block007Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16823
    = surrogateDiagTailX0RatChunk001Sub000Block007Part023

theorem surrogateDiagonalTailChunk001Sub000Block007Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block007Part023CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block007Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block007Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block007Part023CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block007Part023SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block007Part023] using hcert

def TailChunk001Sub000Block007Part024SupportExplicit : Finset ℕ :=
  ([16826] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block007Part024 : ℚ :=
  (30859214625 : ℚ) / 81444002476399936

def SurrogateDiagonalTailChunk001Sub000Block007Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16826
    = surrogateDiagTailX0RatChunk001Sub000Block007Part024

theorem surrogateDiagonalTailChunk001Sub000Block007Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block007Part024CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block007Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block007Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block007Part024CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block007Part024SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block007Part024] using hcert

def surrogateDiagonalTailChunk001Sub000Block007HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block007Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block007Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block007Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block007Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block007Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block007Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block007Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block007Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block007Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block007Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block007Head : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block007Part000
    + surrogateDiagTailX0RatChunk001Sub000Block007Part001
    + surrogateDiagTailX0RatChunk001Sub000Block007Part002
    + surrogateDiagTailX0RatChunk001Sub000Block007Part003
    + surrogateDiagTailX0RatChunk001Sub000Block007Part004
    + surrogateDiagTailX0RatChunk001Sub000Block007Part005
    + surrogateDiagTailX0RatChunk001Sub000Block007Part006
    + surrogateDiagTailX0RatChunk001Sub000Block007Part007
    + surrogateDiagTailX0RatChunk001Sub000Block007Part008
    + surrogateDiagTailX0RatChunk001Sub000Block007Part009

def surrogateDiagonalTailChunk001Sub000Block007MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block007Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block007Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block007Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block007Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block007Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block007Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block007Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block007Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block007Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block007Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block007Mid : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block007Part010
    + surrogateDiagTailX0RatChunk001Sub000Block007Part011
    + surrogateDiagTailX0RatChunk001Sub000Block007Part012
    + surrogateDiagTailX0RatChunk001Sub000Block007Part013
    + surrogateDiagTailX0RatChunk001Sub000Block007Part014
    + surrogateDiagTailX0RatChunk001Sub000Block007Part015
    + surrogateDiagTailX0RatChunk001Sub000Block007Part016
    + surrogateDiagTailX0RatChunk001Sub000Block007Part017
    + surrogateDiagTailX0RatChunk001Sub000Block007Part018
    + surrogateDiagTailX0RatChunk001Sub000Block007Part019

def surrogateDiagonalTailChunk001Sub000Block007TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block007Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block007Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block007Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block007Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block007Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block007Tail : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block007Part020
    + surrogateDiagTailX0RatChunk001Sub000Block007Part021
    + surrogateDiagTailX0RatChunk001Sub000Block007Part022
    + surrogateDiagTailX0RatChunk001Sub000Block007Part023
    + surrogateDiagTailX0RatChunk001Sub000Block007Part024

def surrogateDiagonalTailChunk001Sub000Block007Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk001Sub000Block007HeadSum X0
    + surrogateDiagonalTailChunk001Sub000Block007MidSum X0
    + surrogateDiagonalTailChunk001Sub000Block007TailSum X0

def surrogateDiagTailX0RatChunk001Sub000Block007 : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block007Part000
    + surrogateDiagTailX0RatChunk001Sub000Block007Part001
    + surrogateDiagTailX0RatChunk001Sub000Block007Part002
    + surrogateDiagTailX0RatChunk001Sub000Block007Part003
    + surrogateDiagTailX0RatChunk001Sub000Block007Part004
    + surrogateDiagTailX0RatChunk001Sub000Block007Part005
    + surrogateDiagTailX0RatChunk001Sub000Block007Part006
    + surrogateDiagTailX0RatChunk001Sub000Block007Part007
    + surrogateDiagTailX0RatChunk001Sub000Block007Part008
    + surrogateDiagTailX0RatChunk001Sub000Block007Part009
    + surrogateDiagTailX0RatChunk001Sub000Block007Part010
    + surrogateDiagTailX0RatChunk001Sub000Block007Part011
    + surrogateDiagTailX0RatChunk001Sub000Block007Part012
    + surrogateDiagTailX0RatChunk001Sub000Block007Part013
    + surrogateDiagTailX0RatChunk001Sub000Block007Part014
    + surrogateDiagTailX0RatChunk001Sub000Block007Part015
    + surrogateDiagTailX0RatChunk001Sub000Block007Part016
    + surrogateDiagTailX0RatChunk001Sub000Block007Part017
    + surrogateDiagTailX0RatChunk001Sub000Block007Part018
    + surrogateDiagTailX0RatChunk001Sub000Block007Part019
    + surrogateDiagTailX0RatChunk001Sub000Block007Part020
    + surrogateDiagTailX0RatChunk001Sub000Block007Part021
    + surrogateDiagTailX0RatChunk001Sub000Block007Part022
    + surrogateDiagTailX0RatChunk001Sub000Block007Part023
    + surrogateDiagTailX0RatChunk001Sub000Block007Part024

theorem surrogateDiagTailX0RatChunk001Sub000Block007_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk001Sub000Block007Head + surrogateDiagTailX0RatChunk001Sub000Block007Mid + surrogateDiagTailX0RatChunk001Sub000Block007Tail =
      surrogateDiagTailX0RatChunk001Sub000Block007 := by
  unfold surrogateDiagTailX0RatChunk001Sub000Block007Head surrogateDiagTailX0RatChunk001Sub000Block007Mid surrogateDiagTailX0RatChunk001Sub000Block007Tail surrogateDiagTailX0RatChunk001Sub000Block007
  ring

def SurrogateDiagonalTailChunk001Sub000Block007HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block007HeadSum X0 = surrogateDiagTailX0RatChunk001Sub000Block007Head

def SurrogateDiagonalTailChunk001Sub000Block007MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block007MidSum X0 = surrogateDiagTailX0RatChunk001Sub000Block007Mid

def SurrogateDiagonalTailChunk001Sub000Block007TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block007TailSum X0 = surrogateDiagTailX0RatChunk001Sub000Block007Tail

theorem surrogateDiagonalTailChunk001Sub000Block007_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk001Sub000Block007HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk001Sub000Block007MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk001Sub000Block007TailCertificateAt X0) :
    surrogateDiagonalTailChunk001Sub000Block007Sum X0 = surrogateDiagTailX0RatChunk001Sub000Block007 := by
  unfold SurrogateDiagonalTailChunk001Sub000Block007HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk001Sub000Block007MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk001Sub000Block007TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk001Sub000Block007Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk001Sub000Block007_eq_head_add_mid_add_tail

/-- Block 008 covers tail-support indices [10200,10225) and q from 16827 to 16867. -/

def TailChunk001Sub000Block008Part000SupportExplicit : Finset ℕ :=
  ([16827] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block008Part000 : ℚ :=
  (8379064769 : ℚ) / 39507077371507200

def SurrogateDiagonalTailChunk001Sub000Block008Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16827
    = surrogateDiagTailX0RatChunk001Sub000Block008Part000

theorem surrogateDiagonalTailChunk001Sub000Block008Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block008Part000CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block008Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block008Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block008Part000CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block008Part000SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block008Part000] using hcert

def TailChunk001Sub000Block008Part001SupportExplicit : Finset ℕ :=
  ([16829] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block008Part001 : ℚ :=
  (4425238140625 : ℚ) / 50129904924157753632

def SurrogateDiagonalTailChunk001Sub000Block008Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16829
    = surrogateDiagTailX0RatChunk001Sub000Block008Part001

theorem surrogateDiagonalTailChunk001Sub000Block008Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block008Part001CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block008Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block008Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block008Part001CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block008Part001SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block008Part001] using hcert

def TailChunk001Sub000Block008Part002SupportExplicit : Finset ℕ :=
  ([16831] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block008Part002 : ℚ :=
  (7082064025 : ℚ) / 80245985339080242

def SurrogateDiagonalTailChunk001Sub000Block008Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16831
    = surrogateDiagTailX0RatChunk001Sub000Block008Part002

theorem surrogateDiagonalTailChunk001Sub000Block008Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block008Part002CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block008Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block008Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block008Part002CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block008Part002SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block008Part002] using hcert

def TailChunk001Sub000Block008Part003SupportExplicit : Finset ℕ :=
  ([16833] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block008Part003 : ℚ :=
  (148358261021 : ℚ) / 680380528896000000

def SurrogateDiagonalTailChunk001Sub000Block008Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16833
    = surrogateDiagTailX0RatChunk001Sub000Block008Part003

theorem surrogateDiagonalTailChunk001Sub000Block008Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block008Part003CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block008Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block008Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block008Part003CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block008Part003SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block008Part003] using hcert

def TailChunk001Sub000Block008Part004SupportExplicit : Finset ℕ :=
  ([16834] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block008Part004 : ℚ :=
  (46555194925 : ℚ) / 3339525023000390016

def SurrogateDiagonalTailChunk001Sub000Block008Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16834
    = surrogateDiagTailX0RatChunk001Sub000Block008Part004

theorem surrogateDiagonalTailChunk001Sub000Block008Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block008Part004CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block008Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block008Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block008Part004CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block008Part004SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block008Part004] using hcert

def TailChunk001Sub000Block008Part005SupportExplicit : Finset ℕ :=
  ([16835] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block008Part005 : ℚ :=
  (98609782075 : ℚ) / 2407828590453325824

def SurrogateDiagonalTailChunk001Sub000Block008Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16835
    = surrogateDiagTailX0RatChunk001Sub000Block008Part005

theorem surrogateDiagonalTailChunk001Sub000Block008Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block008Part005CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block008Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block008Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block008Part005CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block008Part005SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block008Part005] using hcert

def TailChunk001Sub000Block008Part006SupportExplicit : Finset ℕ :=
  ([16837] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block008Part006 : ℚ :=
  (81818520475 : ℚ) / 188775579070746329088

def SurrogateDiagonalTailChunk001Sub000Block008Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16837
    = surrogateDiagTailX0RatChunk001Sub000Block008Part006

theorem surrogateDiagonalTailChunk001Sub000Block008Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block008Part006CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block008Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block008Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block008Part006CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block008Part006SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block008Part006] using hcert

def TailChunk001Sub000Block008Part007SupportExplicit : Finset ℕ :=
  ([16838] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block008Part007 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block008Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16838
    = surrogateDiagTailX0RatChunk001Sub000Block008Part007

theorem surrogateDiagonalTailChunk001Sub000Block008Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block008Part007CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block008Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block008Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block008Part007CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block008Part007SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block008Part007] using hcert

def TailChunk001Sub000Block008Part008SupportExplicit : Finset ℕ :=
  ([16841] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block008Part008 : ℚ :=
  (17674827667 : ℚ) / 5480908772562000000

def SurrogateDiagonalTailChunk001Sub000Block008Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16841
    = surrogateDiagTailX0RatChunk001Sub000Block008Part008

theorem surrogateDiagonalTailChunk001Sub000Block008Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block008Part008CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block008Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block008Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block008Part008CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block008Part008SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block008Part008] using hcert

def TailChunk001Sub000Block008Part009SupportExplicit : Finset ℕ :=
  ([16842] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block008Part009 : ℚ :=
  (894508909 : ℚ) / 1966473216000000

def SurrogateDiagonalTailChunk001Sub000Block008Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16842
    = surrogateDiagTailX0RatChunk001Sub000Block008Part009

theorem surrogateDiagonalTailChunk001Sub000Block008Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block008Part009CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block008Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block008Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block008Part009CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block008Part009SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block008Part009] using hcert

def TailChunk001Sub000Block008Part010SupportExplicit : Finset ℕ :=
  ([16843] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block008Part010 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block008Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16843
    = surrogateDiagTailX0RatChunk001Sub000Block008Part010

theorem surrogateDiagonalTailChunk001Sub000Block008Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block008Part010CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block008Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block008Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block008Part010CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block008Part010SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block008Part010] using hcert

def TailChunk001Sub000Block008Part011SupportExplicit : Finset ℕ :=
  ([16845] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block008Part011 : ℚ :=
  (553356043675 : ℚ) / 16231484244388773888

def SurrogateDiagonalTailChunk001Sub000Block008Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16845
    = surrogateDiagTailX0RatChunk001Sub000Block008Part011

theorem surrogateDiagonalTailChunk001Sub000Block008Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block008Part011CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block008Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block008Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block008Part011CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block008Part011SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block008Part011] using hcert

def TailChunk001Sub000Block008Part012SupportExplicit : Finset ℕ :=
  ([16846] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block008Part012 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block008Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16846
    = surrogateDiagTailX0RatChunk001Sub000Block008Part012

theorem surrogateDiagonalTailChunk001Sub000Block008Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block008Part012CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block008Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block008Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block008Part012CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block008Part012SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block008Part012] using hcert

def TailChunk001Sub000Block008Part013SupportExplicit : Finset ℕ :=
  ([16847] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block008Part013 : ℚ :=
  (12441394081 : ℚ) / 6296621083538227200

def SurrogateDiagonalTailChunk001Sub000Block008Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16847
    = surrogateDiagTailX0RatChunk001Sub000Block008Part013

theorem surrogateDiagonalTailChunk001Sub000Block008Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block008Part013CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block008Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block008Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block008Part013CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block008Part013SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block008Part013] using hcert

def TailChunk001Sub000Block008Part014SupportExplicit : Finset ℕ :=
  ([16849] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block008Part014 : ℚ :=
  (13759527625 : ℚ) / 1429482509408894976

def SurrogateDiagonalTailChunk001Sub000Block008Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16849
    = surrogateDiagTailX0RatChunk001Sub000Block008Part014

theorem surrogateDiagonalTailChunk001Sub000Block008Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block008Part014CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block008Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block008Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block008Part014CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block008Part014SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block008Part014] using hcert

def TailChunk001Sub000Block008Part015SupportExplicit : Finset ℕ :=
  ([16851] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block008Part015 : ℚ :=
  (1456195689 : ℚ) / 467176702502502400

def SurrogateDiagonalTailChunk001Sub000Block008Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16851
    = surrogateDiagTailX0RatChunk001Sub000Block008Part015

theorem surrogateDiagonalTailChunk001Sub000Block008Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block008Part015CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block008Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block008Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block008Part015CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block008Part015SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block008Part015] using hcert

def TailChunk001Sub000Block008Part016SupportExplicit : Finset ℕ :=
  ([16853] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block008Part016 : ℚ :=
  (149850742475 : ℚ) / 80876392484587619904

def SurrogateDiagonalTailChunk001Sub000Block008Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16853
    = surrogateDiagTailX0RatChunk001Sub000Block008Part016

theorem surrogateDiagonalTailChunk001Sub000Block008Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block008Part016CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block008Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block008Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block008Part016CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block008Part016SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block008Part016] using hcert

def TailChunk001Sub000Block008Part017SupportExplicit : Finset ℕ :=
  ([16855] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block008Part017 : ℚ :=
  (1896152043 : ℚ) / 220168488013690880

def SurrogateDiagonalTailChunk001Sub000Block008Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16855
    = surrogateDiagTailX0RatChunk001Sub000Block008Part017

theorem surrogateDiagonalTailChunk001Sub000Block008Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block008Part017CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block008Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block008Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block008Part017CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block008Part017SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block008Part017] using hcert

def TailChunk001Sub000Block008Part018SupportExplicit : Finset ℕ :=
  ([16858] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block008Part018 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block008Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16858
    = surrogateDiagTailX0RatChunk001Sub000Block008Part018

theorem surrogateDiagonalTailChunk001Sub000Block008Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block008Part018CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block008Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block008Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block008Part018CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block008Part018SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block008Part018] using hcert

def TailChunk001Sub000Block008Part019SupportExplicit : Finset ℕ :=
  ([16859] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block008Part019 : ℚ :=
  (207597752575 : ℚ) / 168175182021446780928

def SurrogateDiagonalTailChunk001Sub000Block008Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16859
    = surrogateDiagTailX0RatChunk001Sub000Block008Part019

theorem surrogateDiagonalTailChunk001Sub000Block008Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block008Part019CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block008Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block008Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block008Part019CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block008Part019SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block008Part019] using hcert

def TailChunk001Sub000Block008Part020SupportExplicit : Finset ℕ :=
  ([16861] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block008Part020 : ℚ :=
  (211702510325 : ℚ) / 73137793435019771904

def SurrogateDiagonalTailChunk001Sub000Block008Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16861
    = surrogateDiagTailX0RatChunk001Sub000Block008Part020

theorem surrogateDiagonalTailChunk001Sub000Block008Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block008Part020CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block008Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block008Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block008Part020CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block008Part020SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block008Part020] using hcert

def TailChunk001Sub000Block008Part021SupportExplicit : Finset ℕ :=
  ([16862] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block008Part021 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block008Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16862
    = surrogateDiagTailX0RatChunk001Sub000Block008Part021

theorem surrogateDiagonalTailChunk001Sub000Block008Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block008Part021CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block008Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block008Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block008Part021CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block008Part021SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block008Part021] using hcert

def TailChunk001Sub000Block008Part022SupportExplicit : Finset ℕ :=
  ([16863] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block008Part022 : ℚ :=
  (24051591353 : ℚ) / 185789243090534400

def SurrogateDiagonalTailChunk001Sub000Block008Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16863
    = surrogateDiagTailX0RatChunk001Sub000Block008Part022

theorem surrogateDiagonalTailChunk001Sub000Block008Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block008Part022CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block008Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block008Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block008Part022CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block008Part022SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block008Part022] using hcert

def TailChunk001Sub000Block008Part023SupportExplicit : Finset ℕ :=
  ([16865] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block008Part023 : ℚ :=
  (711899765875 : ℚ) / 82759353237707194368

def SurrogateDiagonalTailChunk001Sub000Block008Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16865
    = surrogateDiagTailX0RatChunk001Sub000Block008Part023

theorem surrogateDiagonalTailChunk001Sub000Block008Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block008Part023CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block008Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block008Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block008Part023CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block008Part023SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block008Part023] using hcert

def TailChunk001Sub000Block008Part024SupportExplicit : Finset ℕ :=
  ([16867] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block008Part024 : ℚ :=
  (3248801191 : ℚ) / 7594850026272000000

def SurrogateDiagonalTailChunk001Sub000Block008Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16867
    = surrogateDiagTailX0RatChunk001Sub000Block008Part024

theorem surrogateDiagonalTailChunk001Sub000Block008Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block008Part024CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block008Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block008Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block008Part024CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block008Part024SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block008Part024] using hcert

def surrogateDiagonalTailChunk001Sub000Block008HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block008Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block008Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block008Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block008Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block008Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block008Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block008Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block008Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block008Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block008Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block008Head : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block008Part000
    + surrogateDiagTailX0RatChunk001Sub000Block008Part001
    + surrogateDiagTailX0RatChunk001Sub000Block008Part002
    + surrogateDiagTailX0RatChunk001Sub000Block008Part003
    + surrogateDiagTailX0RatChunk001Sub000Block008Part004
    + surrogateDiagTailX0RatChunk001Sub000Block008Part005
    + surrogateDiagTailX0RatChunk001Sub000Block008Part006
    + surrogateDiagTailX0RatChunk001Sub000Block008Part007
    + surrogateDiagTailX0RatChunk001Sub000Block008Part008
    + surrogateDiagTailX0RatChunk001Sub000Block008Part009

def surrogateDiagonalTailChunk001Sub000Block008MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block008Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block008Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block008Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block008Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block008Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block008Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block008Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block008Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block008Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block008Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block008Mid : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block008Part010
    + surrogateDiagTailX0RatChunk001Sub000Block008Part011
    + surrogateDiagTailX0RatChunk001Sub000Block008Part012
    + surrogateDiagTailX0RatChunk001Sub000Block008Part013
    + surrogateDiagTailX0RatChunk001Sub000Block008Part014
    + surrogateDiagTailX0RatChunk001Sub000Block008Part015
    + surrogateDiagTailX0RatChunk001Sub000Block008Part016
    + surrogateDiagTailX0RatChunk001Sub000Block008Part017
    + surrogateDiagTailX0RatChunk001Sub000Block008Part018
    + surrogateDiagTailX0RatChunk001Sub000Block008Part019

def surrogateDiagonalTailChunk001Sub000Block008TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block008Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block008Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block008Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block008Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block008Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block008Tail : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block008Part020
    + surrogateDiagTailX0RatChunk001Sub000Block008Part021
    + surrogateDiagTailX0RatChunk001Sub000Block008Part022
    + surrogateDiagTailX0RatChunk001Sub000Block008Part023
    + surrogateDiagTailX0RatChunk001Sub000Block008Part024

def surrogateDiagonalTailChunk001Sub000Block008Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk001Sub000Block008HeadSum X0
    + surrogateDiagonalTailChunk001Sub000Block008MidSum X0
    + surrogateDiagonalTailChunk001Sub000Block008TailSum X0

def surrogateDiagTailX0RatChunk001Sub000Block008 : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block008Part000
    + surrogateDiagTailX0RatChunk001Sub000Block008Part001
    + surrogateDiagTailX0RatChunk001Sub000Block008Part002
    + surrogateDiagTailX0RatChunk001Sub000Block008Part003
    + surrogateDiagTailX0RatChunk001Sub000Block008Part004
    + surrogateDiagTailX0RatChunk001Sub000Block008Part005
    + surrogateDiagTailX0RatChunk001Sub000Block008Part006
    + surrogateDiagTailX0RatChunk001Sub000Block008Part007
    + surrogateDiagTailX0RatChunk001Sub000Block008Part008
    + surrogateDiagTailX0RatChunk001Sub000Block008Part009
    + surrogateDiagTailX0RatChunk001Sub000Block008Part010
    + surrogateDiagTailX0RatChunk001Sub000Block008Part011
    + surrogateDiagTailX0RatChunk001Sub000Block008Part012
    + surrogateDiagTailX0RatChunk001Sub000Block008Part013
    + surrogateDiagTailX0RatChunk001Sub000Block008Part014
    + surrogateDiagTailX0RatChunk001Sub000Block008Part015
    + surrogateDiagTailX0RatChunk001Sub000Block008Part016
    + surrogateDiagTailX0RatChunk001Sub000Block008Part017
    + surrogateDiagTailX0RatChunk001Sub000Block008Part018
    + surrogateDiagTailX0RatChunk001Sub000Block008Part019
    + surrogateDiagTailX0RatChunk001Sub000Block008Part020
    + surrogateDiagTailX0RatChunk001Sub000Block008Part021
    + surrogateDiagTailX0RatChunk001Sub000Block008Part022
    + surrogateDiagTailX0RatChunk001Sub000Block008Part023
    + surrogateDiagTailX0RatChunk001Sub000Block008Part024

theorem surrogateDiagTailX0RatChunk001Sub000Block008_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk001Sub000Block008Head + surrogateDiagTailX0RatChunk001Sub000Block008Mid + surrogateDiagTailX0RatChunk001Sub000Block008Tail =
      surrogateDiagTailX0RatChunk001Sub000Block008 := by
  unfold surrogateDiagTailX0RatChunk001Sub000Block008Head surrogateDiagTailX0RatChunk001Sub000Block008Mid surrogateDiagTailX0RatChunk001Sub000Block008Tail surrogateDiagTailX0RatChunk001Sub000Block008
  ring

def SurrogateDiagonalTailChunk001Sub000Block008HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block008HeadSum X0 = surrogateDiagTailX0RatChunk001Sub000Block008Head

def SurrogateDiagonalTailChunk001Sub000Block008MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block008MidSum X0 = surrogateDiagTailX0RatChunk001Sub000Block008Mid

def SurrogateDiagonalTailChunk001Sub000Block008TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block008TailSum X0 = surrogateDiagTailX0RatChunk001Sub000Block008Tail

theorem surrogateDiagonalTailChunk001Sub000Block008_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk001Sub000Block008HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk001Sub000Block008MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk001Sub000Block008TailCertificateAt X0) :
    surrogateDiagonalTailChunk001Sub000Block008Sum X0 = surrogateDiagTailX0RatChunk001Sub000Block008 := by
  unfold SurrogateDiagonalTailChunk001Sub000Block008HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk001Sub000Block008MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk001Sub000Block008TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk001Sub000Block008Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk001Sub000Block008_eq_head_add_mid_add_tail

/-- Block 009 covers tail-support indices [10225,10250) and q from 16869 to 16906. -/

def TailChunk001Sub000Block009Part000SupportExplicit : Finset ℕ :=
  ([16869] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block009Part000 : ℚ :=
  (988027648475 : ℚ) / 19983898304253877824

def SurrogateDiagonalTailChunk001Sub000Block009Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16869
    = surrogateDiagTailX0RatChunk001Sub000Block009Part000

theorem surrogateDiagonalTailChunk001Sub000Block009Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block009Part000CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block009Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block009Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block009Part000CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block009Part000SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block009Part000] using hcert

def TailChunk001Sub000Block009Part001SupportExplicit : Finset ℕ :=
  ([16870] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block009Part001 : ℚ :=
  (7307845087 : ℚ) / 27524332309708800

def SurrogateDiagonalTailChunk001Sub000Block009Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16870
    = surrogateDiagTailX0RatChunk001Sub000Block009Part001

theorem surrogateDiagonalTailChunk001Sub000Block009Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block009Part001CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block009Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block009Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block009Part001CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block009Part001SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block009Part001] using hcert

def TailChunk001Sub000Block009Part002SupportExplicit : Finset ℕ :=
  ([16871] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block009Part002 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block009Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16871
    = surrogateDiagTailX0RatChunk001Sub000Block009Part002

theorem surrogateDiagonalTailChunk001Sub000Block009Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block009Part002CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block009Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block009Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block009Part002CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block009Part002SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block009Part002] using hcert

def TailChunk001Sub000Block009Part003SupportExplicit : Finset ℕ :=
  ([16873] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block009Part003 : ℚ :=
  (10514915025 : ℚ) / 15325302164701885024

def SurrogateDiagonalTailChunk001Sub000Block009Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16873
    = surrogateDiagTailX0RatChunk001Sub000Block009Part003

theorem surrogateDiagonalTailChunk001Sub000Block009Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block009Part003CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block009Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block009Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block009Part003CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block009Part003SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block009Part003] using hcert

def TailChunk001Sub000Block009Part004SupportExplicit : Finset ℕ :=
  ([16874] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block009Part004 : ℚ :=
  (17278876273 : ℚ) / 234705792828211200

def SurrogateDiagonalTailChunk001Sub000Block009Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16874
    = surrogateDiagTailX0RatChunk001Sub000Block009Part004

theorem surrogateDiagonalTailChunk001Sub000Block009Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block009Part004CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block009Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block009Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block009Part004CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block009Part004SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block009Part004] using hcert

def TailChunk001Sub000Block009Part005SupportExplicit : Finset ℕ :=
  ([16877] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block009Part005 : ℚ :=
  (14554842107 : ℚ) / 2186402052499905600

def SurrogateDiagonalTailChunk001Sub000Block009Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16877
    = surrogateDiagTailX0RatChunk001Sub000Block009Part005

theorem surrogateDiagonalTailChunk001Sub000Block009Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block009Part005CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block009Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block009Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block009Part005CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block009Part005SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block009Part005] using hcert

def TailChunk001Sub000Block009Part006SupportExplicit : Finset ℕ :=
  ([16878] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block009Part006 : ℚ :=
  (978467980075 : ℚ) / 2088641481500786688

def SurrogateDiagonalTailChunk001Sub000Block009Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16878
    = surrogateDiagTailX0RatChunk001Sub000Block009Part006

theorem surrogateDiagonalTailChunk001Sub000Block009Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block009Part006CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block009Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block009Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block009Part006CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block009Part006SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block009Part006] using hcert

def TailChunk001Sub000Block009Part007SupportExplicit : Finset ℕ :=
  ([16879] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block009Part007 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block009Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16879
    = surrogateDiagTailX0RatChunk001Sub000Block009Part007

theorem surrogateDiagonalTailChunk001Sub000Block009Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block009Part007CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block009Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block009Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block009Part007CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block009Part007SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block009Part007] using hcert

def TailChunk001Sub000Block009Part008SupportExplicit : Finset ℕ :=
  ([16881] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block009Part008 : ℚ :=
  (38995079507 : ℚ) / 621888502077849600

def SurrogateDiagonalTailChunk001Sub000Block009Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16881
    = surrogateDiagTailX0RatChunk001Sub000Block009Part008

theorem surrogateDiagonalTailChunk001Sub000Block009Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block009Part008CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block009Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block009Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block009Part008CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block009Part008SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block009Part008] using hcert

def TailChunk001Sub000Block009Part009SupportExplicit : Finset ℕ :=
  ([16882] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block009Part009 : ℚ :=
  (123769984975 : ℚ) / 10510948876340423808

def SurrogateDiagonalTailChunk001Sub000Block009Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16882
    = surrogateDiagTailX0RatChunk001Sub000Block009Part009

theorem surrogateDiagonalTailChunk001Sub000Block009Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block009Part009CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block009Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block009Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block009Part009CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block009Part009SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block009Part009] using hcert

def TailChunk001Sub000Block009Part010SupportExplicit : Finset ℕ :=
  ([16883] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block009Part010 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block009Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16883
    = surrogateDiagTailX0RatChunk001Sub000Block009Part010

theorem surrogateDiagonalTailChunk001Sub000Block009Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block009Part010CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block009Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block009Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block009Part010CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block009Part010SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block009Part010] using hcert

def TailChunk001Sub000Block009Part011SupportExplicit : Finset ℕ :=
  ([16885] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block009Part011 : ℚ :=
  (158155753 : ℚ) / 9354084305172480

def SurrogateDiagonalTailChunk001Sub000Block009Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16885
    = surrogateDiagTailX0RatChunk001Sub000Block009Part011

theorem surrogateDiagonalTailChunk001Sub000Block009Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block009Part011CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block009Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block009Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block009Part011CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block009Part011SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block009Part011] using hcert

def TailChunk001Sub000Block009Part012SupportExplicit : Finset ℕ :=
  ([16886] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block009Part012 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block009Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16886
    = surrogateDiagTailX0RatChunk001Sub000Block009Part012

theorem surrogateDiagonalTailChunk001Sub000Block009Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block009Part012CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block009Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block009Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block009Part012CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block009Part012SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block009Part012] using hcert

def TailChunk001Sub000Block009Part013SupportExplicit : Finset ℕ :=
  ([16887] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block009Part013 : ℚ :=
  (217263606325 : ℚ) / 3210438120604434432

def SurrogateDiagonalTailChunk001Sub000Block009Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16887
    = surrogateDiagTailX0RatChunk001Sub000Block009Part013

theorem surrogateDiagonalTailChunk001Sub000Block009Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block009Part013CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block009Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block009Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block009Part013CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block009Part013SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block009Part013] using hcert

def TailChunk001Sub000Block009Part014SupportExplicit : Finset ℕ :=
  ([16889] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block009Part014 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block009Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16889
    = surrogateDiagTailX0RatChunk001Sub000Block009Part014

theorem surrogateDiagonalTailChunk001Sub000Block009Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block009Part014CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block009Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block009Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block009Part014CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block009Part014SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block009Part014] using hcert

def TailChunk001Sub000Block009Part015SupportExplicit : Finset ℕ :=
  ([16890] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block009Part015 : ℚ :=
  (290330046075 : ℚ) / 340573470114021376

def SurrogateDiagonalTailChunk001Sub000Block009Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16890
    = surrogateDiagTailX0RatChunk001Sub000Block009Part015

theorem surrogateDiagonalTailChunk001Sub000Block009Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block009Part015CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block009Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block009Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block009Part015CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block009Part015SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block009Part015] using hcert

def TailChunk001Sub000Block009Part016SupportExplicit : Finset ℕ :=
  ([16891] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block009Part016 : ℚ :=
  (921189167425 : ℚ) / 85744063494864488448

def SurrogateDiagonalTailChunk001Sub000Block009Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16891
    = surrogateDiagTailX0RatChunk001Sub000Block009Part016

theorem surrogateDiagonalTailChunk001Sub000Block009Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block009Part016CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block009Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block009Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block009Part016CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block009Part016SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block009Part016] using hcert

def TailChunk001Sub000Block009Part017SupportExplicit : Finset ℕ :=
  ([16894] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block009Part017 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block009Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16894
    = surrogateDiagTailX0RatChunk001Sub000Block009Part017

theorem surrogateDiagonalTailChunk001Sub000Block009Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block009Part017CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block009Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block009Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block009Part017CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block009Part017SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block009Part017] using hcert

def TailChunk001Sub000Block009Part018SupportExplicit : Finset ℕ :=
  ([16895] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block009Part018 : ℚ :=
  (29608014119 : ℚ) / 1410837064718745600

def SurrogateDiagonalTailChunk001Sub000Block009Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16895
    = surrogateDiagTailX0RatChunk001Sub000Block009Part018

theorem surrogateDiagonalTailChunk001Sub000Block009Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block009Part018CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block009Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block009Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block009Part018CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block009Part018SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block009Part018] using hcert

def TailChunk001Sub000Block009Part019SupportExplicit : Finset ℕ :=
  ([16897] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block009Part019 : ℚ :=
  (3623107 : ℚ) / 6540792015863808

def SurrogateDiagonalTailChunk001Sub000Block009Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16897
    = surrogateDiagTailX0RatChunk001Sub000Block009Part019

theorem surrogateDiagonalTailChunk001Sub000Block009Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block009Part019CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block009Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block009Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block009Part019CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block009Part019SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block009Part019] using hcert

def TailChunk001Sub000Block009Part020SupportExplicit : Finset ℕ :=
  ([16898] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block009Part020 : ℚ :=
  (537943583 : ℚ) / 5827682705080320

def SurrogateDiagonalTailChunk001Sub000Block009Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16898
    = surrogateDiagTailX0RatChunk001Sub000Block009Part020

theorem surrogateDiagonalTailChunk001Sub000Block009Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block009Part020CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block009Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block009Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block009Part020CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block009Part020SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block009Part020] using hcert

def TailChunk001Sub000Block009Part021SupportExplicit : Finset ℕ :=
  ([16899] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block009Part021 : ℚ :=
  (11238046669 : ℚ) / 203179255053465600

def SurrogateDiagonalTailChunk001Sub000Block009Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16899
    = surrogateDiagTailX0RatChunk001Sub000Block009Part021

theorem surrogateDiagonalTailChunk001Sub000Block009Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block009Part021CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block009Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block009Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block009Part021CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block009Part021SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block009Part021] using hcert

def TailChunk001Sub000Block009Part022SupportExplicit : Finset ℕ :=
  ([16901] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block009Part022 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block009Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16901
    = surrogateDiagTailX0RatChunk001Sub000Block009Part022

theorem surrogateDiagonalTailChunk001Sub000Block009Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block009Part022CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block009Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block009Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block009Part022CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block009Part022SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block009Part022] using hcert

def TailChunk001Sub000Block009Part023SupportExplicit : Finset ℕ :=
  ([16903] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block009Part023 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block009Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16903
    = surrogateDiagTailX0RatChunk001Sub000Block009Part023

theorem surrogateDiagonalTailChunk001Sub000Block009Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block009Part023CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block009Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block009Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block009Part023CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block009Part023SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block009Part023] using hcert

def TailChunk001Sub000Block009Part024SupportExplicit : Finset ℕ :=
  ([16906] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block009Part024 : ℚ :=
  (56965515625 : ℚ) / 11685000376046095488

def SurrogateDiagonalTailChunk001Sub000Block009Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16906
    = surrogateDiagTailX0RatChunk001Sub000Block009Part024

theorem surrogateDiagonalTailChunk001Sub000Block009Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block009Part024CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block009Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block009Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block009Part024CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block009Part024SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block009Part024] using hcert

def surrogateDiagonalTailChunk001Sub000Block009HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block009Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block009Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block009Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block009Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block009Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block009Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block009Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block009Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block009Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block009Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block009Head : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block009Part000
    + surrogateDiagTailX0RatChunk001Sub000Block009Part001
    + surrogateDiagTailX0RatChunk001Sub000Block009Part002
    + surrogateDiagTailX0RatChunk001Sub000Block009Part003
    + surrogateDiagTailX0RatChunk001Sub000Block009Part004
    + surrogateDiagTailX0RatChunk001Sub000Block009Part005
    + surrogateDiagTailX0RatChunk001Sub000Block009Part006
    + surrogateDiagTailX0RatChunk001Sub000Block009Part007
    + surrogateDiagTailX0RatChunk001Sub000Block009Part008
    + surrogateDiagTailX0RatChunk001Sub000Block009Part009

def surrogateDiagonalTailChunk001Sub000Block009MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block009Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block009Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block009Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block009Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block009Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block009Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block009Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block009Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block009Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block009Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block009Mid : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block009Part010
    + surrogateDiagTailX0RatChunk001Sub000Block009Part011
    + surrogateDiagTailX0RatChunk001Sub000Block009Part012
    + surrogateDiagTailX0RatChunk001Sub000Block009Part013
    + surrogateDiagTailX0RatChunk001Sub000Block009Part014
    + surrogateDiagTailX0RatChunk001Sub000Block009Part015
    + surrogateDiagTailX0RatChunk001Sub000Block009Part016
    + surrogateDiagTailX0RatChunk001Sub000Block009Part017
    + surrogateDiagTailX0RatChunk001Sub000Block009Part018
    + surrogateDiagTailX0RatChunk001Sub000Block009Part019

def surrogateDiagonalTailChunk001Sub000Block009TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block009Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block009Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block009Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block009Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block009Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block009Tail : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block009Part020
    + surrogateDiagTailX0RatChunk001Sub000Block009Part021
    + surrogateDiagTailX0RatChunk001Sub000Block009Part022
    + surrogateDiagTailX0RatChunk001Sub000Block009Part023
    + surrogateDiagTailX0RatChunk001Sub000Block009Part024

def surrogateDiagonalTailChunk001Sub000Block009Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk001Sub000Block009HeadSum X0
    + surrogateDiagonalTailChunk001Sub000Block009MidSum X0
    + surrogateDiagonalTailChunk001Sub000Block009TailSum X0

def surrogateDiagTailX0RatChunk001Sub000Block009 : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block009Part000
    + surrogateDiagTailX0RatChunk001Sub000Block009Part001
    + surrogateDiagTailX0RatChunk001Sub000Block009Part002
    + surrogateDiagTailX0RatChunk001Sub000Block009Part003
    + surrogateDiagTailX0RatChunk001Sub000Block009Part004
    + surrogateDiagTailX0RatChunk001Sub000Block009Part005
    + surrogateDiagTailX0RatChunk001Sub000Block009Part006
    + surrogateDiagTailX0RatChunk001Sub000Block009Part007
    + surrogateDiagTailX0RatChunk001Sub000Block009Part008
    + surrogateDiagTailX0RatChunk001Sub000Block009Part009
    + surrogateDiagTailX0RatChunk001Sub000Block009Part010
    + surrogateDiagTailX0RatChunk001Sub000Block009Part011
    + surrogateDiagTailX0RatChunk001Sub000Block009Part012
    + surrogateDiagTailX0RatChunk001Sub000Block009Part013
    + surrogateDiagTailX0RatChunk001Sub000Block009Part014
    + surrogateDiagTailX0RatChunk001Sub000Block009Part015
    + surrogateDiagTailX0RatChunk001Sub000Block009Part016
    + surrogateDiagTailX0RatChunk001Sub000Block009Part017
    + surrogateDiagTailX0RatChunk001Sub000Block009Part018
    + surrogateDiagTailX0RatChunk001Sub000Block009Part019
    + surrogateDiagTailX0RatChunk001Sub000Block009Part020
    + surrogateDiagTailX0RatChunk001Sub000Block009Part021
    + surrogateDiagTailX0RatChunk001Sub000Block009Part022
    + surrogateDiagTailX0RatChunk001Sub000Block009Part023
    + surrogateDiagTailX0RatChunk001Sub000Block009Part024

theorem surrogateDiagTailX0RatChunk001Sub000Block009_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk001Sub000Block009Head + surrogateDiagTailX0RatChunk001Sub000Block009Mid + surrogateDiagTailX0RatChunk001Sub000Block009Tail =
      surrogateDiagTailX0RatChunk001Sub000Block009 := by
  unfold surrogateDiagTailX0RatChunk001Sub000Block009Head surrogateDiagTailX0RatChunk001Sub000Block009Mid surrogateDiagTailX0RatChunk001Sub000Block009Tail surrogateDiagTailX0RatChunk001Sub000Block009
  ring

def SurrogateDiagonalTailChunk001Sub000Block009HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block009HeadSum X0 = surrogateDiagTailX0RatChunk001Sub000Block009Head

def SurrogateDiagonalTailChunk001Sub000Block009MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block009MidSum X0 = surrogateDiagTailX0RatChunk001Sub000Block009Mid

def SurrogateDiagonalTailChunk001Sub000Block009TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block009TailSum X0 = surrogateDiagTailX0RatChunk001Sub000Block009Tail

theorem surrogateDiagonalTailChunk001Sub000Block009_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk001Sub000Block009HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk001Sub000Block009MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk001Sub000Block009TailCertificateAt X0) :
    surrogateDiagonalTailChunk001Sub000Block009Sum X0 = surrogateDiagTailX0RatChunk001Sub000Block009 := by
  unfold SurrogateDiagonalTailChunk001Sub000Block009HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk001Sub000Block009MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk001Sub000Block009TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk001Sub000Block009Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk001Sub000Block009_eq_head_add_mid_add_tail

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

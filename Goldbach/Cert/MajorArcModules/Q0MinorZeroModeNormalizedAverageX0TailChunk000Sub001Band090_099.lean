import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0TailPilot25

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

open scoped BigOperators

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

/- Generated direct-term certificate blocks for tail chunk 000, subchunk 001, blocks [90,100). -/

/-- Block 090 covers tail-support indices [7250,7275) and q from 11982 to 12021. -/

def TailChunk000Sub001Block090Part000SupportExplicit : Finset ℕ :=
  ([11982] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block090Part000 : ℚ :=
  (622914544175 : ℚ) / 317511159299073024

def SurrogateDiagonalTailChunk000Sub001Block090Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11982
    = surrogateDiagTailX0RatChunk000Sub001Block090Part000

theorem surrogateDiagonalTailChunk000Sub001Block090Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block090Part000CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block090Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block090Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block090Part000CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block090Part000SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block090Part000] using hcert

def TailChunk000Sub001Block090Part001SupportExplicit : Finset ℕ :=
  ([11983] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block090Part001 : ℚ :=
  (22239000081 : ℚ) / 114208831711969280

def SurrogateDiagonalTailChunk000Sub001Block090Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11983
    = surrogateDiagTailX0RatChunk000Sub001Block090Part001

theorem surrogateDiagonalTailChunk000Sub001Block090Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block090Part001CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block090Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block090Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block090Part001CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block090Part001SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block090Part001] using hcert

def TailChunk000Sub001Block090Part002SupportExplicit : Finset ℕ :=
  ([11985] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block090Part002 : ℚ :=
  (1305873805925 : ℚ) / 1502685405835689984

def SurrogateDiagonalTailChunk000Sub001Block090Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11985
    = surrogateDiagTailX0RatChunk000Sub001Block090Part002

theorem surrogateDiagonalTailChunk000Sub001Block090Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block090Part002CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block090Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block090Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block090Part002CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block090Part002SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block090Part002] using hcert

def TailChunk000Sub001Block090Part003SupportExplicit : Finset ℕ :=
  ([11986] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block090Part003 : ℚ :=
  (27210552263 : ℚ) / 30954365507174400

def SurrogateDiagonalTailChunk000Sub001Block090Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11986
    = surrogateDiagTailX0RatChunk000Sub001Block090Part003

theorem surrogateDiagonalTailChunk000Sub001Block090Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block090Part003CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block090Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block090Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block090Part003CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block090Part003SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block090Part003] using hcert

def TailChunk000Sub001Block090Part004SupportExplicit : Finset ℕ :=
  ([11987] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block090Part004 : ℚ :=
  (2245127640625 : ℚ) / 12902205682855550802

def SurrogateDiagonalTailChunk000Sub001Block090Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11987
    = surrogateDiagTailX0RatChunk000Sub001Block090Part004

theorem surrogateDiagonalTailChunk000Sub001Block090Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block090Part004CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block090Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block090Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block090Part004CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block090Part004SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block090Part004] using hcert

def TailChunk000Sub001Block090Part005SupportExplicit : Finset ℕ :=
  ([11989] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block090Part005 : ℚ :=
  (579718541 : ℚ) / 2917131517641600

def SurrogateDiagonalTailChunk000Sub001Block090Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11989
    = surrogateDiagTailX0RatChunk000Sub001Block090Part005

theorem surrogateDiagonalTailChunk000Sub001Block090Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block090Part005CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block090Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block090Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block090Part005CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block090Part005SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block090Part005] using hcert

def TailChunk000Sub001Block090Part006SupportExplicit : Finset ℕ :=
  ([11990] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block090Part006 : ℚ :=
  (60634518979 : ℚ) / 34835483079475200

def SurrogateDiagonalTailChunk000Sub001Block090Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11990
    = surrogateDiagTailX0RatChunk000Sub001Block090Part006

theorem surrogateDiagonalTailChunk000Sub001Block090Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block090Part006CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block090Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block090Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block090Part006CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block090Part006SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block090Part006] using hcert

def TailChunk000Sub001Block090Part007SupportExplicit : Finset ℕ :=
  ([11991] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block090Part007 : ℚ :=
  (64239402497 : ℚ) / 109466507291673600

def SurrogateDiagonalTailChunk000Sub001Block090Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11991
    = surrogateDiagTailX0RatChunk000Sub001Block090Part007

theorem surrogateDiagonalTailChunk000Sub001Block090Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block090Part007CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block090Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block090Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block090Part007CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block090Part007SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block090Part007] using hcert

def TailChunk000Sub001Block090Part008SupportExplicit : Finset ℕ :=
  ([11993] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block090Part008 : ℚ :=
  (87889125425 : ℚ) / 481113358591992192

def SurrogateDiagonalTailChunk000Sub001Block090Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11993
    = surrogateDiagTailX0RatChunk000Sub001Block090Part008

theorem surrogateDiagonalTailChunk000Sub001Block090Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block090Part008CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block090Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block090Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block090Part008CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block090Part008SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block090Part008] using hcert

def TailChunk000Sub001Block090Part009SupportExplicit : Finset ℕ :=
  ([11994] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block090Part009 : ℚ :=
  (312081434425 : ℚ) / 159392831552032032

def SurrogateDiagonalTailChunk000Sub001Block090Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11994
    = surrogateDiagTailX0RatChunk000Sub001Block090Part009

theorem surrogateDiagonalTailChunk000Sub001Block090Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block090Part009CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block090Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block090Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block090Part009CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block090Part009SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block090Part009] using hcert

def TailChunk000Sub001Block090Part010SupportExplicit : Finset ℕ :=
  ([11995] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block090Part010 : ℚ :=
  (6111629657725 : ℚ) / 21167206139167131648

def SurrogateDiagonalTailChunk000Sub001Block090Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11995
    = surrogateDiagTailX0RatChunk000Sub001Block090Part010

theorem surrogateDiagonalTailChunk000Sub001Block090Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block090Part010CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block090Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block090Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block090Part010CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block090Part010SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block090Part010] using hcert

def TailChunk000Sub001Block090Part011SupportExplicit : Finset ℕ :=
  ([11998] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block090Part011 : ℚ :=
  (1879874531575 : ℚ) / 1739910540580651008

def SurrogateDiagonalTailChunk000Sub001Block090Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11998
    = surrogateDiagTailX0RatChunk000Sub001Block090Part011

theorem surrogateDiagonalTailChunk000Sub001Block090Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block090Part011CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block090Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block090Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block090Part011CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block090Part011SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block090Part011] using hcert

def TailChunk000Sub001Block090Part012SupportExplicit : Finset ℕ :=
  ([12001] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block090Part012 : ℚ :=
  (306092688277 : ℚ) / 1411863926322000000

def SurrogateDiagonalTailChunk000Sub001Block090Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12001
    = surrogateDiagTailX0RatChunk000Sub001Block090Part012

theorem surrogateDiagonalTailChunk000Sub001Block090Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block090Part012CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block090Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block090Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block090Part012CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block090Part012SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block090Part012] using hcert

def TailChunk000Sub001Block090Part013SupportExplicit : Finset ℕ :=
  ([12002] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block090Part013 : ℚ :=
  (696173633475 : ℚ) / 838602569386295296

def SurrogateDiagonalTailChunk000Sub001Block090Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12002
    = surrogateDiagTailX0RatChunk000Sub001Block090Part013

theorem surrogateDiagonalTailChunk000Sub001Block090Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block090Part013CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block090Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block090Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block090Part013CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block090Part013SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block090Part013] using hcert

def TailChunk000Sub001Block090Part014SupportExplicit : Finset ℕ :=
  ([12003] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block090Part014 : ℚ :=
  (100028496749 : ℚ) / 204840960000000000

def SurrogateDiagonalTailChunk000Sub001Block090Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12003
    = surrogateDiagTailX0RatChunk000Sub001Block090Part014

theorem surrogateDiagonalTailChunk000Sub001Block090Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block090Part014CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block090Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block090Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block090Part014CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block090Part014SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block090Part014] using hcert

def TailChunk000Sub001Block090Part015SupportExplicit : Finset ℕ :=
  ([12007] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block090Part015 : ℚ :=
  (2252625765625 : ℚ) / 12988536634370106162

def SurrogateDiagonalTailChunk000Sub001Block090Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12007
    = surrogateDiagTailX0RatChunk000Sub001Block090Part015

theorem surrogateDiagonalTailChunk000Sub001Block090Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block090Part015CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block090Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block090Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block090Part015CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block090Part015SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block090Part015] using hcert

def TailChunk000Sub001Block090Part016SupportExplicit : Finset ℕ :=
  ([12009] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block090Part016 : ℚ :=
  (312901680475 : ℚ) / 641409216512104008

def SurrogateDiagonalTailChunk000Sub001Block090Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12009
    = surrogateDiagTailX0RatChunk000Sub001Block090Part016

theorem surrogateDiagonalTailChunk000Sub001Block090Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block090Part016CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block090Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block090Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block090Part016CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block090Part016SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block090Part016] using hcert

def TailChunk000Sub001Block090Part017SupportExplicit : Finset ℕ :=
  ([12010] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block090Part017 : ℚ :=
  (11410494349 : ℚ) / 8849129472000000

def SurrogateDiagonalTailChunk000Sub001Block090Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12010
    = surrogateDiagTailX0RatChunk000Sub001Block090Part017

theorem surrogateDiagonalTailChunk000Sub001Block090Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block090Part017CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block090Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block090Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block090Part017CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block090Part017SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block090Part017] using hcert

def TailChunk000Sub001Block090Part018SupportExplicit : Finset ℕ :=
  ([12011] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block090Part018 : ℚ :=
  (3606603025 : ℚ) / 20809367489299602

def SurrogateDiagonalTailChunk000Sub001Block090Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12011
    = surrogateDiagTailX0RatChunk000Sub001Block090Part018

theorem surrogateDiagonalTailChunk000Sub001Block090Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block090Part018CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block090Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block090Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block090Part018CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block090Part018SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block090Part018] using hcert

def TailChunk000Sub001Block090Part019SupportExplicit : Finset ℕ :=
  ([12013] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block090Part019 : ℚ :=
  (345006992563 : ℚ) / 1861479343600435200

def SurrogateDiagonalTailChunk000Sub001Block090Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12013
    = surrogateDiagTailX0RatChunk000Sub001Block090Part019

theorem surrogateDiagonalTailChunk000Sub001Block090Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block090Part019CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block090Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block090Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block090Part019CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block090Part019SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block090Part019] using hcert

def TailChunk000Sub001Block090Part020SupportExplicit : Finset ℕ :=
  ([12014] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block090Part020 : ℚ :=
  (563813265625 : ℚ) / 813407512213458162

def SurrogateDiagonalTailChunk000Sub001Block090Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12014
    = surrogateDiagTailX0RatChunk000Sub001Block090Part020

theorem surrogateDiagonalTailChunk000Sub001Block090Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block090Part020CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block090Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block090Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block090Part020CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block090Part020SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block090Part020] using hcert

def TailChunk000Sub001Block090Part021SupportExplicit : Finset ℕ :=
  ([12017] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block090Part021 : ℚ :=
  (348834814399 : ℚ) / 1913005141099315200

def SurrogateDiagonalTailChunk000Sub001Block090Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12017
    = surrogateDiagTailX0RatChunk000Sub001Block090Part021

theorem surrogateDiagonalTailChunk000Sub001Block090Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block090Part021CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block090Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block090Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block090Part021CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block090Part021SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block090Part021] using hcert

def TailChunk000Sub001Block090Part022SupportExplicit : Finset ℕ :=
  ([12018] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block090Part022 : ℚ :=
  (62625 : ℚ) / 26762342464

def SurrogateDiagonalTailChunk000Sub001Block090Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12018
    = surrogateDiagTailX0RatChunk000Sub001Block090Part022

theorem surrogateDiagonalTailChunk000Sub001Block090Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block090Part022CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block090Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block090Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block090Part022CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block090Part022SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block090Part022] using hcert

def TailChunk000Sub001Block090Part023SupportExplicit : Finset ℕ :=
  ([12019] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block090Part023 : ℚ :=
  (5573899163 : ℚ) / 18878142873600000

def SurrogateDiagonalTailChunk000Sub001Block090Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12019
    = surrogateDiagTailX0RatChunk000Sub001Block090Part023

theorem surrogateDiagonalTailChunk000Sub001Block090Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block090Part023CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block090Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block090Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block090Part023CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block090Part023SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block090Part023] using hcert

def TailChunk000Sub001Block090Part024SupportExplicit : Finset ℕ :=
  ([12021] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block090Part024 : ℚ :=
  (1254109622275 : ℚ) / 2575909673491874592

def SurrogateDiagonalTailChunk000Sub001Block090Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12021
    = surrogateDiagTailX0RatChunk000Sub001Block090Part024

theorem surrogateDiagonalTailChunk000Sub001Block090Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block090Part024CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block090Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block090Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block090Part024CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block090Part024SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block090Part024] using hcert

def surrogateDiagonalTailChunk000Sub001Block090HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block090Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block090Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block090Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block090Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block090Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block090Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block090Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block090Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block090Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block090Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block090Head : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block090Part000
    + surrogateDiagTailX0RatChunk000Sub001Block090Part001
    + surrogateDiagTailX0RatChunk000Sub001Block090Part002
    + surrogateDiagTailX0RatChunk000Sub001Block090Part003
    + surrogateDiagTailX0RatChunk000Sub001Block090Part004
    + surrogateDiagTailX0RatChunk000Sub001Block090Part005
    + surrogateDiagTailX0RatChunk000Sub001Block090Part006
    + surrogateDiagTailX0RatChunk000Sub001Block090Part007
    + surrogateDiagTailX0RatChunk000Sub001Block090Part008
    + surrogateDiagTailX0RatChunk000Sub001Block090Part009

def surrogateDiagonalTailChunk000Sub001Block090MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block090Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block090Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block090Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block090Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block090Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block090Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block090Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block090Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block090Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block090Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block090Mid : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block090Part010
    + surrogateDiagTailX0RatChunk000Sub001Block090Part011
    + surrogateDiagTailX0RatChunk000Sub001Block090Part012
    + surrogateDiagTailX0RatChunk000Sub001Block090Part013
    + surrogateDiagTailX0RatChunk000Sub001Block090Part014
    + surrogateDiagTailX0RatChunk000Sub001Block090Part015
    + surrogateDiagTailX0RatChunk000Sub001Block090Part016
    + surrogateDiagTailX0RatChunk000Sub001Block090Part017
    + surrogateDiagTailX0RatChunk000Sub001Block090Part018
    + surrogateDiagTailX0RatChunk000Sub001Block090Part019

def surrogateDiagonalTailChunk000Sub001Block090TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block090Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block090Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block090Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block090Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block090Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block090Tail : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block090Part020
    + surrogateDiagTailX0RatChunk000Sub001Block090Part021
    + surrogateDiagTailX0RatChunk000Sub001Block090Part022
    + surrogateDiagTailX0RatChunk000Sub001Block090Part023
    + surrogateDiagTailX0RatChunk000Sub001Block090Part024

def surrogateDiagonalTailChunk000Sub001Block090Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub001Block090HeadSum X0
    + surrogateDiagonalTailChunk000Sub001Block090MidSum X0
    + surrogateDiagonalTailChunk000Sub001Block090TailSum X0

def surrogateDiagTailX0RatChunk000Sub001Block090 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block090Part000
    + surrogateDiagTailX0RatChunk000Sub001Block090Part001
    + surrogateDiagTailX0RatChunk000Sub001Block090Part002
    + surrogateDiagTailX0RatChunk000Sub001Block090Part003
    + surrogateDiagTailX0RatChunk000Sub001Block090Part004
    + surrogateDiagTailX0RatChunk000Sub001Block090Part005
    + surrogateDiagTailX0RatChunk000Sub001Block090Part006
    + surrogateDiagTailX0RatChunk000Sub001Block090Part007
    + surrogateDiagTailX0RatChunk000Sub001Block090Part008
    + surrogateDiagTailX0RatChunk000Sub001Block090Part009
    + surrogateDiagTailX0RatChunk000Sub001Block090Part010
    + surrogateDiagTailX0RatChunk000Sub001Block090Part011
    + surrogateDiagTailX0RatChunk000Sub001Block090Part012
    + surrogateDiagTailX0RatChunk000Sub001Block090Part013
    + surrogateDiagTailX0RatChunk000Sub001Block090Part014
    + surrogateDiagTailX0RatChunk000Sub001Block090Part015
    + surrogateDiagTailX0RatChunk000Sub001Block090Part016
    + surrogateDiagTailX0RatChunk000Sub001Block090Part017
    + surrogateDiagTailX0RatChunk000Sub001Block090Part018
    + surrogateDiagTailX0RatChunk000Sub001Block090Part019
    + surrogateDiagTailX0RatChunk000Sub001Block090Part020
    + surrogateDiagTailX0RatChunk000Sub001Block090Part021
    + surrogateDiagTailX0RatChunk000Sub001Block090Part022
    + surrogateDiagTailX0RatChunk000Sub001Block090Part023
    + surrogateDiagTailX0RatChunk000Sub001Block090Part024

theorem surrogateDiagTailX0RatChunk000Sub001Block090_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk000Sub001Block090Head + surrogateDiagTailX0RatChunk000Sub001Block090Mid + surrogateDiagTailX0RatChunk000Sub001Block090Tail =
      surrogateDiagTailX0RatChunk000Sub001Block090 := by
  unfold surrogateDiagTailX0RatChunk000Sub001Block090Head surrogateDiagTailX0RatChunk000Sub001Block090Mid surrogateDiagTailX0RatChunk000Sub001Block090Tail surrogateDiagTailX0RatChunk000Sub001Block090
  ring

def SurrogateDiagonalTailChunk000Sub001Block090HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block090HeadSum X0 = surrogateDiagTailX0RatChunk000Sub001Block090Head

def SurrogateDiagonalTailChunk000Sub001Block090MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block090MidSum X0 = surrogateDiagTailX0RatChunk000Sub001Block090Mid

def SurrogateDiagonalTailChunk000Sub001Block090TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block090TailSum X0 = surrogateDiagTailX0RatChunk000Sub001Block090Tail

theorem surrogateDiagonalTailChunk000Sub001Block090_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk000Sub001Block090HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk000Sub001Block090MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk000Sub001Block090TailCertificateAt X0) :
    surrogateDiagonalTailChunk000Sub001Block090Sum X0 = surrogateDiagTailX0RatChunk000Sub001Block090 := by
  unfold SurrogateDiagonalTailChunk000Sub001Block090HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk000Sub001Block090MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk000Sub001Block090TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk000Sub001Block090Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk000Sub001Block090_eq_head_add_mid_add_tail

/-- Block 091 covers tail-support indices [7275,7300) and q from 12022 to 12062. -/

def TailChunk000Sub001Block091Part000SupportExplicit : Finset ℕ :=
  ([12022] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block091Part000 : ℚ :=
  (903303025 : ℚ) / 1304922556334802

def SurrogateDiagonalTailChunk000Sub001Block091Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12022
    = surrogateDiagTailX0RatChunk000Sub001Block091Part000

theorem surrogateDiagonalTailChunk000Sub001Block091Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block091Part000CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block091Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block091Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block091Part000CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block091Part000SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block091Part000] using hcert

def TailChunk000Sub001Block091Part001SupportExplicit : Finset ℕ :=
  ([12023] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block091Part001 : ℚ :=
  (310206050641 : ℚ) / 1422254785374259200

def SurrogateDiagonalTailChunk000Sub001Block091Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12023
    = surrogateDiagTailX0RatChunk000Sub001Block091Part001

theorem surrogateDiagonalTailChunk000Sub001Block091Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block091Part001CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block091Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block091Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block091Part001CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block091Part001SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block091Part001] using hcert

def TailChunk000Sub001Block091Part002SupportExplicit : Finset ℕ :=
  ([12026] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block091Part002 : ℚ :=
  (231741494275 : ℚ) / 1756228464520852608

def SurrogateDiagonalTailChunk000Sub001Block091Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12026
    = surrogateDiagTailX0RatChunk000Sub001Block091Part002

theorem surrogateDiagonalTailChunk000Sub001Block091Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block091Part002CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block091Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block091Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block091Part002CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block091Part002SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block091Part002] using hcert

def TailChunk000Sub001Block091Part003SupportExplicit : Finset ℕ :=
  ([12027] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block091Part003 : ℚ :=
  (10338134521 : ℚ) / 81679682493964800

def SurrogateDiagonalTailChunk000Sub001Block091Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12027
    = surrogateDiagTailX0RatChunk000Sub001Block091Part003

theorem surrogateDiagonalTailChunk000Sub001Block091Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block091Part003CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block091Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block091Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block091Part003CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block091Part003SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block091Part003] using hcert

def TailChunk000Sub001Block091Part004SupportExplicit : Finset ℕ :=
  ([12029] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block091Part004 : ℚ :=
  (5513489375 : ℚ) / 1499690347718884992

def SurrogateDiagonalTailChunk000Sub001Block091Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12029
    = surrogateDiagTailX0RatChunk000Sub001Block091Part004

theorem surrogateDiagonalTailChunk000Sub001Block091Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block091Part004CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block091Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block091Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block091Part004CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block091Part004SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block091Part004] using hcert

def TailChunk000Sub001Block091Part005SupportExplicit : Finset ℕ :=
  ([12030] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block091Part005 : ℚ :=
  (22097811073 : ℚ) / 10487857152000000

def SurrogateDiagonalTailChunk000Sub001Block091Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12030
    = surrogateDiagTailX0RatChunk000Sub001Block091Part005

theorem surrogateDiagonalTailChunk000Sub001Block091Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block091Part005CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block091Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block091Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block091Part005CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block091Part005SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block091Part005] using hcert

def TailChunk000Sub001Block091Part006SupportExplicit : Finset ℕ :=
  ([12031] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block091Part006 : ℚ :=
  (14381843025 : ℚ) / 7949187475893767168

def SurrogateDiagonalTailChunk000Sub001Block091Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12031
    = surrogateDiagTailX0RatChunk000Sub001Block091Part006

theorem surrogateDiagonalTailChunk000Sub001Block091Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block091Part006CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block091Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block091Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block091Part006CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block091Part006SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block091Part006] using hcert

def TailChunk000Sub001Block091Part007SupportExplicit : Finset ℕ :=
  ([12034] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block091Part007 : ℚ :=
  (32797747 : ℚ) / 427360211951400

def SurrogateDiagonalTailChunk000Sub001Block091Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12034
    = surrogateDiagTailX0RatChunk000Sub001Block091Part007

theorem surrogateDiagonalTailChunk000Sub001Block091Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block091Part007CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block091Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block091Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block091Part007CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block091Part007SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block091Part007] using hcert

def TailChunk000Sub001Block091Part008SupportExplicit : Finset ℕ :=
  ([12035] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block091Part008 : ℚ :=
  (33056726175 : ℚ) / 741213153026834432

def SurrogateDiagonalTailChunk000Sub001Block091Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12035
    = surrogateDiagTailX0RatChunk000Sub001Block091Part008

theorem surrogateDiagonalTailChunk000Sub001Block091Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block091Part008CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block091Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block091Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block091Part008CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block091Part008SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block091Part008] using hcert

def TailChunk000Sub001Block091Part009SupportExplicit : Finset ℕ :=
  ([12037] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block091Part009 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block091Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12037
    = surrogateDiagTailX0RatChunk000Sub001Block091Part009

theorem surrogateDiagonalTailChunk000Sub001Block091Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block091Part009CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block091Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block091Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block091Part009CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block091Part009SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block091Part009] using hcert

def TailChunk000Sub001Block091Part010SupportExplicit : Finset ℕ :=
  ([12038] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block091Part010 : ℚ :=
  (63215875 : ℚ) / 994198970274048

def SurrogateDiagonalTailChunk000Sub001Block091Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12038
    = surrogateDiagTailX0RatChunk000Sub001Block091Part010

theorem surrogateDiagonalTailChunk000Sub001Block091Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block091Part010CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block091Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block091Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block091Part010CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block091Part010SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block091Part010] using hcert

def TailChunk000Sub001Block091Part011SupportExplicit : Finset ℕ :=
  ([12039] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block091Part011 : ℚ :=
  (31457315225 : ℚ) / 323922086048837184

def SurrogateDiagonalTailChunk000Sub001Block091Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12039
    = surrogateDiagTailX0RatChunk000Sub001Block091Part011

theorem surrogateDiagonalTailChunk000Sub001Block091Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block091Part011CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block091Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block091Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block091Part011CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block091Part011SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block091Part011] using hcert

def TailChunk000Sub001Block091Part012SupportExplicit : Finset ℕ :=
  ([12041] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block091Part012 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block091Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12041
    = surrogateDiagTailX0RatChunk000Sub001Block091Part012

theorem surrogateDiagonalTailChunk000Sub001Block091Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block091Part012CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block091Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block091Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block091Part012CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block091Part012SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block091Part012] using hcert

def TailChunk000Sub001Block091Part013SupportExplicit : Finset ℕ :=
  ([12043] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block091Part013 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block091Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12043
    = surrogateDiagTailX0RatChunk000Sub001Block091Part013

theorem surrogateDiagonalTailChunk000Sub001Block091Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block091Part013CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block091Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block091Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block091Part013CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block091Part013SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block091Part013] using hcert

def TailChunk000Sub001Block091Part014SupportExplicit : Finset ℕ :=
  ([12045] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block091Part014 : ℚ :=
  (14334755227 : ℚ) / 36699109746278400

def SurrogateDiagonalTailChunk000Sub001Block091Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12045
    = surrogateDiagTailX0RatChunk000Sub001Block091Part014

theorem surrogateDiagonalTailChunk000Sub001Block091Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block091Part014CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block091Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block091Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block091Part014CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block091Part014SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block091Part014] using hcert

def TailChunk000Sub001Block091Part015SupportExplicit : Finset ℕ :=
  ([12046] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block091Part015 : ℚ :=
  (105176912575 : ℚ) / 2617370539389831168

def SurrogateDiagonalTailChunk000Sub001Block091Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12046
    = surrogateDiagTailX0RatChunk000Sub001Block091Part015

theorem surrogateDiagonalTailChunk000Sub001Block091Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block091Part015CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block091Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block091Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block091Part015CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block091Part015SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block091Part015] using hcert

def TailChunk000Sub001Block091Part016SupportExplicit : Finset ℕ :=
  ([12047] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block091Part016 : ℚ :=
  (1236339433 : ℚ) / 63027943100006400

def SurrogateDiagonalTailChunk000Sub001Block091Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12047
    = surrogateDiagTailX0RatChunk000Sub001Block091Part016

theorem surrogateDiagonalTailChunk000Sub001Block091Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block091Part016CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block091Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block091Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block091Part016CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block091Part016SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block091Part016] using hcert

def TailChunk000Sub001Block091Part017SupportExplicit : Finset ℕ :=
  ([12049] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block091Part017 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block091Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12049
    = surrogateDiagTailX0RatChunk000Sub001Block091Part017

theorem surrogateDiagonalTailChunk000Sub001Block091Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block091Part017CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block091Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block091Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block091Part017CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block091Part017SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block091Part017] using hcert

def TailChunk000Sub001Block091Part018SupportExplicit : Finset ℕ :=
  ([12053] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block091Part018 : ℚ :=
  (112019045075 : ℚ) / 20587794498808971264

def SurrogateDiagonalTailChunk000Sub001Block091Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12053
    = surrogateDiagTailX0RatChunk000Sub001Block091Part018

theorem surrogateDiagonalTailChunk000Sub001Block091Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block091Part018CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block091Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block091Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block091Part018CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block091Part018SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block091Part018] using hcert

def TailChunk000Sub001Block091Part019SupportExplicit : Finset ℕ :=
  ([12055] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block091Part019 : ℚ :=
  (29084707969 : ℚ) / 863763773827123200

def SurrogateDiagonalTailChunk000Sub001Block091Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12055
    = surrogateDiagTailX0RatChunk000Sub001Block091Part019

theorem surrogateDiagonalTailChunk000Sub001Block091Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block091Part019CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block091Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block091Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block091Part019CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block091Part019SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block091Part019] using hcert

def TailChunk000Sub001Block091Part020SupportExplicit : Finset ℕ :=
  ([12057] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block091Part020 : ℚ :=
  (72117524075 : ℚ) / 744832357875598272

def SurrogateDiagonalTailChunk000Sub001Block091Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12057
    = surrogateDiagTailX0RatChunk000Sub001Block091Part020

theorem surrogateDiagonalTailChunk000Sub001Block091Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block091Part020CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block091Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block091Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block091Part020CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block091Part020SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block091Part020] using hcert

def TailChunk000Sub001Block091Part021SupportExplicit : Finset ℕ :=
  ([12058] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block091Part021 : ℚ :=
  (567950640625 : ℚ) / 825391214898092832

def SurrogateDiagonalTailChunk000Sub001Block091Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12058
    = surrogateDiagTailX0RatChunk000Sub001Block091Part021

theorem surrogateDiagonalTailChunk000Sub001Block091Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block091Part021CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block091Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block091Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block091Part021CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block091Part021SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block091Part021] using hcert

def TailChunk000Sub001Block091Part022SupportExplicit : Finset ℕ :=
  ([12059] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block091Part022 : ℚ :=
  (1051062959 : ℚ) / 367222063890032640

def SurrogateDiagonalTailChunk000Sub001Block091Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12059
    = surrogateDiagTailX0RatChunk000Sub001Block091Part022

theorem surrogateDiagonalTailChunk000Sub001Block091Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block091Part022CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block091Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block091Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block091Part022CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block091Part022SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block091Part022] using hcert

def TailChunk000Sub001Block091Part023SupportExplicit : Finset ℕ :=
  ([12061] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block091Part023 : ℚ :=
  (210749425 : ℚ) / 10768980958158528

def SurrogateDiagonalTailChunk000Sub001Block091Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12061
    = surrogateDiagTailX0RatChunk000Sub001Block091Part023

theorem surrogateDiagonalTailChunk000Sub001Block091Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block091Part023CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block091Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block091Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block091Part023CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block091Part023SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block091Part023] using hcert

def TailChunk000Sub001Block091Part024SupportExplicit : Finset ℕ :=
  ([12062] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block091Part024 : ℚ :=
  (121475159575 : ℚ) / 160703159403119616

def SurrogateDiagonalTailChunk000Sub001Block091Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12062
    = surrogateDiagTailX0RatChunk000Sub001Block091Part024

theorem surrogateDiagonalTailChunk000Sub001Block091Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block091Part024CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block091Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block091Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block091Part024CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block091Part024SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block091Part024] using hcert

def surrogateDiagonalTailChunk000Sub001Block091HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block091Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block091Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block091Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block091Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block091Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block091Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block091Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block091Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block091Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block091Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block091Head : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block091Part000
    + surrogateDiagTailX0RatChunk000Sub001Block091Part001
    + surrogateDiagTailX0RatChunk000Sub001Block091Part002
    + surrogateDiagTailX0RatChunk000Sub001Block091Part003
    + surrogateDiagTailX0RatChunk000Sub001Block091Part004
    + surrogateDiagTailX0RatChunk000Sub001Block091Part005
    + surrogateDiagTailX0RatChunk000Sub001Block091Part006
    + surrogateDiagTailX0RatChunk000Sub001Block091Part007
    + surrogateDiagTailX0RatChunk000Sub001Block091Part008
    + surrogateDiagTailX0RatChunk000Sub001Block091Part009

def surrogateDiagonalTailChunk000Sub001Block091MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block091Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block091Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block091Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block091Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block091Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block091Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block091Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block091Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block091Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block091Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block091Mid : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block091Part010
    + surrogateDiagTailX0RatChunk000Sub001Block091Part011
    + surrogateDiagTailX0RatChunk000Sub001Block091Part012
    + surrogateDiagTailX0RatChunk000Sub001Block091Part013
    + surrogateDiagTailX0RatChunk000Sub001Block091Part014
    + surrogateDiagTailX0RatChunk000Sub001Block091Part015
    + surrogateDiagTailX0RatChunk000Sub001Block091Part016
    + surrogateDiagTailX0RatChunk000Sub001Block091Part017
    + surrogateDiagTailX0RatChunk000Sub001Block091Part018
    + surrogateDiagTailX0RatChunk000Sub001Block091Part019

def surrogateDiagonalTailChunk000Sub001Block091TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block091Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block091Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block091Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block091Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block091Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block091Tail : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block091Part020
    + surrogateDiagTailX0RatChunk000Sub001Block091Part021
    + surrogateDiagTailX0RatChunk000Sub001Block091Part022
    + surrogateDiagTailX0RatChunk000Sub001Block091Part023
    + surrogateDiagTailX0RatChunk000Sub001Block091Part024

def surrogateDiagonalTailChunk000Sub001Block091Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub001Block091HeadSum X0
    + surrogateDiagonalTailChunk000Sub001Block091MidSum X0
    + surrogateDiagonalTailChunk000Sub001Block091TailSum X0

def surrogateDiagTailX0RatChunk000Sub001Block091 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block091Part000
    + surrogateDiagTailX0RatChunk000Sub001Block091Part001
    + surrogateDiagTailX0RatChunk000Sub001Block091Part002
    + surrogateDiagTailX0RatChunk000Sub001Block091Part003
    + surrogateDiagTailX0RatChunk000Sub001Block091Part004
    + surrogateDiagTailX0RatChunk000Sub001Block091Part005
    + surrogateDiagTailX0RatChunk000Sub001Block091Part006
    + surrogateDiagTailX0RatChunk000Sub001Block091Part007
    + surrogateDiagTailX0RatChunk000Sub001Block091Part008
    + surrogateDiagTailX0RatChunk000Sub001Block091Part009
    + surrogateDiagTailX0RatChunk000Sub001Block091Part010
    + surrogateDiagTailX0RatChunk000Sub001Block091Part011
    + surrogateDiagTailX0RatChunk000Sub001Block091Part012
    + surrogateDiagTailX0RatChunk000Sub001Block091Part013
    + surrogateDiagTailX0RatChunk000Sub001Block091Part014
    + surrogateDiagTailX0RatChunk000Sub001Block091Part015
    + surrogateDiagTailX0RatChunk000Sub001Block091Part016
    + surrogateDiagTailX0RatChunk000Sub001Block091Part017
    + surrogateDiagTailX0RatChunk000Sub001Block091Part018
    + surrogateDiagTailX0RatChunk000Sub001Block091Part019
    + surrogateDiagTailX0RatChunk000Sub001Block091Part020
    + surrogateDiagTailX0RatChunk000Sub001Block091Part021
    + surrogateDiagTailX0RatChunk000Sub001Block091Part022
    + surrogateDiagTailX0RatChunk000Sub001Block091Part023
    + surrogateDiagTailX0RatChunk000Sub001Block091Part024

theorem surrogateDiagTailX0RatChunk000Sub001Block091_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk000Sub001Block091Head + surrogateDiagTailX0RatChunk000Sub001Block091Mid + surrogateDiagTailX0RatChunk000Sub001Block091Tail =
      surrogateDiagTailX0RatChunk000Sub001Block091 := by
  unfold surrogateDiagTailX0RatChunk000Sub001Block091Head surrogateDiagTailX0RatChunk000Sub001Block091Mid surrogateDiagTailX0RatChunk000Sub001Block091Tail surrogateDiagTailX0RatChunk000Sub001Block091
  ring

def SurrogateDiagonalTailChunk000Sub001Block091HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block091HeadSum X0 = surrogateDiagTailX0RatChunk000Sub001Block091Head

def SurrogateDiagonalTailChunk000Sub001Block091MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block091MidSum X0 = surrogateDiagTailX0RatChunk000Sub001Block091Mid

def SurrogateDiagonalTailChunk000Sub001Block091TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block091TailSum X0 = surrogateDiagTailX0RatChunk000Sub001Block091Tail

theorem surrogateDiagonalTailChunk000Sub001Block091_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk000Sub001Block091HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk000Sub001Block091MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk000Sub001Block091TailCertificateAt X0) :
    surrogateDiagonalTailChunk000Sub001Block091Sum X0 = surrogateDiagTailX0RatChunk000Sub001Block091 := by
  unfold SurrogateDiagonalTailChunk000Sub001Block091HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk000Sub001Block091MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk000Sub001Block091TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk000Sub001Block091Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk000Sub001Block091_eq_head_add_mid_add_tail

/-- Block 092 covers tail-support indices [7300,7325) and q from 12063 to 12101. -/

def TailChunk000Sub001Block092Part000SupportExplicit : Finset ℕ :=
  ([12063] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block092Part000 : ℚ :=
  (1010650087 : ℚ) / 10448430394625280

def SurrogateDiagonalTailChunk000Sub001Block092Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12063
    = surrogateDiagTailX0RatChunk000Sub001Block092Part000

theorem surrogateDiagonalTailChunk000Sub001Block092Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block092Part000CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block092Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block092Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block092Part000CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block092Part000SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block092Part000] using hcert

def TailChunk000Sub001Block092Part001SupportExplicit : Finset ℕ :=
  ([12065] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block092Part001 : ℚ :=
  (205220639425 : ℚ) / 4234274740487135232

def SurrogateDiagonalTailChunk000Sub001Block092Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12065
    = surrogateDiagTailX0RatChunk000Sub001Block092Part001

theorem surrogateDiagonalTailChunk000Sub001Block092Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block092Part001CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block092Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block092Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block092Part001CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block092Part001SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block092Part001] using hcert

def TailChunk000Sub001Block092Part002SupportExplicit : Finset ℕ :=
  ([12066] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block092Part002 : ℚ :=
  (2020883 : ℚ) / 870528427200

def SurrogateDiagonalTailChunk000Sub001Block092Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12066
    = surrogateDiagTailX0RatChunk000Sub001Block092Part002

theorem surrogateDiagonalTailChunk000Sub001Block092Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block092Part002CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block092Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block092Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block092Part002CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block092Part002SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block092Part002] using hcert

def TailChunk000Sub001Block092Part003SupportExplicit : Finset ℕ :=
  ([12067] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block092Part003 : ℚ :=
  (37820665 : ℚ) / 3608021156579328

def SurrogateDiagonalTailChunk000Sub001Block092Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12067
    = surrogateDiagTailX0RatChunk000Sub001Block092Part003

theorem surrogateDiagonalTailChunk000Sub001Block092Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block092Part003CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block092Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block092Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block092Part003CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block092Part003SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block092Part003] using hcert

def TailChunk000Sub001Block092Part004SupportExplicit : Finset ℕ :=
  ([12070] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block092Part004 : ℚ :=
  (13246269 : ℚ) / 8393781673984

def SurrogateDiagonalTailChunk000Sub001Block092Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12070
    = surrogateDiagTailX0RatChunk000Sub001Block092Part004

theorem surrogateDiagonalTailChunk000Sub001Block092Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block092Part004CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block092Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block092Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block092Part004CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block092Part004SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block092Part004] using hcert

def TailChunk000Sub001Block092Part005SupportExplicit : Finset ℕ :=
  ([12071] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block092Part005 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block092Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12071
    = surrogateDiagTailX0RatChunk000Sub001Block092Part005

theorem surrogateDiagonalTailChunk000Sub001Block092Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block092Part005CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block092Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block092Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block092Part005CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block092Part005SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block092Part005] using hcert

def TailChunk000Sub001Block092Part006SupportExplicit : Finset ℕ :=
  ([12073] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block092Part006 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block092Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12073
    = surrogateDiagTailX0RatChunk000Sub001Block092Part006

theorem surrogateDiagonalTailChunk000Sub001Block092Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block092Part006CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block092Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block092Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block092Part006CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block092Part006SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block092Part006] using hcert

def TailChunk000Sub001Block092Part007SupportExplicit : Finset ℕ :=
  ([12074] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block092Part007 : ℚ :=
  (569458890625 : ℚ) / 829781584021937952

def SurrogateDiagonalTailChunk000Sub001Block092Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12074
    = surrogateDiagTailX0RatChunk000Sub001Block092Part007

theorem surrogateDiagonalTailChunk000Sub001Block092Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block092Part007CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block092Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block092Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block092Part007CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block092Part007SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block092Part007] using hcert

def TailChunk000Sub001Block092Part008SupportExplicit : Finset ℕ :=
  ([12077] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block092Part008 : ℚ :=
  (272657597125 : ℚ) / 38454197096974123008

def SurrogateDiagonalTailChunk000Sub001Block092Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12077
    = surrogateDiagTailX0RatChunk000Sub001Block092Part008

theorem surrogateDiagonalTailChunk000Sub001Block092Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block092Part008CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block092Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block092Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block092Part008CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block092Part008SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block092Part008] using hcert

def TailChunk000Sub001Block092Part009SupportExplicit : Finset ℕ :=
  ([12079] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block092Part009 : ℚ :=
  (45934974125 : ℚ) / 24042966493371039744

def SurrogateDiagonalTailChunk000Sub001Block092Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12079
    = surrogateDiagTailX0RatChunk000Sub001Block092Part009

theorem surrogateDiagonalTailChunk000Sub001Block092Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block092Part009CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block092Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block092Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block092Part009CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block092Part009SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block092Part009] using hcert

def TailChunk000Sub001Block092Part010SupportExplicit : Finset ℕ :=
  ([12081] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block092Part010 : ℚ :=
  (506833668425 : ℚ) / 5255474438170211904

def SurrogateDiagonalTailChunk000Sub001Block092Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12081
    = surrogateDiagTailX0RatChunk000Sub001Block092Part010

theorem surrogateDiagonalTailChunk000Sub001Block092Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block092Part010CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block092Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block092Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block092Part010CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block092Part010SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block092Part010] using hcert

def TailChunk000Sub001Block092Part011SupportExplicit : Finset ℕ :=
  ([12082] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block092Part011 : ℚ :=
  (1906293934975 : ℚ) / 1789208380554726528

def SurrogateDiagonalTailChunk000Sub001Block092Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12082
    = surrogateDiagTailX0RatChunk000Sub001Block092Part011

theorem surrogateDiagonalTailChunk000Sub001Block092Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block092Part011CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block092Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block092Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block092Part011CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block092Part011SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block092Part011] using hcert

def TailChunk000Sub001Block092Part012SupportExplicit : Finset ℕ :=
  ([12083] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block092Part012 : ℚ :=
  (3328397 : ℚ) / 1574489828065280

def SurrogateDiagonalTailChunk000Sub001Block092Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12083
    = surrogateDiagTailX0RatChunk000Sub001Block092Part012

theorem surrogateDiagonalTailChunk000Sub001Block092Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block092Part012CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block092Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block092Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block092Part012CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block092Part012SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block092Part012] using hcert

def TailChunk000Sub001Block092Part013SupportExplicit : Finset ℕ :=
  ([12085] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block092Part013 : ℚ :=
  (730736473525 : ℚ) / 21809943674678673408

def SurrogateDiagonalTailChunk000Sub001Block092Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12085
    = surrogateDiagTailX0RatChunk000Sub001Block092Part013

theorem surrogateDiagonalTailChunk000Sub001Block092Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block092Part013CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block092Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block092Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block092Part013CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block092Part013SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block092Part013] using hcert

def TailChunk000Sub001Block092Part014SupportExplicit : Finset ℕ :=
  ([12086] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block092Part014 : ℚ :=
  (570591390625 : ℚ) / 833085837115462962

def SurrogateDiagonalTailChunk000Sub001Block092Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12086
    = surrogateDiagTailX0RatChunk000Sub001Block092Part014

theorem surrogateDiagonalTailChunk000Sub001Block092Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block092Part014CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block092Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block092Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block092Part014CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block092Part014SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block092Part014] using hcert

def TailChunk000Sub001Block092Part015SupportExplicit : Finset ℕ :=
  ([12089] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block092Part015 : ℚ :=
  (1744613641 : ℚ) / 42649872780902400

def SurrogateDiagonalTailChunk000Sub001Block092Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12089
    = surrogateDiagTailX0RatChunk000Sub001Block092Part015

theorem surrogateDiagonalTailChunk000Sub001Block092Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block092Part015CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block092Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block092Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block092Part015CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block092Part015SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block092Part015] using hcert

def TailChunk000Sub001Block092Part016SupportExplicit : Finset ℕ :=
  ([12090] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block092Part016 : ℚ :=
  (302368579 : ℚ) / 57342358978560

def SurrogateDiagonalTailChunk000Sub001Block092Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12090
    = surrogateDiagTailX0RatChunk000Sub001Block092Part016

theorem surrogateDiagonalTailChunk000Sub001Block092Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block092Part016CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block092Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block092Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block092Part016CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block092Part016SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block092Part016] using hcert

def TailChunk000Sub001Block092Part017SupportExplicit : Finset ℕ :=
  ([12091] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block092Part017 : ℚ :=
  (4267468525 : ℚ) / 3104576944533700608

def SurrogateDiagonalTailChunk000Sub001Block092Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12091
    = surrogateDiagTailX0RatChunk000Sub001Block092Part017

theorem surrogateDiagonalTailChunk000Sub001Block092Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block092Part017CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block092Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block092Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block092Part017CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block092Part017SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block092Part017] using hcert

def TailChunk000Sub001Block092Part018SupportExplicit : Finset ℕ :=
  ([12093] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block092Part018 : ℚ :=
  (57501544675 : ℚ) / 495476210551504896

def SurrogateDiagonalTailChunk000Sub001Block092Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12093
    = surrogateDiagTailX0RatChunk000Sub001Block092Part018

theorem surrogateDiagonalTailChunk000Sub001Block092Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block092Part018CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block092Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block092Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block092Part018CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block092Part018SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block092Part018] using hcert

def TailChunk000Sub001Block092Part019SupportExplicit : Finset ℕ :=
  ([12094] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block092Part019 : ℚ :=
  (571347015625 : ℚ) / 835294148262977682

def SurrogateDiagonalTailChunk000Sub001Block092Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12094
    = surrogateDiagTailX0RatChunk000Sub001Block092Part019

theorem surrogateDiagonalTailChunk000Sub001Block092Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block092Part019CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block092Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block092Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block092Part019CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block092Part019SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block092Part019] using hcert

def TailChunk000Sub001Block092Part020SupportExplicit : Finset ℕ :=
  ([12095] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block092Part020 : ℚ :=
  (5286270627 : ℚ) / 123631034905395200

def SurrogateDiagonalTailChunk000Sub001Block092Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12095
    = surrogateDiagTailX0RatChunk000Sub001Block092Part020

theorem surrogateDiagonalTailChunk000Sub001Block092Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block092Part020CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block092Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block092Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block092Part020CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block092Part020SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block092Part020] using hcert

def TailChunk000Sub001Block092Part021SupportExplicit : Finset ℕ :=
  ([12097] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block092Part021 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block092Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12097
    = surrogateDiagTailX0RatChunk000Sub001Block092Part021

theorem surrogateDiagonalTailChunk000Sub001Block092Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block092Part021CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block092Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block092Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block092Part021CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block092Part021SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block092Part021] using hcert

def TailChunk000Sub001Block092Part022SupportExplicit : Finset ℕ :=
  ([12098] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block092Part022 : ℚ :=
  (720318461475 : ℚ) / 920028948912996736

def SurrogateDiagonalTailChunk000Sub001Block092Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12098
    = surrogateDiagTailX0RatChunk000Sub001Block092Part022

theorem surrogateDiagonalTailChunk000Sub001Block092Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block092Part022CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block092Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block092Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block092Part022CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block092Part022SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block092Part022] using hcert

def TailChunk000Sub001Block092Part023SupportExplicit : Finset ℕ :=
  ([12099] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block092Part023 : ℚ :=
  (1976363616325 : ℚ) / 9142224179377471488

def SurrogateDiagonalTailChunk000Sub001Block092Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12099
    = surrogateDiagTailX0RatChunk000Sub001Block092Part023

theorem surrogateDiagonalTailChunk000Sub001Block092Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block092Part023CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block092Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block092Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block092Part023CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block092Part023SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block092Part023] using hcert

def TailChunk000Sub001Block092Part024SupportExplicit : Finset ℕ :=
  ([12101] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block092Part024 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block092Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12101
    = surrogateDiagTailX0RatChunk000Sub001Block092Part024

theorem surrogateDiagonalTailChunk000Sub001Block092Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block092Part024CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block092Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block092Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block092Part024CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block092Part024SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block092Part024] using hcert

def surrogateDiagonalTailChunk000Sub001Block092HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block092Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block092Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block092Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block092Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block092Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block092Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block092Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block092Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block092Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block092Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block092Head : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block092Part000
    + surrogateDiagTailX0RatChunk000Sub001Block092Part001
    + surrogateDiagTailX0RatChunk000Sub001Block092Part002
    + surrogateDiagTailX0RatChunk000Sub001Block092Part003
    + surrogateDiagTailX0RatChunk000Sub001Block092Part004
    + surrogateDiagTailX0RatChunk000Sub001Block092Part005
    + surrogateDiagTailX0RatChunk000Sub001Block092Part006
    + surrogateDiagTailX0RatChunk000Sub001Block092Part007
    + surrogateDiagTailX0RatChunk000Sub001Block092Part008
    + surrogateDiagTailX0RatChunk000Sub001Block092Part009

def surrogateDiagonalTailChunk000Sub001Block092MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block092Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block092Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block092Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block092Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block092Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block092Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block092Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block092Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block092Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block092Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block092Mid : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block092Part010
    + surrogateDiagTailX0RatChunk000Sub001Block092Part011
    + surrogateDiagTailX0RatChunk000Sub001Block092Part012
    + surrogateDiagTailX0RatChunk000Sub001Block092Part013
    + surrogateDiagTailX0RatChunk000Sub001Block092Part014
    + surrogateDiagTailX0RatChunk000Sub001Block092Part015
    + surrogateDiagTailX0RatChunk000Sub001Block092Part016
    + surrogateDiagTailX0RatChunk000Sub001Block092Part017
    + surrogateDiagTailX0RatChunk000Sub001Block092Part018
    + surrogateDiagTailX0RatChunk000Sub001Block092Part019

def surrogateDiagonalTailChunk000Sub001Block092TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block092Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block092Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block092Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block092Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block092Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block092Tail : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block092Part020
    + surrogateDiagTailX0RatChunk000Sub001Block092Part021
    + surrogateDiagTailX0RatChunk000Sub001Block092Part022
    + surrogateDiagTailX0RatChunk000Sub001Block092Part023
    + surrogateDiagTailX0RatChunk000Sub001Block092Part024

def surrogateDiagonalTailChunk000Sub001Block092Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub001Block092HeadSum X0
    + surrogateDiagonalTailChunk000Sub001Block092MidSum X0
    + surrogateDiagonalTailChunk000Sub001Block092TailSum X0

def surrogateDiagTailX0RatChunk000Sub001Block092 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block092Part000
    + surrogateDiagTailX0RatChunk000Sub001Block092Part001
    + surrogateDiagTailX0RatChunk000Sub001Block092Part002
    + surrogateDiagTailX0RatChunk000Sub001Block092Part003
    + surrogateDiagTailX0RatChunk000Sub001Block092Part004
    + surrogateDiagTailX0RatChunk000Sub001Block092Part005
    + surrogateDiagTailX0RatChunk000Sub001Block092Part006
    + surrogateDiagTailX0RatChunk000Sub001Block092Part007
    + surrogateDiagTailX0RatChunk000Sub001Block092Part008
    + surrogateDiagTailX0RatChunk000Sub001Block092Part009
    + surrogateDiagTailX0RatChunk000Sub001Block092Part010
    + surrogateDiagTailX0RatChunk000Sub001Block092Part011
    + surrogateDiagTailX0RatChunk000Sub001Block092Part012
    + surrogateDiagTailX0RatChunk000Sub001Block092Part013
    + surrogateDiagTailX0RatChunk000Sub001Block092Part014
    + surrogateDiagTailX0RatChunk000Sub001Block092Part015
    + surrogateDiagTailX0RatChunk000Sub001Block092Part016
    + surrogateDiagTailX0RatChunk000Sub001Block092Part017
    + surrogateDiagTailX0RatChunk000Sub001Block092Part018
    + surrogateDiagTailX0RatChunk000Sub001Block092Part019
    + surrogateDiagTailX0RatChunk000Sub001Block092Part020
    + surrogateDiagTailX0RatChunk000Sub001Block092Part021
    + surrogateDiagTailX0RatChunk000Sub001Block092Part022
    + surrogateDiagTailX0RatChunk000Sub001Block092Part023
    + surrogateDiagTailX0RatChunk000Sub001Block092Part024

theorem surrogateDiagTailX0RatChunk000Sub001Block092_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk000Sub001Block092Head + surrogateDiagTailX0RatChunk000Sub001Block092Mid + surrogateDiagTailX0RatChunk000Sub001Block092Tail =
      surrogateDiagTailX0RatChunk000Sub001Block092 := by
  unfold surrogateDiagTailX0RatChunk000Sub001Block092Head surrogateDiagTailX0RatChunk000Sub001Block092Mid surrogateDiagTailX0RatChunk000Sub001Block092Tail surrogateDiagTailX0RatChunk000Sub001Block092
  ring

def SurrogateDiagonalTailChunk000Sub001Block092HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block092HeadSum X0 = surrogateDiagTailX0RatChunk000Sub001Block092Head

def SurrogateDiagonalTailChunk000Sub001Block092MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block092MidSum X0 = surrogateDiagTailX0RatChunk000Sub001Block092Mid

def SurrogateDiagonalTailChunk000Sub001Block092TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block092TailSum X0 = surrogateDiagTailX0RatChunk000Sub001Block092Tail

theorem surrogateDiagonalTailChunk000Sub001Block092_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk000Sub001Block092HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk000Sub001Block092MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk000Sub001Block092TailCertificateAt X0) :
    surrogateDiagonalTailChunk000Sub001Block092Sum X0 = surrogateDiagTailX0RatChunk000Sub001Block092 := by
  unfold SurrogateDiagonalTailChunk000Sub001Block092HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk000Sub001Block092MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk000Sub001Block092TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk000Sub001Block092Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk000Sub001Block092_eq_head_add_mid_add_tail

/-- Block 093 covers tail-support indices [7325,7350) and q from 12102 to 12143. -/

def TailChunk000Sub001Block093Part000SupportExplicit : Finset ℕ :=
  ([12102] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block093Part000 : ℚ :=
  (148175 : ℚ) / 64210599936

def SurrogateDiagonalTailChunk000Sub001Block093Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12102
    = surrogateDiagTailX0RatChunk000Sub001Block093Part000

theorem surrogateDiagonalTailChunk000Sub001Block093Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block093Part000CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block093Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block093Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block093Part000CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block093Part000SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block093Part000] using hcert

def TailChunk000Sub001Block093Part001SupportExplicit : Finset ℕ :=
  ([12106] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block093Part001 : ℚ :=
  (572481390625 : ℚ) / 838614843120497952

def SurrogateDiagonalTailChunk000Sub001Block093Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12106
    = surrogateDiagTailX0RatChunk000Sub001Block093Part001

theorem surrogateDiagonalTailChunk000Sub001Block093Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block093Part001CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block093Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block093Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block093Part001CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block093Part001SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block093Part001] using hcert

def TailChunk000Sub001Block093Part002SupportExplicit : Finset ℕ :=
  ([12107] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block093Part002 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block093Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12107
    = surrogateDiagTailX0RatChunk000Sub001Block093Part002

theorem surrogateDiagonalTailChunk000Sub001Block093Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block093Part002CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block093Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block093Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block093Part002CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block093Part002SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block093Part002] using hcert

def TailChunk000Sub001Block093Part003SupportExplicit : Finset ℕ :=
  ([12109] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block093Part003 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block093Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12109
    = surrogateDiagTailX0RatChunk000Sub001Block093Part003

theorem surrogateDiagonalTailChunk000Sub001Block093Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block093Part003CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block093Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block093Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block093Part003CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block093Part003SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block093Part003] using hcert

def TailChunk000Sub001Block093Part004SupportExplicit : Finset ℕ :=
  ([12110] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block093Part004 : ℚ :=
  (747171844325 : ℚ) / 363040952256036864

def SurrogateDiagonalTailChunk000Sub001Block093Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12110
    = surrogateDiagTailX0RatChunk000Sub001Block093Part004

theorem surrogateDiagonalTailChunk000Sub001Block093Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block093Part004CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block093Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block093Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block093Part004CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block093Part004SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block093Part004] using hcert

def TailChunk000Sub001Block093Part005SupportExplicit : Finset ℕ :=
  ([12111] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block093Part005 : ℚ :=
  (15050662391 : ℚ) / 57432956089559040

def SurrogateDiagonalTailChunk000Sub001Block093Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12111
    = surrogateDiagTailX0RatChunk000Sub001Block093Part005

theorem surrogateDiagonalTailChunk000Sub001Block093Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block093Part005CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block093Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block093Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block093Part005CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block093Part005SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block093Part005] using hcert

def TailChunk000Sub001Block093Part006SupportExplicit : Finset ℕ :=
  ([12113] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block093Part006 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block093Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12113
    = surrogateDiagTailX0RatChunk000Sub001Block093Part006

theorem surrogateDiagonalTailChunk000Sub001Block093Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block093Part006CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block093Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block093Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block093Part006CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block093Part006SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block093Part006] using hcert

def TailChunk000Sub001Block093Part007SupportExplicit : Finset ℕ :=
  ([12115] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block093Part007 : ℚ :=
  (734364246025 : ℚ) / 22027407157347207168

def SurrogateDiagonalTailChunk000Sub001Block093Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12115
    = surrogateDiagTailX0RatChunk000Sub001Block093Part007

theorem surrogateDiagonalTailChunk000Sub001Block093Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block093Part007CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block093Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block093Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block093Part007CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block093Part007SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block093Part007] using hcert

def TailChunk000Sub001Block093Part008SupportExplicit : Finset ℕ :=
  ([12117] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block093Part008 : ℚ :=
  (1828061401225 : ℚ) / 5707445547741216768

def SurrogateDiagonalTailChunk000Sub001Block093Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12117
    = surrogateDiagTailX0RatChunk000Sub001Block093Part008

theorem surrogateDiagonalTailChunk000Sub001Block093Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block093Part008CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block093Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block093Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block093Part008CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block093Part008SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block093Part008] using hcert

def TailChunk000Sub001Block093Part009SupportExplicit : Finset ℕ :=
  ([12118] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block093Part009 : ℚ :=
  (741937627825 : ℚ) / 1012723760310091776

def SurrogateDiagonalTailChunk000Sub001Block093Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12118
    = surrogateDiagTailX0RatChunk000Sub001Block093Part009

theorem surrogateDiagonalTailChunk000Sub001Block093Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block093Part009CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block093Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block093Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block093Part009CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block093Part009SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block093Part009] using hcert

def TailChunk000Sub001Block093Part010SupportExplicit : Finset ℕ :=
  ([12119] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block093Part010 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block093Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12119
    = surrogateDiagTailX0RatChunk000Sub001Block093Part010

theorem surrogateDiagonalTailChunk000Sub001Block093Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block093Part010CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block093Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block093Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block093Part010CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block093Part010SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block093Part010] using hcert

def TailChunk000Sub001Block093Part011SupportExplicit : Finset ℕ :=
  ([12121] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block093Part011 : ℚ :=
  (329924131 : ℚ) / 22614127348285440

def SurrogateDiagonalTailChunk000Sub001Block093Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12121
    = surrogateDiagTailX0RatChunk000Sub001Block093Part011

theorem surrogateDiagonalTailChunk000Sub001Block093Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block093Part011CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block093Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block093Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block093Part011CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block093Part011SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block093Part011] using hcert

def TailChunk000Sub001Block093Part012SupportExplicit : Finset ℕ :=
  ([12122] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block093Part012 : ℚ :=
  (73993231861 : ℚ) / 64537033081651200

def SurrogateDiagonalTailChunk000Sub001Block093Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12122
    = surrogateDiagTailX0RatChunk000Sub001Block093Part012

theorem surrogateDiagonalTailChunk000Sub001Block093Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block093Part012CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block093Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block093Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block093Part012CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block093Part012SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block093Part012] using hcert

def TailChunk000Sub001Block093Part013SupportExplicit : Finset ℕ :=
  ([12126] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block093Part013 : ℚ :=
  (1219723823875 : ℚ) / 557410736870443008

def SurrogateDiagonalTailChunk000Sub001Block093Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12126
    = surrogateDiagTailX0RatChunk000Sub001Block093Part013

theorem surrogateDiagonalTailChunk000Sub001Block093Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block093Part013CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block093Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block093Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block093Part013CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block093Part013SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block093Part013] using hcert

def TailChunk000Sub001Block093Part014SupportExplicit : Finset ℕ :=
  ([12127] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block093Part014 : ℚ :=
  (3084650167 : ℚ) / 1992290264713267200

def SurrogateDiagonalTailChunk000Sub001Block093Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12127
    = surrogateDiagTailX0RatChunk000Sub001Block093Part014

theorem surrogateDiagonalTailChunk000Sub001Block093Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block093Part014CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block093Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block093Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block093Part014CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block093Part014SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block093Part014] using hcert

def TailChunk000Sub001Block093Part015SupportExplicit : Finset ℕ :=
  ([12129] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block093Part015 : ℚ :=
  (21410737097 : ℚ) / 153231691858329600

def SurrogateDiagonalTailChunk000Sub001Block093Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12129
    = surrogateDiagTailX0RatChunk000Sub001Block093Part015

theorem surrogateDiagonalTailChunk000Sub001Block093Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block093Part015CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block093Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block093Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block093Part015CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block093Part015SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block093Part015] using hcert

def TailChunk000Sub001Block093Part016SupportExplicit : Finset ℕ :=
  ([12130] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block093Part016 : ℚ :=
  (290991944275 : ℚ) / 230210990339309568

def SurrogateDiagonalTailChunk000Sub001Block093Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12130
    = surrogateDiagTailX0RatChunk000Sub001Block093Part016

theorem surrogateDiagonalTailChunk000Sub001Block093Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block093Part016CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block093Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block093Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block093Part016CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block093Part016SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block093Part016] using hcert

def TailChunk000Sub001Block093Part017SupportExplicit : Finset ℕ :=
  ([12131] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block093Part017 : ℚ :=
  (31339813225 : ℚ) / 1620133887560795136

def SurrogateDiagonalTailChunk000Sub001Block093Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12131
    = surrogateDiagTailX0RatChunk000Sub001Block093Part017

theorem surrogateDiagonalTailChunk000Sub001Block093Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block093Part017CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block093Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block093Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block093Part017CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block093Part017SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block093Part017] using hcert

def TailChunk000Sub001Block093Part018SupportExplicit : Finset ℕ :=
  ([12133] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block093Part018 : ℚ :=
  (4087282767 : ℚ) / 491690676877014400

def SurrogateDiagonalTailChunk000Sub001Block093Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12133
    = surrogateDiagTailX0RatChunk000Sub001Block093Part018

theorem surrogateDiagonalTailChunk000Sub001Block093Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block093Part018CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block093Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block093Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block093Part018CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block093Part018SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block093Part018] using hcert

def TailChunk000Sub001Block093Part019SupportExplicit : Finset ℕ :=
  ([12134] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block093Part019 : ℚ :=
  (575132640625 : ℚ) / 846401630776069842

def SurrogateDiagonalTailChunk000Sub001Block093Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12134
    = surrogateDiagTailX0RatChunk000Sub001Block093Part019

theorem surrogateDiagonalTailChunk000Sub001Block093Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block093Part019CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block093Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block093Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block093Part019CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block093Part019SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block093Part019] using hcert

def TailChunk000Sub001Block093Part020SupportExplicit : Finset ℕ :=
  ([12135] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block093Part020 : ℚ :=
  (368074587825 : ℚ) / 1455160827823783936

def SurrogateDiagonalTailChunk000Sub001Block093Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12135
    = surrogateDiagTailX0RatChunk000Sub001Block093Part020

theorem surrogateDiagonalTailChunk000Sub001Block093Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block093Part020CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block093Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block093Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block093Part020CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block093Part020SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block093Part020] using hcert

def TailChunk000Sub001Block093Part021SupportExplicit : Finset ℕ :=
  ([12137] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block093Part021 : ℚ :=
  (43767126425 : ℚ) / 24702995869688807424

def SurrogateDiagonalTailChunk000Sub001Block093Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12137
    = surrogateDiagTailX0RatChunk000Sub001Block093Part021

theorem surrogateDiagonalTailChunk000Sub001Block093Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block093Part021CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block093Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block093Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block093Part021CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block093Part021SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block093Part021] using hcert

def TailChunk000Sub001Block093Part022SupportExplicit : Finset ℕ :=
  ([12139] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block093Part022 : ℚ :=
  (3188744809 : ℚ) / 1992290264713267200

def SurrogateDiagonalTailChunk000Sub001Block093Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12139
    = surrogateDiagTailX0RatChunk000Sub001Block093Part022

theorem surrogateDiagonalTailChunk000Sub001Block093Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block093Part022CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block093Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block093Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block093Part022CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block093Part022SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block093Part022] using hcert

def TailChunk000Sub001Block093Part023SupportExplicit : Finset ℕ :=
  ([12142] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block093Part023 : ℚ :=
  (698092779275 : ℚ) / 815031239299209216

def SurrogateDiagonalTailChunk000Sub001Block093Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12142
    = surrogateDiagTailX0RatChunk000Sub001Block093Part023

theorem surrogateDiagonalTailChunk000Sub001Block093Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block093Part023CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block093Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block093Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block093Part023CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block093Part023SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block093Part023] using hcert

def TailChunk000Sub001Block093Part024SupportExplicit : Finset ℕ :=
  ([12143] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block093Part024 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block093Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12143
    = surrogateDiagTailX0RatChunk000Sub001Block093Part024

theorem surrogateDiagonalTailChunk000Sub001Block093Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block093Part024CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block093Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block093Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block093Part024CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block093Part024SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block093Part024] using hcert

def surrogateDiagonalTailChunk000Sub001Block093HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block093Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block093Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block093Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block093Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block093Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block093Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block093Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block093Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block093Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block093Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block093Head : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block093Part000
    + surrogateDiagTailX0RatChunk000Sub001Block093Part001
    + surrogateDiagTailX0RatChunk000Sub001Block093Part002
    + surrogateDiagTailX0RatChunk000Sub001Block093Part003
    + surrogateDiagTailX0RatChunk000Sub001Block093Part004
    + surrogateDiagTailX0RatChunk000Sub001Block093Part005
    + surrogateDiagTailX0RatChunk000Sub001Block093Part006
    + surrogateDiagTailX0RatChunk000Sub001Block093Part007
    + surrogateDiagTailX0RatChunk000Sub001Block093Part008
    + surrogateDiagTailX0RatChunk000Sub001Block093Part009

def surrogateDiagonalTailChunk000Sub001Block093MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block093Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block093Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block093Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block093Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block093Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block093Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block093Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block093Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block093Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block093Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block093Mid : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block093Part010
    + surrogateDiagTailX0RatChunk000Sub001Block093Part011
    + surrogateDiagTailX0RatChunk000Sub001Block093Part012
    + surrogateDiagTailX0RatChunk000Sub001Block093Part013
    + surrogateDiagTailX0RatChunk000Sub001Block093Part014
    + surrogateDiagTailX0RatChunk000Sub001Block093Part015
    + surrogateDiagTailX0RatChunk000Sub001Block093Part016
    + surrogateDiagTailX0RatChunk000Sub001Block093Part017
    + surrogateDiagTailX0RatChunk000Sub001Block093Part018
    + surrogateDiagTailX0RatChunk000Sub001Block093Part019

def surrogateDiagonalTailChunk000Sub001Block093TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block093Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block093Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block093Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block093Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block093Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block093Tail : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block093Part020
    + surrogateDiagTailX0RatChunk000Sub001Block093Part021
    + surrogateDiagTailX0RatChunk000Sub001Block093Part022
    + surrogateDiagTailX0RatChunk000Sub001Block093Part023
    + surrogateDiagTailX0RatChunk000Sub001Block093Part024

def surrogateDiagonalTailChunk000Sub001Block093Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub001Block093HeadSum X0
    + surrogateDiagonalTailChunk000Sub001Block093MidSum X0
    + surrogateDiagonalTailChunk000Sub001Block093TailSum X0

def surrogateDiagTailX0RatChunk000Sub001Block093 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block093Part000
    + surrogateDiagTailX0RatChunk000Sub001Block093Part001
    + surrogateDiagTailX0RatChunk000Sub001Block093Part002
    + surrogateDiagTailX0RatChunk000Sub001Block093Part003
    + surrogateDiagTailX0RatChunk000Sub001Block093Part004
    + surrogateDiagTailX0RatChunk000Sub001Block093Part005
    + surrogateDiagTailX0RatChunk000Sub001Block093Part006
    + surrogateDiagTailX0RatChunk000Sub001Block093Part007
    + surrogateDiagTailX0RatChunk000Sub001Block093Part008
    + surrogateDiagTailX0RatChunk000Sub001Block093Part009
    + surrogateDiagTailX0RatChunk000Sub001Block093Part010
    + surrogateDiagTailX0RatChunk000Sub001Block093Part011
    + surrogateDiagTailX0RatChunk000Sub001Block093Part012
    + surrogateDiagTailX0RatChunk000Sub001Block093Part013
    + surrogateDiagTailX0RatChunk000Sub001Block093Part014
    + surrogateDiagTailX0RatChunk000Sub001Block093Part015
    + surrogateDiagTailX0RatChunk000Sub001Block093Part016
    + surrogateDiagTailX0RatChunk000Sub001Block093Part017
    + surrogateDiagTailX0RatChunk000Sub001Block093Part018
    + surrogateDiagTailX0RatChunk000Sub001Block093Part019
    + surrogateDiagTailX0RatChunk000Sub001Block093Part020
    + surrogateDiagTailX0RatChunk000Sub001Block093Part021
    + surrogateDiagTailX0RatChunk000Sub001Block093Part022
    + surrogateDiagTailX0RatChunk000Sub001Block093Part023
    + surrogateDiagTailX0RatChunk000Sub001Block093Part024

theorem surrogateDiagTailX0RatChunk000Sub001Block093_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk000Sub001Block093Head + surrogateDiagTailX0RatChunk000Sub001Block093Mid + surrogateDiagTailX0RatChunk000Sub001Block093Tail =
      surrogateDiagTailX0RatChunk000Sub001Block093 := by
  unfold surrogateDiagTailX0RatChunk000Sub001Block093Head surrogateDiagTailX0RatChunk000Sub001Block093Mid surrogateDiagTailX0RatChunk000Sub001Block093Tail surrogateDiagTailX0RatChunk000Sub001Block093
  ring

def SurrogateDiagonalTailChunk000Sub001Block093HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block093HeadSum X0 = surrogateDiagTailX0RatChunk000Sub001Block093Head

def SurrogateDiagonalTailChunk000Sub001Block093MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block093MidSum X0 = surrogateDiagTailX0RatChunk000Sub001Block093Mid

def SurrogateDiagonalTailChunk000Sub001Block093TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block093TailSum X0 = surrogateDiagTailX0RatChunk000Sub001Block093Tail

theorem surrogateDiagonalTailChunk000Sub001Block093_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk000Sub001Block093HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk000Sub001Block093MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk000Sub001Block093TailCertificateAt X0) :
    surrogateDiagonalTailChunk000Sub001Block093Sum X0 = surrogateDiagTailX0RatChunk000Sub001Block093 := by
  unfold SurrogateDiagonalTailChunk000Sub001Block093HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk000Sub001Block093MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk000Sub001Block093TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk000Sub001Block093Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk000Sub001Block093_eq_head_add_mid_add_tail

/-- Block 094 covers tail-support indices [7350,7375) and q from 12145 to 12183. -/

def TailChunk000Sub001Block094Part000SupportExplicit : Finset ℕ :=
  ([12145] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block094Part000 : ℚ :=
  (980090108875 : ℚ) / 11889845762566422528

def SurrogateDiagonalTailChunk000Sub001Block094Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12145
    = surrogateDiagTailX0RatChunk000Sub001Block094Part000

theorem surrogateDiagonalTailChunk000Sub001Block094Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block094Part000CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block094Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block094Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block094Part000CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block094Part000SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block094Part000] using hcert

def TailChunk000Sub001Block094Part001SupportExplicit : Finset ℕ :=
  ([12146] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block094Part001 : ℚ :=
  (576270765625 : ℚ) / 849755372607263232

def SurrogateDiagonalTailChunk000Sub001Block094Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12146
    = surrogateDiagTailX0RatChunk000Sub001Block094Part001

theorem surrogateDiagonalTailChunk000Sub001Block094Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block094Part001CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block094Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block094Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block094Part001CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block094Part001SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block094Part001] using hcert

def TailChunk000Sub001Block094Part002SupportExplicit : Finset ℕ :=
  ([12147] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block094Part002 : ℚ :=
  (256192271575 : ℚ) / 2685646609721720832

def SurrogateDiagonalTailChunk000Sub001Block094Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12147
    = surrogateDiagTailX0RatChunk000Sub001Block094Part002

theorem surrogateDiagonalTailChunk000Sub001Block094Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block094Part002CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block094Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block094Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block094Part002CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block094Part002SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block094Part002] using hcert

def TailChunk000Sub001Block094Part003SupportExplicit : Finset ℕ :=
  ([12149] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block094Part003 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block094Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12149
    = surrogateDiagTailX0RatChunk000Sub001Block094Part003

theorem surrogateDiagonalTailChunk000Sub001Block094Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block094Part003CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block094Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block094Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block094Part003CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block094Part003SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block094Part003] using hcert

def TailChunk000Sub001Block094Part004SupportExplicit : Finset ℕ :=
  ([12151] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block094Part004 : ℚ :=
  (34871409775 : ℚ) / 11730164971653714432

def SurrogateDiagonalTailChunk000Sub001Block094Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12151
    = surrogateDiagTailX0RatChunk000Sub001Block094Part004

theorem surrogateDiagonalTailChunk000Sub001Block094Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block094Part004CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block094Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block094Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block094Part004CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block094Part004SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block094Part004] using hcert

def TailChunk000Sub001Block094Part005SupportExplicit : Finset ℕ :=
  ([12153] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block094Part005 : ℚ :=
  (820625069 : ℚ) / 8611066068840000

def SurrogateDiagonalTailChunk000Sub001Block094Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12153
    = surrogateDiagTailX0RatChunk000Sub001Block094Part005

theorem surrogateDiagonalTailChunk000Sub001Block094Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block094Part005CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block094Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block094Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block094Part005CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block094Part005SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block094Part005] using hcert

def TailChunk000Sub001Block094Part006SupportExplicit : Finset ℕ :=
  ([12154] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block094Part006 : ℚ :=
  (62122211225 : ℚ) / 85081868588563488

def SurrogateDiagonalTailChunk000Sub001Block094Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12154
    = surrogateDiagTailX0RatChunk000Sub001Block094Part006

theorem surrogateDiagonalTailChunk000Sub001Block094Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block094Part006CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block094Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block094Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block094Part006CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block094Part006SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block094Part006] using hcert

def TailChunk000Sub001Block094Part007SupportExplicit : Finset ℕ :=
  ([12155] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block094Part007 : ℚ :=
  (41116967221 : ℚ) / 347961929446195200

def SurrogateDiagonalTailChunk000Sub001Block094Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12155
    = surrogateDiagTailX0RatChunk000Sub001Block094Part007

theorem surrogateDiagonalTailChunk000Sub001Block094Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block094Part007CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block094Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block094Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block094Part007CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block094Part007SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block094Part007] using hcert

def TailChunk000Sub001Block094Part008SupportExplicit : Finset ℕ :=
  ([12157] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block094Part008 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block094Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12157
    = surrogateDiagTailX0RatChunk000Sub001Block094Part008

theorem surrogateDiagonalTailChunk000Sub001Block094Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block094Part008CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block094Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block094Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block094Part008CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block094Part008SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block094Part008] using hcert

def TailChunk000Sub001Block094Part009SupportExplicit : Finset ℕ :=
  ([12158] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block094Part009 : ℚ :=
  (577410015625 : ℚ) / 853119071110692882

def SurrogateDiagonalTailChunk000Sub001Block094Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12158
    = surrogateDiagTailX0RatChunk000Sub001Block094Part009

theorem surrogateDiagonalTailChunk000Sub001Block094Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block094Part009CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block094Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block094Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block094Part009CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block094Part009SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block094Part009] using hcert

def TailChunk000Sub001Block094Part010SupportExplicit : Finset ℕ :=
  ([12161] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block094Part010 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block094Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12161
    = surrogateDiagTailX0RatChunk000Sub001Block094Part010

theorem surrogateDiagonalTailChunk000Sub001Block094Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block094Part010CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block094Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block094Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block094Part010CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block094Part010SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block094Part010] using hcert

def TailChunk000Sub001Block094Part011SupportExplicit : Finset ℕ :=
  ([12162] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block094Part011 : ℚ :=
  (153987825 : ℚ) / 67393460259904

def SurrogateDiagonalTailChunk000Sub001Block094Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12162
    = surrogateDiagTailX0RatChunk000Sub001Block094Part011

theorem surrogateDiagonalTailChunk000Sub001Block094Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block094Part011CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block094Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block094Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block094Part011CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block094Part011SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block094Part011] using hcert

def TailChunk000Sub001Block094Part012SupportExplicit : Finset ℕ :=
  ([12163] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block094Part012 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block094Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12163
    = surrogateDiagTailX0RatChunk000Sub001Block094Part012

theorem surrogateDiagonalTailChunk000Sub001Block094Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block094Part012CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block094Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block094Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block094Part012CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block094Part012SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block094Part012] using hcert

def TailChunk000Sub001Block094Part013SupportExplicit : Finset ℕ :=
  ([12165] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block094Part013 : ℚ :=
  (1775495353 : ℚ) / 7054185323593728

def SurrogateDiagonalTailChunk000Sub001Block094Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12165
    = surrogateDiagTailX0RatChunk000Sub001Block094Part013

theorem surrogateDiagonalTailChunk000Sub001Block094Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block094Part013CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block094Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block094Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block094Part013CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block094Part013SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block094Part013] using hcert

def TailChunk000Sub001Block094Part014SupportExplicit : Finset ℕ :=
  ([12166] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block094Part014 : ℚ :=
  (2132487509 : ℚ) / 1499409589953600

def SurrogateDiagonalTailChunk000Sub001Block094Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12166
    = surrogateDiagTailX0RatChunk000Sub001Block094Part014

theorem surrogateDiagonalTailChunk000Sub001Block094Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block094Part014CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block094Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block094Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block094Part014CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block094Part014SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block094Part014] using hcert

def TailChunk000Sub001Block094Part015SupportExplicit : Finset ℕ :=
  ([12169] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block094Part015 : ℚ :=
  (1263706375 : ℚ) / 607484826629831808

def SurrogateDiagonalTailChunk000Sub001Block094Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12169
    = surrogateDiagTailX0RatChunk000Sub001Block094Part015

theorem surrogateDiagonalTailChunk000Sub001Block094Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block094Part015CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block094Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block094Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block094Part015CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block094Part015SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block094Part015] using hcert

def TailChunk000Sub001Block094Part016SupportExplicit : Finset ℕ :=
  ([12170] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block094Part016 : ℚ :=
  (61782038025 : ℚ) / 233265157445255168

def SurrogateDiagonalTailChunk000Sub001Block094Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12170
    = surrogateDiagTailX0RatChunk000Sub001Block094Part016

theorem surrogateDiagonalTailChunk000Sub001Block094Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block094Part016CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block094Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block094Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block094Part016CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block094Part016SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block094Part016] using hcert

def TailChunk000Sub001Block094Part017SupportExplicit : Finset ℕ :=
  ([12171] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block094Part017 : ℚ :=
  (257205271525 : ℚ) / 2706940036656340992

def SurrogateDiagonalTailChunk000Sub001Block094Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12171
    = surrogateDiagTailX0RatChunk000Sub001Block094Part017

theorem surrogateDiagonalTailChunk000Sub001Block094Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block094Part017CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block094Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block094Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block094Part017CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block094Part017SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block094Part017] using hcert

def TailChunk000Sub001Block094Part018SupportExplicit : Finset ℕ :=
  ([12173] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block094Part018 : ℚ :=
  (663390906625 : ℚ) / 24370991051108548608

def SurrogateDiagonalTailChunk000Sub001Block094Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12173
    = surrogateDiagTailX0RatChunk000Sub001Block094Part018

theorem surrogateDiagonalTailChunk000Sub001Block094Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block094Part018CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block094Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block094Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block094Part018CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block094Part018SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block094Part018] using hcert

def TailChunk000Sub001Block094Part019SupportExplicit : Finset ℕ :=
  ([12174] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block094Part019 : ℚ :=
  (257310051275 : ℚ) / 338367504582042624

def SurrogateDiagonalTailChunk000Sub001Block094Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12174
    = surrogateDiagTailX0RatChunk000Sub001Block094Part019

theorem surrogateDiagonalTailChunk000Sub001Block094Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block094Part019CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block094Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block094Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block094Part019CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block094Part019SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block094Part019] using hcert

def TailChunk000Sub001Block094Part020SupportExplicit : Finset ℕ :=
  ([12178] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block094Part020 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block094Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12178
    = surrogateDiagTailX0RatChunk000Sub001Block094Part020

theorem surrogateDiagonalTailChunk000Sub001Block094Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block094Part020CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block094Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block094Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block094Part020CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block094Part020SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block094Part020] using hcert

def TailChunk000Sub001Block094Part021SupportExplicit : Finset ℕ :=
  ([12179] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block094Part021 : ℚ :=
  (7384287427 : ℚ) / 1761557267821363200

def SurrogateDiagonalTailChunk000Sub001Block094Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12179
    = surrogateDiagTailX0RatChunk000Sub001Block094Part021

theorem surrogateDiagonalTailChunk000Sub001Block094Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block094Part021CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block094Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block094Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block094Part021CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block094Part021SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block094Part021] using hcert

def TailChunk000Sub001Block094Part022SupportExplicit : Finset ℕ :=
  ([12181] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block094Part022 : ℚ :=
  (30812651125 : ℚ) / 4421938809923960832

def SurrogateDiagonalTailChunk000Sub001Block094Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12181
    = surrogateDiagTailX0RatChunk000Sub001Block094Part022

theorem surrogateDiagonalTailChunk000Sub001Block094Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block094Part022CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block094Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block094Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block094Part022CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block094Part022SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block094Part022] using hcert

def TailChunk000Sub001Block094Part023SupportExplicit : Finset ℕ :=
  ([12182] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block094Part023 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block094Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12182
    = surrogateDiagTailX0RatChunk000Sub001Block094Part023

theorem surrogateDiagonalTailChunk000Sub001Block094Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block094Part023CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block094Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block094Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block094Part023CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block094Part023SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block094Part023] using hcert

def TailChunk000Sub001Block094Part024SupportExplicit : Finset ℕ :=
  ([12183] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block094Part024 : ℚ :=
  (41858802103 : ℚ) / 370224590112000000

def SurrogateDiagonalTailChunk000Sub001Block094Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12183
    = surrogateDiagTailX0RatChunk000Sub001Block094Part024

theorem surrogateDiagonalTailChunk000Sub001Block094Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block094Part024CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block094Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block094Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block094Part024CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block094Part024SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block094Part024] using hcert

def surrogateDiagonalTailChunk000Sub001Block094HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block094Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block094Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block094Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block094Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block094Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block094Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block094Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block094Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block094Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block094Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block094Head : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block094Part000
    + surrogateDiagTailX0RatChunk000Sub001Block094Part001
    + surrogateDiagTailX0RatChunk000Sub001Block094Part002
    + surrogateDiagTailX0RatChunk000Sub001Block094Part003
    + surrogateDiagTailX0RatChunk000Sub001Block094Part004
    + surrogateDiagTailX0RatChunk000Sub001Block094Part005
    + surrogateDiagTailX0RatChunk000Sub001Block094Part006
    + surrogateDiagTailX0RatChunk000Sub001Block094Part007
    + surrogateDiagTailX0RatChunk000Sub001Block094Part008
    + surrogateDiagTailX0RatChunk000Sub001Block094Part009

def surrogateDiagonalTailChunk000Sub001Block094MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block094Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block094Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block094Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block094Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block094Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block094Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block094Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block094Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block094Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block094Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block094Mid : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block094Part010
    + surrogateDiagTailX0RatChunk000Sub001Block094Part011
    + surrogateDiagTailX0RatChunk000Sub001Block094Part012
    + surrogateDiagTailX0RatChunk000Sub001Block094Part013
    + surrogateDiagTailX0RatChunk000Sub001Block094Part014
    + surrogateDiagTailX0RatChunk000Sub001Block094Part015
    + surrogateDiagTailX0RatChunk000Sub001Block094Part016
    + surrogateDiagTailX0RatChunk000Sub001Block094Part017
    + surrogateDiagTailX0RatChunk000Sub001Block094Part018
    + surrogateDiagTailX0RatChunk000Sub001Block094Part019

def surrogateDiagonalTailChunk000Sub001Block094TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block094Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block094Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block094Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block094Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block094Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block094Tail : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block094Part020
    + surrogateDiagTailX0RatChunk000Sub001Block094Part021
    + surrogateDiagTailX0RatChunk000Sub001Block094Part022
    + surrogateDiagTailX0RatChunk000Sub001Block094Part023
    + surrogateDiagTailX0RatChunk000Sub001Block094Part024

def surrogateDiagonalTailChunk000Sub001Block094Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub001Block094HeadSum X0
    + surrogateDiagonalTailChunk000Sub001Block094MidSum X0
    + surrogateDiagonalTailChunk000Sub001Block094TailSum X0

def surrogateDiagTailX0RatChunk000Sub001Block094 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block094Part000
    + surrogateDiagTailX0RatChunk000Sub001Block094Part001
    + surrogateDiagTailX0RatChunk000Sub001Block094Part002
    + surrogateDiagTailX0RatChunk000Sub001Block094Part003
    + surrogateDiagTailX0RatChunk000Sub001Block094Part004
    + surrogateDiagTailX0RatChunk000Sub001Block094Part005
    + surrogateDiagTailX0RatChunk000Sub001Block094Part006
    + surrogateDiagTailX0RatChunk000Sub001Block094Part007
    + surrogateDiagTailX0RatChunk000Sub001Block094Part008
    + surrogateDiagTailX0RatChunk000Sub001Block094Part009
    + surrogateDiagTailX0RatChunk000Sub001Block094Part010
    + surrogateDiagTailX0RatChunk000Sub001Block094Part011
    + surrogateDiagTailX0RatChunk000Sub001Block094Part012
    + surrogateDiagTailX0RatChunk000Sub001Block094Part013
    + surrogateDiagTailX0RatChunk000Sub001Block094Part014
    + surrogateDiagTailX0RatChunk000Sub001Block094Part015
    + surrogateDiagTailX0RatChunk000Sub001Block094Part016
    + surrogateDiagTailX0RatChunk000Sub001Block094Part017
    + surrogateDiagTailX0RatChunk000Sub001Block094Part018
    + surrogateDiagTailX0RatChunk000Sub001Block094Part019
    + surrogateDiagTailX0RatChunk000Sub001Block094Part020
    + surrogateDiagTailX0RatChunk000Sub001Block094Part021
    + surrogateDiagTailX0RatChunk000Sub001Block094Part022
    + surrogateDiagTailX0RatChunk000Sub001Block094Part023
    + surrogateDiagTailX0RatChunk000Sub001Block094Part024

theorem surrogateDiagTailX0RatChunk000Sub001Block094_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk000Sub001Block094Head + surrogateDiagTailX0RatChunk000Sub001Block094Mid + surrogateDiagTailX0RatChunk000Sub001Block094Tail =
      surrogateDiagTailX0RatChunk000Sub001Block094 := by
  unfold surrogateDiagTailX0RatChunk000Sub001Block094Head surrogateDiagTailX0RatChunk000Sub001Block094Mid surrogateDiagTailX0RatChunk000Sub001Block094Tail surrogateDiagTailX0RatChunk000Sub001Block094
  ring

def SurrogateDiagonalTailChunk000Sub001Block094HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block094HeadSum X0 = surrogateDiagTailX0RatChunk000Sub001Block094Head

def SurrogateDiagonalTailChunk000Sub001Block094MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block094MidSum X0 = surrogateDiagTailX0RatChunk000Sub001Block094Mid

def SurrogateDiagonalTailChunk000Sub001Block094TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block094TailSum X0 = surrogateDiagTailX0RatChunk000Sub001Block094Tail

theorem surrogateDiagonalTailChunk000Sub001Block094_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk000Sub001Block094HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk000Sub001Block094MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk000Sub001Block094TailCertificateAt X0) :
    surrogateDiagonalTailChunk000Sub001Block094Sum X0 = surrogateDiagTailX0RatChunk000Sub001Block094 := by
  unfold SurrogateDiagonalTailChunk000Sub001Block094HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk000Sub001Block094MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk000Sub001Block094TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk000Sub001Block094Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk000Sub001Block094_eq_head_add_mid_add_tail

/-- Block 095 covers tail-support indices [7375,7400) and q from 12185 to 12226. -/

def TailChunk000Sub001Block095Part000SupportExplicit : Finset ℕ :=
  ([12185] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block095Part000 : ℚ :=
  (247621347175 : ℚ) / 7513714781073801216

def SurrogateDiagonalTailChunk000Sub001Block095Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12185
    = surrogateDiagTailX0RatChunk000Sub001Block095Part000

theorem surrogateDiagonalTailChunk000Sub001Block095Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block095Part000CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block095Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block095Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block095Part000CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block095Part000SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block095Part000] using hcert

def TailChunk000Sub001Block095Part001SupportExplicit : Finset ℕ :=
  ([12187] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block095Part001 : ℚ :=
  (421720411 : ℚ) / 22003668077644800

def SurrogateDiagonalTailChunk000Sub001Block095Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12187
    = surrogateDiagTailX0RatChunk000Sub001Block095Part001

theorem surrogateDiagonalTailChunk000Sub001Block095Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block095Part001CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block095Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block095Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block095Part001CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block095Part001SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block095Part001] using hcert

def TailChunk000Sub001Block095Part002SupportExplicit : Finset ℕ :=
  ([12189] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block095Part002 : ℚ :=
  (352624037775 : ℚ) / 2804228156771270656

def SurrogateDiagonalTailChunk000Sub001Block095Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12189
    = surrogateDiagTailX0RatChunk000Sub001Block095Part002

theorem surrogateDiagonalTailChunk000Sub001Block095Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block095Part002CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block095Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block095Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block095Part002CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block095Part002SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block095Part002] using hcert

def TailChunk000Sub001Block095Part003SupportExplicit : Finset ℕ :=
  ([12190] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block095Part003 : ℚ :=
  (139362476925 : ℚ) / 365468261478301696

def SurrogateDiagonalTailChunk000Sub001Block095Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12190
    = surrogateDiagTailX0RatChunk000Sub001Block095Part003

theorem surrogateDiagonalTailChunk000Sub001Block095Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block095Part003CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block095Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block095Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block095Part003CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block095Part003SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block095Part003] using hcert

def TailChunk000Sub001Block095Part004SupportExplicit : Finset ℕ :=
  ([12191] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block095Part004 : ℚ :=
  (6000790525 : ℚ) / 4252143873908957184

def SurrogateDiagonalTailChunk000Sub001Block095Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12191
    = surrogateDiagTailX0RatChunk000Sub001Block095Part004

theorem surrogateDiagonalTailChunk000Sub001Block095Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block095Part004CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block095Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block095Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block095Part004CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block095Part004SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block095Part004] using hcert

def TailChunk000Sub001Block095Part005SupportExplicit : Finset ℕ :=
  ([12193] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block095Part005 : ℚ :=
  (70350447325 : ℚ) / 51299505760043532288

def SurrogateDiagonalTailChunk000Sub001Block095Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12193
    = surrogateDiagTailX0RatChunk000Sub001Block095Part005

theorem surrogateDiagonalTailChunk000Sub001Block095Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block095Part005CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block095Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block095Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block095Part005CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block095Part005SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block095Part005] using hcert

def TailChunk000Sub001Block095Part006SupportExplicit : Finset ℕ :=
  ([12194] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block095Part006 : ℚ :=
  (684522775 : ℚ) / 2623592118140928

def SurrogateDiagonalTailChunk000Sub001Block095Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12194
    = surrogateDiagTailX0RatChunk000Sub001Block095Part006

theorem surrogateDiagonalTailChunk000Sub001Block095Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block095Part006CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block095Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block095Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block095Part006CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block095Part006SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block095Part006] using hcert

def TailChunk000Sub001Block095Part007SupportExplicit : Finset ℕ :=
  ([12197] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block095Part007 : ℚ :=
  (2324481390625 : ℚ) / 13830456986737849632

def SurrogateDiagonalTailChunk000Sub001Block095Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12197
    = surrogateDiagTailX0RatChunk000Sub001Block095Part007

theorem surrogateDiagonalTailChunk000Sub001Block095Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block095Part007CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block095Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block095Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block095Part007CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block095Part007SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block095Part007] using hcert

def TailChunk000Sub001Block095Part008SupportExplicit : Finset ℕ :=
  ([12198] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block095Part008 : ℚ :=
  (479699562925 : ℚ) / 176741716412307456

def SurrogateDiagonalTailChunk000Sub001Block095Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12198
    = surrogateDiagTailX0RatChunk000Sub001Block095Part008

theorem surrogateDiagonalTailChunk000Sub001Block095Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block095Part008CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block095Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block095Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block095Part008CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block095Part008SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block095Part008] using hcert

def TailChunk000Sub001Block095Part009SupportExplicit : Finset ℕ :=
  ([12199] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block095Part009 : ℚ :=
  (319359247249 : ℚ) / 1507460328675379200

def SurrogateDiagonalTailChunk000Sub001Block095Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12199
    = surrogateDiagTailX0RatChunk000Sub001Block095Part009

theorem surrogateDiagonalTailChunk000Sub001Block095Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block095Part009CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block095Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block095Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block095Part009CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block095Part009SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block095Part009] using hcert

def TailChunk000Sub001Block095Part010SupportExplicit : Finset ℕ :=
  ([12202] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block095Part010 : ℚ :=
  (37222201 : ℚ) / 55394440672800

def SurrogateDiagonalTailChunk000Sub001Block095Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12202
    = surrogateDiagTailX0RatChunk000Sub001Block095Part010

theorem surrogateDiagonalTailChunk000Sub001Block095Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block095Part010CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block095Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block095Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block095Part010CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block095Part010SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block095Part010] using hcert

def TailChunk000Sub001Block095Part011SupportExplicit : Finset ℕ :=
  ([12203] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block095Part011 : ℚ :=
  (2326768890625 : ℚ) / 13857693457338578802

def SurrogateDiagonalTailChunk000Sub001Block095Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12203
    = surrogateDiagTailX0RatChunk000Sub001Block095Part011

theorem surrogateDiagonalTailChunk000Sub001Block095Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block095Part011CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block095Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block095Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block095Part011CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block095Part011SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block095Part011] using hcert

def TailChunk000Sub001Block095Part012SupportExplicit : Finset ℕ :=
  ([12205] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block095Part012 : ℚ :=
  (253101829219 : ℚ) / 907582515983155200

def SurrogateDiagonalTailChunk000Sub001Block095Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12205
    = surrogateDiagTailX0RatChunk000Sub001Block095Part012

theorem surrogateDiagonalTailChunk000Sub001Block095Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block095Part012CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block095Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block095Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block095Part012CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block095Part012SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block095Part012] using hcert

def TailChunk000Sub001Block095Part013SupportExplicit : Finset ℕ :=
  ([12206] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block095Part013 : ℚ :=
  (720051997575 : ℚ) / 897258624241893376

def SurrogateDiagonalTailChunk000Sub001Block095Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12206
    = surrogateDiagTailX0RatChunk000Sub001Block095Part013

theorem surrogateDiagonalTailChunk000Sub001Block095Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block095Part013CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block095Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block095Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block095Part013CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block095Part013SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block095Part013] using hcert

def TailChunk000Sub001Block095Part014SupportExplicit : Finset ℕ :=
  ([12207] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block095Part014 : ℚ :=
  (505198134475 : ℚ) / 873469394552881152

def SurrogateDiagonalTailChunk000Sub001Block095Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12207
    = surrogateDiagTailX0RatChunk000Sub001Block095Part014

theorem surrogateDiagonalTailChunk000Sub001Block095Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block095Part014CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block095Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block095Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block095Part014CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block095Part014SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block095Part014] using hcert

def TailChunk000Sub001Block095Part015SupportExplicit : Finset ℕ :=
  ([12209] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block095Part015 : ℚ :=
  (38998520999 : ℚ) / 212556126788812800

def SurrogateDiagonalTailChunk000Sub001Block095Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12209
    = surrogateDiagTailX0RatChunk000Sub001Block095Part015

theorem surrogateDiagonalTailChunk000Sub001Block095Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block095Part015CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block095Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block095Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block095Part015CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block095Part015SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block095Part015] using hcert

def TailChunk000Sub001Block095Part016SupportExplicit : Finset ℕ :=
  ([12210] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block095Part016 : ℚ :=
  (8208113981 : ℚ) / 1376216615485440

def SurrogateDiagonalTailChunk000Sub001Block095Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12210
    = surrogateDiagTailX0RatChunk000Sub001Block095Part016

theorem surrogateDiagonalTailChunk000Sub001Block095Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block095Part016CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block095Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block095Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block095Part016CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block095Part016SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block095Part016] using hcert

def TailChunk000Sub001Block095Part017SupportExplicit : Finset ℕ :=
  ([12211] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block095Part017 : ℚ :=
  (3727713025 : ℚ) / 22230514086584562

def SurrogateDiagonalTailChunk000Sub001Block095Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12211
    = surrogateDiagTailX0RatChunk000Sub001Block095Part017

theorem surrogateDiagonalTailChunk000Sub001Block095Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block095Part017CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block095Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block095Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block095Part017CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block095Part017SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block095Part017] using hcert

def TailChunk000Sub001Block095Part018SupportExplicit : Finset ℕ :=
  ([12214] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block095Part018 : ℚ :=
  (11141264021 : ℚ) / 14945352664838400

def SurrogateDiagonalTailChunk000Sub001Block095Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12214
    = surrogateDiagTailX0RatChunk000Sub001Block095Part018

theorem surrogateDiagonalTailChunk000Sub001Block095Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block095Part018CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block095Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block095Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block095Part018CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block095Part018SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block095Part018] using hcert

def TailChunk000Sub001Block095Part019SupportExplicit : Finset ℕ :=
  ([12215] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block095Part019 : ℚ :=
  (4957973223925 : ℚ) / 12167148300214468608

def SurrogateDiagonalTailChunk000Sub001Block095Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12215
    = surrogateDiagTailX0RatChunk000Sub001Block095Part019

theorem surrogateDiagonalTailChunk000Sub001Block095Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block095Part019CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block095Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block095Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block095Part019CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block095Part019SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block095Part019] using hcert

def TailChunk000Sub001Block095Part020SupportExplicit : Finset ℕ :=
  ([12217] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block095Part020 : ℚ :=
  (105349683175 : ℚ) / 550518569480596608

def SurrogateDiagonalTailChunk000Sub001Block095Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12217
    = surrogateDiagTailX0RatChunk000Sub001Block095Part020

theorem surrogateDiagonalTailChunk000Sub001Block095Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block095Part020CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block095Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block095Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block095Part020CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block095Part020SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block095Part020] using hcert

def TailChunk000Sub001Block095Part021SupportExplicit : Finset ℕ :=
  ([12218] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block095Part021 : ℚ :=
  (89936635957 : ℚ) / 122849580299059200

def SurrogateDiagonalTailChunk000Sub001Block095Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12218
    = surrogateDiagTailX0RatChunk000Sub001Block095Part021

theorem surrogateDiagonalTailChunk000Sub001Block095Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block095Part021CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block095Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block095Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block095Part021CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block095Part021SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block095Part021] using hcert

def TailChunk000Sub001Block095Part022SupportExplicit : Finset ℕ :=
  ([12219] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block095Part022 : ℚ :=
  (4145920592725 : ℚ) / 10999625998976974848

def SurrogateDiagonalTailChunk000Sub001Block095Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12219
    = surrogateDiagTailX0RatChunk000Sub001Block095Part022

theorem surrogateDiagonalTailChunk000Sub001Block095Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block095Part022CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block095Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block095Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block095Part022CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block095Part022SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block095Part022] using hcert

def TailChunk000Sub001Block095Part023SupportExplicit : Finset ℕ :=
  ([12223] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block095Part023 : ℚ :=
  (4223864954675 : ℚ) / 21775822649337053184

def SurrogateDiagonalTailChunk000Sub001Block095Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12223
    = surrogateDiagTailX0RatChunk000Sub001Block095Part023

theorem surrogateDiagonalTailChunk000Sub001Block095Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block095Part023CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block095Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block095Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block095Part023CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block095Part023SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block095Part023] using hcert

def TailChunk000Sub001Block095Part024SupportExplicit : Finset ℕ :=
  ([12226] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block095Part024 : ℚ :=
  (583887015625 : ℚ) / 872369051187412992

def SurrogateDiagonalTailChunk000Sub001Block095Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12226
    = surrogateDiagTailX0RatChunk000Sub001Block095Part024

theorem surrogateDiagonalTailChunk000Sub001Block095Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block095Part024CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block095Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block095Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block095Part024CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block095Part024SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block095Part024] using hcert

def surrogateDiagonalTailChunk000Sub001Block095HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block095Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block095Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block095Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block095Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block095Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block095Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block095Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block095Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block095Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block095Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block095Head : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block095Part000
    + surrogateDiagTailX0RatChunk000Sub001Block095Part001
    + surrogateDiagTailX0RatChunk000Sub001Block095Part002
    + surrogateDiagTailX0RatChunk000Sub001Block095Part003
    + surrogateDiagTailX0RatChunk000Sub001Block095Part004
    + surrogateDiagTailX0RatChunk000Sub001Block095Part005
    + surrogateDiagTailX0RatChunk000Sub001Block095Part006
    + surrogateDiagTailX0RatChunk000Sub001Block095Part007
    + surrogateDiagTailX0RatChunk000Sub001Block095Part008
    + surrogateDiagTailX0RatChunk000Sub001Block095Part009

def surrogateDiagonalTailChunk000Sub001Block095MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block095Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block095Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block095Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block095Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block095Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block095Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block095Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block095Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block095Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block095Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block095Mid : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block095Part010
    + surrogateDiagTailX0RatChunk000Sub001Block095Part011
    + surrogateDiagTailX0RatChunk000Sub001Block095Part012
    + surrogateDiagTailX0RatChunk000Sub001Block095Part013
    + surrogateDiagTailX0RatChunk000Sub001Block095Part014
    + surrogateDiagTailX0RatChunk000Sub001Block095Part015
    + surrogateDiagTailX0RatChunk000Sub001Block095Part016
    + surrogateDiagTailX0RatChunk000Sub001Block095Part017
    + surrogateDiagTailX0RatChunk000Sub001Block095Part018
    + surrogateDiagTailX0RatChunk000Sub001Block095Part019

def surrogateDiagonalTailChunk000Sub001Block095TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block095Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block095Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block095Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block095Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block095Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block095Tail : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block095Part020
    + surrogateDiagTailX0RatChunk000Sub001Block095Part021
    + surrogateDiagTailX0RatChunk000Sub001Block095Part022
    + surrogateDiagTailX0RatChunk000Sub001Block095Part023
    + surrogateDiagTailX0RatChunk000Sub001Block095Part024

def surrogateDiagonalTailChunk000Sub001Block095Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub001Block095HeadSum X0
    + surrogateDiagonalTailChunk000Sub001Block095MidSum X0
    + surrogateDiagonalTailChunk000Sub001Block095TailSum X0

def surrogateDiagTailX0RatChunk000Sub001Block095 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block095Part000
    + surrogateDiagTailX0RatChunk000Sub001Block095Part001
    + surrogateDiagTailX0RatChunk000Sub001Block095Part002
    + surrogateDiagTailX0RatChunk000Sub001Block095Part003
    + surrogateDiagTailX0RatChunk000Sub001Block095Part004
    + surrogateDiagTailX0RatChunk000Sub001Block095Part005
    + surrogateDiagTailX0RatChunk000Sub001Block095Part006
    + surrogateDiagTailX0RatChunk000Sub001Block095Part007
    + surrogateDiagTailX0RatChunk000Sub001Block095Part008
    + surrogateDiagTailX0RatChunk000Sub001Block095Part009
    + surrogateDiagTailX0RatChunk000Sub001Block095Part010
    + surrogateDiagTailX0RatChunk000Sub001Block095Part011
    + surrogateDiagTailX0RatChunk000Sub001Block095Part012
    + surrogateDiagTailX0RatChunk000Sub001Block095Part013
    + surrogateDiagTailX0RatChunk000Sub001Block095Part014
    + surrogateDiagTailX0RatChunk000Sub001Block095Part015
    + surrogateDiagTailX0RatChunk000Sub001Block095Part016
    + surrogateDiagTailX0RatChunk000Sub001Block095Part017
    + surrogateDiagTailX0RatChunk000Sub001Block095Part018
    + surrogateDiagTailX0RatChunk000Sub001Block095Part019
    + surrogateDiagTailX0RatChunk000Sub001Block095Part020
    + surrogateDiagTailX0RatChunk000Sub001Block095Part021
    + surrogateDiagTailX0RatChunk000Sub001Block095Part022
    + surrogateDiagTailX0RatChunk000Sub001Block095Part023
    + surrogateDiagTailX0RatChunk000Sub001Block095Part024

theorem surrogateDiagTailX0RatChunk000Sub001Block095_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk000Sub001Block095Head + surrogateDiagTailX0RatChunk000Sub001Block095Mid + surrogateDiagTailX0RatChunk000Sub001Block095Tail =
      surrogateDiagTailX0RatChunk000Sub001Block095 := by
  unfold surrogateDiagTailX0RatChunk000Sub001Block095Head surrogateDiagTailX0RatChunk000Sub001Block095Mid surrogateDiagTailX0RatChunk000Sub001Block095Tail surrogateDiagTailX0RatChunk000Sub001Block095
  ring

def SurrogateDiagonalTailChunk000Sub001Block095HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block095HeadSum X0 = surrogateDiagTailX0RatChunk000Sub001Block095Head

def SurrogateDiagonalTailChunk000Sub001Block095MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block095MidSum X0 = surrogateDiagTailX0RatChunk000Sub001Block095Mid

def SurrogateDiagonalTailChunk000Sub001Block095TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block095TailSum X0 = surrogateDiagTailX0RatChunk000Sub001Block095Tail

theorem surrogateDiagonalTailChunk000Sub001Block095_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk000Sub001Block095HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk000Sub001Block095MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk000Sub001Block095TailCertificateAt X0) :
    surrogateDiagonalTailChunk000Sub001Block095Sum X0 = surrogateDiagTailX0RatChunk000Sub001Block095 := by
  unfold SurrogateDiagonalTailChunk000Sub001Block095HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk000Sub001Block095MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk000Sub001Block095TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk000Sub001Block095Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk000Sub001Block095_eq_head_add_mid_add_tail

/-- Block 096 covers tail-support indices [7400,7425) and q from 12227 to 12265. -/

def TailChunk000Sub001Block096Part000SupportExplicit : Finset ℕ :=
  ([12227] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block096Part000 : ℚ :=
  (2335930140625 : ℚ) / 13967041815546760722

def SurrogateDiagonalTailChunk000Sub001Block096Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12227
    = surrogateDiagTailX0RatChunk000Sub001Block096Part000

theorem surrogateDiagonalTailChunk000Sub001Block096Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block096Part000CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block096Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block096Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block096Part000CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block096Part000SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block096Part000] using hcert

def TailChunk000Sub001Block096Part001SupportExplicit : Finset ℕ :=
  ([12229] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block096Part001 : ℚ :=
  (56585430125 : ℚ) / 235287496209228921

def SurrogateDiagonalTailChunk000Sub001Block096Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12229
    = surrogateDiagTailX0RatChunk000Sub001Block096Part001

theorem surrogateDiagonalTailChunk000Sub001Block096Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block096Part001CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block096Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block096Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block096Part001CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block096Part001SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block096Part001] using hcert

def TailChunk000Sub001Block096Part002SupportExplicit : Finset ℕ :=
  ([12230] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block096Part002 : ℚ :=
  (443715223225 : ℚ) / 356854893452308992

def SurrogateDiagonalTailChunk000Sub001Block096Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12230
    = surrogateDiagTailX0RatChunk000Sub001Block096Part002

theorem surrogateDiagonalTailChunk000Sub001Block096Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block096Part002CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block096Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block096Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block096Part002CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block096Part002SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block096Part002] using hcert

def TailChunk000Sub001Block096Part003SupportExplicit : Finset ℕ :=
  ([12233] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block096Part003 : ℚ :=
  (54519813511 : ℚ) / 269880805944115200

def SurrogateDiagonalTailChunk000Sub001Block096Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12233
    = surrogateDiagTailX0RatChunk000Sub001Block096Part003

theorem surrogateDiagonalTailChunk000Sub001Block096Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block096Part003CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block096Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block096Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block096Part003CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block096Part003SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block096Part003] using hcert

def TailChunk000Sub001Block096Part004SupportExplicit : Finset ℕ :=
  ([12234] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block096Part004 : ℚ :=
  (324695952175 : ℚ) / 172545472805482272

def SurrogateDiagonalTailChunk000Sub001Block096Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12234
    = surrogateDiagTailX0RatChunk000Sub001Block096Part004

theorem surrogateDiagonalTailChunk000Sub001Block096Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block096Part004CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block096Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block096Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block096Part004CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block096Part004SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block096Part004] using hcert

def TailChunk000Sub001Block096Part005SupportExplicit : Finset ℕ :=
  ([12235] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block096Part005 : ℚ :=
  (6358696912525 : ℚ) / 22913563468690311168

def SurrogateDiagonalTailChunk000Sub001Block096Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12235
    = surrogateDiagTailX0RatChunk000Sub001Block096Part005

theorem surrogateDiagonalTailChunk000Sub001Block096Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block096Part005CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block096Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block096Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block096Part005CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block096Part005SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block096Part005] using hcert

def TailChunk000Sub001Block096Part006SupportExplicit : Finset ℕ :=
  ([12237] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block096Part006 : ℚ :=
  (4158145592125 : ℚ) / 11064600231433016448

def SurrogateDiagonalTailChunk000Sub001Block096Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12237
    = surrogateDiagTailX0RatChunk000Sub001Block096Part006

theorem surrogateDiagonalTailChunk000Sub001Block096Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block096Part006CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block096Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block096Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block096Part006CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block096Part006SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block096Part006] using hcert

def TailChunk000Sub001Block096Part007SupportExplicit : Finset ℕ :=
  ([12238] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block096Part007 : ℚ :=
  (9926246497 : ℚ) / 13284757924300800

def SurrogateDiagonalTailChunk000Sub001Block096Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12238
    = surrogateDiagTailX0RatChunk000Sub001Block096Part007

theorem surrogateDiagonalTailChunk000Sub001Block096Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block096Part007CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block096Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block096Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block096Part007CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block096Part007SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block096Part007] using hcert

def TailChunk000Sub001Block096Part008SupportExplicit : Finset ℕ :=
  ([12239] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block096Part008 : ℚ :=
  (2340517515625 : ℚ) / 14021958034339909842

def SurrogateDiagonalTailChunk000Sub001Block096Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12239
    = surrogateDiagTailX0RatChunk000Sub001Block096Part008

theorem surrogateDiagonalTailChunk000Sub001Block096Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block096Part008CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block096Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block096Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block096Part008CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block096Part008SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block096Part008] using hcert

def TailChunk000Sub001Block096Part009SupportExplicit : Finset ℕ :=
  ([12241] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block096Part009 : ℚ :=
  (3746052025 : ℚ) / 22449802332413952

def SurrogateDiagonalTailChunk000Sub001Block096Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12241
    = surrogateDiagTailX0RatChunk000Sub001Block096Part009

theorem surrogateDiagonalTailChunk000Sub001Block096Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block096Part009CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block096Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block096Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block096Part009CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block096Part009SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block096Part009] using hcert

def TailChunk000Sub001Block096Part010SupportExplicit : Finset ℕ :=
  ([12242] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block096Part010 : ℚ :=
  (936666025 : ℚ) / 1403112645775872

def SurrogateDiagonalTailChunk000Sub001Block096Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12242
    = surrogateDiagTailX0RatChunk000Sub001Block096Part010

theorem surrogateDiagonalTailChunk000Sub001Block096Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block096Part010CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block096Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block096Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block096Part010CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block096Part010SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block096Part010] using hcert

def TailChunk000Sub001Block096Part011SupportExplicit : Finset ℕ :=
  ([12243] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block096Part011 : ℚ :=
  (8818034059 : ℚ) / 11664922469990400

def SurrogateDiagonalTailChunk000Sub001Block096Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12243
    = surrogateDiagTailX0RatChunk000Sub001Block096Part011

theorem surrogateDiagonalTailChunk000Sub001Block096Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block096Part011CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block096Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block096Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block096Part011CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block096Part011SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block096Part011] using hcert

def TailChunk000Sub001Block096Part012SupportExplicit : Finset ℕ :=
  ([12245] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block096Part012 : ℚ :=
  (237886744951 : ℚ) / 767697710056243200

def SurrogateDiagonalTailChunk000Sub001Block096Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12245
    = surrogateDiagTailX0RatChunk000Sub001Block096Part012

theorem surrogateDiagonalTailChunk000Sub001Block096Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block096Part012CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block096Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block096Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block096Part012CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block096Part012SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block096Part012] using hcert

def TailChunk000Sub001Block096Part013SupportExplicit : Finset ℕ :=
  ([12246] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block096Part013 : ℚ :=
  (156845042275 : ℚ) / 54591837159555072

def SurrogateDiagonalTailChunk000Sub001Block096Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12246
    = surrogateDiagTailX0RatChunk000Sub001Block096Part013

theorem surrogateDiagonalTailChunk000Sub001Block096Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block096Part013CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block096Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block096Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block096Part013CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block096Part013SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block096Part013] using hcert

def TailChunk000Sub001Block096Part014SupportExplicit : Finset ℕ :=
  ([12247] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block096Part014 : ℚ :=
  (178569325643 : ℚ) / 996145132356633600

def SurrogateDiagonalTailChunk000Sub001Block096Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12247
    = surrogateDiagTailX0RatChunk000Sub001Block096Part014

theorem surrogateDiagonalTailChunk000Sub001Block096Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block096Part014CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block096Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block096Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block096Part014CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block096Part014SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block096Part014] using hcert

def TailChunk000Sub001Block096Part015SupportExplicit : Finset ℕ :=
  ([12251] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block096Part015 : ℚ :=
  (150087001 : ℚ) / 900930306281250

def SurrogateDiagonalTailChunk000Sub001Block096Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12251
    = surrogateDiagTailX0RatChunk000Sub001Block096Part015

theorem surrogateDiagonalTailChunk000Sub001Block096Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block096Part015CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block096Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block096Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block096Part015CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block096Part015SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block096Part015] using hcert

def TailChunk000Sub001Block096Part016SupportExplicit : Finset ℕ :=
  ([12253] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block096Part016 : ℚ :=
  (2345875140625 : ℚ) / 14086231453667902752

def SurrogateDiagonalTailChunk000Sub001Block096Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12253
    = surrogateDiagTailX0RatChunk000Sub001Block096Part016

theorem surrogateDiagonalTailChunk000Sub001Block096Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block096Part016CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block096Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block096Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block096Part016CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block096Part016SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block096Part016] using hcert

def TailChunk000Sub001Block096Part017SupportExplicit : Finset ℕ :=
  ([12254] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block096Part017 : ℚ :=
  (27869222421 : ℚ) / 31861393169766400

def SurrogateDiagonalTailChunk000Sub001Block096Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12254
    = surrogateDiagTailX0RatChunk000Sub001Block096Part017

theorem surrogateDiagonalTailChunk000Sub001Block096Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block096Part017CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block096Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block096Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block096Part017CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block096Part017SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block096Part017] using hcert

def TailChunk000Sub001Block096Part018SupportExplicit : Finset ℕ :=
  ([12255] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block096Part018 : ℚ :=
  (203404552325 : ℚ) / 238971413925199872

def SurrogateDiagonalTailChunk000Sub001Block096Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12255
    = surrogateDiagTailX0RatChunk000Sub001Block096Part018

theorem surrogateDiagonalTailChunk000Sub001Block096Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block096Part018CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block096Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block096Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block096Part018CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block096Part018SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block096Part018] using hcert

def TailChunk000Sub001Block096Part019SupportExplicit : Finset ℕ :=
  ([12257] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block096Part019 : ℚ :=
  (3260759690975 : ℚ) / 11494298794195943424

def SurrogateDiagonalTailChunk000Sub001Block096Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12257
    = surrogateDiagTailX0RatChunk000Sub001Block096Part019

theorem surrogateDiagonalTailChunk000Sub001Block096Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block096Part019CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block096Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block096Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block096Part019CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block096Part019SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block096Part019] using hcert

def TailChunk000Sub001Block096Part020SupportExplicit : Finset ℕ :=
  ([12259] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block096Part020 : ℚ :=
  (294591927139 : ℚ) / 1243777004155699200

def SurrogateDiagonalTailChunk000Sub001Block096Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12259
    = surrogateDiagTailX0RatChunk000Sub001Block096Part020

theorem surrogateDiagonalTailChunk000Sub001Block096Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block096Part020CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block096Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block096Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block096Part020CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block096Part020SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block096Part020] using hcert

def TailChunk000Sub001Block096Part021SupportExplicit : Finset ℕ :=
  ([12261] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block096Part021 : ℚ :=
  (2960356243 : ℚ) / 7287755883724800

def SurrogateDiagonalTailChunk000Sub001Block096Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12261
    = surrogateDiagTailX0RatChunk000Sub001Block096Part021

theorem surrogateDiagonalTailChunk000Sub001Block096Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block096Part021CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block096Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block096Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block096Part021CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block096Part021SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block096Part021] using hcert

def TailChunk000Sub001Block096Part022SupportExplicit : Finset ℕ :=
  ([12262] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block096Part022 : ℚ :=
  (939729025 : ℚ) / 1412305818292722

def SurrogateDiagonalTailChunk000Sub001Block096Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12262
    = surrogateDiagTailX0RatChunk000Sub001Block096Part022

theorem surrogateDiagonalTailChunk000Sub001Block096Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block096Part022CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block096Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block096Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block096Part022CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block096Part022SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block096Part022] using hcert

def TailChunk000Sub001Block096Part023SupportExplicit : Finset ℕ :=
  ([12263] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block096Part023 : ℚ :=
  (2349705765625 : ℚ) / 14132276136888577842

def SurrogateDiagonalTailChunk000Sub001Block096Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12263
    = surrogateDiagTailX0RatChunk000Sub001Block096Part023

theorem surrogateDiagonalTailChunk000Sub001Block096Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block096Part023CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block096Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block096Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block096Part023CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block096Part023SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block096Part023] using hcert

def TailChunk000Sub001Block096Part024SupportExplicit : Finset ℕ :=
  ([12265] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block096Part024 : ℚ :=
  (14531655307 : ℚ) / 41461733350932480

def SurrogateDiagonalTailChunk000Sub001Block096Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12265
    = surrogateDiagTailX0RatChunk000Sub001Block096Part024

theorem surrogateDiagonalTailChunk000Sub001Block096Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block096Part024CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block096Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block096Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block096Part024CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block096Part024SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block096Part024] using hcert

def surrogateDiagonalTailChunk000Sub001Block096HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block096Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block096Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block096Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block096Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block096Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block096Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block096Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block096Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block096Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block096Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block096Head : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block096Part000
    + surrogateDiagTailX0RatChunk000Sub001Block096Part001
    + surrogateDiagTailX0RatChunk000Sub001Block096Part002
    + surrogateDiagTailX0RatChunk000Sub001Block096Part003
    + surrogateDiagTailX0RatChunk000Sub001Block096Part004
    + surrogateDiagTailX0RatChunk000Sub001Block096Part005
    + surrogateDiagTailX0RatChunk000Sub001Block096Part006
    + surrogateDiagTailX0RatChunk000Sub001Block096Part007
    + surrogateDiagTailX0RatChunk000Sub001Block096Part008
    + surrogateDiagTailX0RatChunk000Sub001Block096Part009

def surrogateDiagonalTailChunk000Sub001Block096MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block096Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block096Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block096Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block096Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block096Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block096Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block096Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block096Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block096Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block096Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block096Mid : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block096Part010
    + surrogateDiagTailX0RatChunk000Sub001Block096Part011
    + surrogateDiagTailX0RatChunk000Sub001Block096Part012
    + surrogateDiagTailX0RatChunk000Sub001Block096Part013
    + surrogateDiagTailX0RatChunk000Sub001Block096Part014
    + surrogateDiagTailX0RatChunk000Sub001Block096Part015
    + surrogateDiagTailX0RatChunk000Sub001Block096Part016
    + surrogateDiagTailX0RatChunk000Sub001Block096Part017
    + surrogateDiagTailX0RatChunk000Sub001Block096Part018
    + surrogateDiagTailX0RatChunk000Sub001Block096Part019

def surrogateDiagonalTailChunk000Sub001Block096TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block096Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block096Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block096Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block096Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block096Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block096Tail : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block096Part020
    + surrogateDiagTailX0RatChunk000Sub001Block096Part021
    + surrogateDiagTailX0RatChunk000Sub001Block096Part022
    + surrogateDiagTailX0RatChunk000Sub001Block096Part023
    + surrogateDiagTailX0RatChunk000Sub001Block096Part024

def surrogateDiagonalTailChunk000Sub001Block096Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub001Block096HeadSum X0
    + surrogateDiagonalTailChunk000Sub001Block096MidSum X0
    + surrogateDiagonalTailChunk000Sub001Block096TailSum X0

def surrogateDiagTailX0RatChunk000Sub001Block096 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block096Part000
    + surrogateDiagTailX0RatChunk000Sub001Block096Part001
    + surrogateDiagTailX0RatChunk000Sub001Block096Part002
    + surrogateDiagTailX0RatChunk000Sub001Block096Part003
    + surrogateDiagTailX0RatChunk000Sub001Block096Part004
    + surrogateDiagTailX0RatChunk000Sub001Block096Part005
    + surrogateDiagTailX0RatChunk000Sub001Block096Part006
    + surrogateDiagTailX0RatChunk000Sub001Block096Part007
    + surrogateDiagTailX0RatChunk000Sub001Block096Part008
    + surrogateDiagTailX0RatChunk000Sub001Block096Part009
    + surrogateDiagTailX0RatChunk000Sub001Block096Part010
    + surrogateDiagTailX0RatChunk000Sub001Block096Part011
    + surrogateDiagTailX0RatChunk000Sub001Block096Part012
    + surrogateDiagTailX0RatChunk000Sub001Block096Part013
    + surrogateDiagTailX0RatChunk000Sub001Block096Part014
    + surrogateDiagTailX0RatChunk000Sub001Block096Part015
    + surrogateDiagTailX0RatChunk000Sub001Block096Part016
    + surrogateDiagTailX0RatChunk000Sub001Block096Part017
    + surrogateDiagTailX0RatChunk000Sub001Block096Part018
    + surrogateDiagTailX0RatChunk000Sub001Block096Part019
    + surrogateDiagTailX0RatChunk000Sub001Block096Part020
    + surrogateDiagTailX0RatChunk000Sub001Block096Part021
    + surrogateDiagTailX0RatChunk000Sub001Block096Part022
    + surrogateDiagTailX0RatChunk000Sub001Block096Part023
    + surrogateDiagTailX0RatChunk000Sub001Block096Part024

theorem surrogateDiagTailX0RatChunk000Sub001Block096_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk000Sub001Block096Head + surrogateDiagTailX0RatChunk000Sub001Block096Mid + surrogateDiagTailX0RatChunk000Sub001Block096Tail =
      surrogateDiagTailX0RatChunk000Sub001Block096 := by
  unfold surrogateDiagTailX0RatChunk000Sub001Block096Head surrogateDiagTailX0RatChunk000Sub001Block096Mid surrogateDiagTailX0RatChunk000Sub001Block096Tail surrogateDiagTailX0RatChunk000Sub001Block096
  ring

def SurrogateDiagonalTailChunk000Sub001Block096HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block096HeadSum X0 = surrogateDiagTailX0RatChunk000Sub001Block096Head

def SurrogateDiagonalTailChunk000Sub001Block096MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block096MidSum X0 = surrogateDiagTailX0RatChunk000Sub001Block096Mid

def SurrogateDiagonalTailChunk000Sub001Block096TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block096TailSum X0 = surrogateDiagTailX0RatChunk000Sub001Block096Tail

theorem surrogateDiagonalTailChunk000Sub001Block096_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk000Sub001Block096HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk000Sub001Block096MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk000Sub001Block096TailCertificateAt X0) :
    surrogateDiagonalTailChunk000Sub001Block096Sum X0 = surrogateDiagTailX0RatChunk000Sub001Block096 := by
  unfold SurrogateDiagonalTailChunk000Sub001Block096HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk000Sub001Block096MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk000Sub001Block096TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk000Sub001Block096Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk000Sub001Block096_eq_head_add_mid_add_tail

/-- Block 097 covers tail-support indices [7425,7450) and q from 12266 to 12307. -/

def TailChunk000Sub001Block097Part000SupportExplicit : Finset ℕ :=
  ([12266] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block097Part000 : ℚ :=
  (587713890625 : ℚ) / 883843662653213472

def SurrogateDiagonalTailChunk000Sub001Block097Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12266
    = surrogateDiagTailX0RatChunk000Sub001Block097Part000

theorem surrogateDiagonalTailChunk000Sub001Block097Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block097Part000CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block097Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block097Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block097Part000CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block097Part000SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block097Part000] using hcert

def TailChunk000Sub001Block097Part001SupportExplicit : Finset ℕ :=
  ([12269] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block097Part001 : ℚ :=
  (2352005640625 : ℚ) / 14159957074269187872

def SurrogateDiagonalTailChunk000Sub001Block097Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12269
    = surrogateDiagTailX0RatChunk000Sub001Block097Part001

theorem surrogateDiagonalTailChunk000Sub001Block097Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block097Part001CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block097Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block097Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block097Part001CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block097Part001SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block097Part001] using hcert

def TailChunk000Sub001Block097Part002SupportExplicit : Finset ℕ :=
  ([12270] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block097Part002 : ℚ :=
  (38246061025 : ℚ) / 10511475806306304

def SurrogateDiagonalTailChunk000Sub001Block097Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12270
    = surrogateDiagTailX0RatChunk000Sub001Block097Part002

theorem surrogateDiagonalTailChunk000Sub001Block097Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block097Part002CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block097Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block097Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block097Part002CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block097Part002SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block097Part002] using hcert

def TailChunk000Sub001Block097Part003SupportExplicit : Finset ℕ :=
  ([12271] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block097Part003 : ℚ :=
  (1823196830875 : ℚ) / 7633228733351534592

def SurrogateDiagonalTailChunk000Sub001Block097Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12271
    = surrogateDiagTailX0RatChunk000Sub001Block097Part003

theorem surrogateDiagonalTailChunk000Sub001Block097Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block097Part003CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block097Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block097Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block097Part003CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block097Part003SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block097Part003] using hcert

def TailChunk000Sub001Block097Part004SupportExplicit : Finset ℕ :=
  ([12273] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block097Part004 : ℚ :=
  (167305983637 : ℚ) / 447816472761475200

def SurrogateDiagonalTailChunk000Sub001Block097Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12273
    = surrogateDiagTailX0RatChunk000Sub001Block097Part004

theorem surrogateDiagonalTailChunk000Sub001Block097Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block097Part004CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block097Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block097Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block097Part004CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block097Part004SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block097Part004] using hcert

def TailChunk000Sub001Block097Part005SupportExplicit : Finset ℕ :=
  ([12277] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block097Part005 : ℚ :=
  (2355073890625 : ℚ) / 14196928221900163872

def SurrogateDiagonalTailChunk000Sub001Block097Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12277
    = surrogateDiagTailX0RatChunk000Sub001Block097Part005

theorem surrogateDiagonalTailChunk000Sub001Block097Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block097Part005CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block097Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block097Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block097Part005CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block097Part005SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block097Part005] using hcert

def TailChunk000Sub001Block097Part006SupportExplicit : Finset ℕ :=
  ([12278] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block097Part006 : ℚ :=
  (1920657411775 : ℚ) / 1908307183337883648

def SurrogateDiagonalTailChunk000Sub001Block097Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12278
    = surrogateDiagTailX0RatChunk000Sub001Block097Part006

theorem surrogateDiagonalTailChunk000Sub001Block097Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block097Part006CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block097Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block097Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block097Part006CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block097Part006SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block097Part006] using hcert

def TailChunk000Sub001Block097Part007SupportExplicit : Finset ℕ :=
  ([12279] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block097Part007 : ℚ :=
  (380612780975 : ℚ) / 1019756909317183488

def SurrogateDiagonalTailChunk000Sub001Block097Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12279
    = surrogateDiagTailX0RatChunk000Sub001Block097Part007

theorem surrogateDiagonalTailChunk000Sub001Block097Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block097Part007CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block097Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block097Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block097Part007CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block097Part007SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block097Part007] using hcert

def TailChunk000Sub001Block097Part008SupportExplicit : Finset ℕ :=
  ([12281] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block097Part008 : ℚ :=
  (3770574025 : ℚ) / 22744705474048512

def SurrogateDiagonalTailChunk000Sub001Block097Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12281
    = surrogateDiagTailX0RatChunk000Sub001Block097Part008

theorem surrogateDiagonalTailChunk000Sub001Block097Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block097Part008CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block097Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block097Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block097Part008CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block097Part008SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block097Part008] using hcert

def TailChunk000Sub001Block097Part009SupportExplicit : Finset ℕ :=
  ([12282] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block097Part009 : ℚ :=
  (25786837575 : ℚ) / 11709194391617536

def SurrogateDiagonalTailChunk000Sub001Block097Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12282
    = surrogateDiagTailX0RatChunk000Sub001Block097Part009

theorem surrogateDiagonalTailChunk000Sub001Block097Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block097Part009CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block097Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block097Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block097Part009CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block097Part009SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block097Part009] using hcert

def TailChunk000Sub001Block097Part010SupportExplicit : Finset ℕ :=
  ([12283] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block097Part010 : ℚ :=
  (52196975839 : ℚ) / 300258117823641600

def SurrogateDiagonalTailChunk000Sub001Block097Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12283
    = surrogateDiagTailX0RatChunk000Sub001Block097Part010

theorem surrogateDiagonalTailChunk000Sub001Block097Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block097Part010CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block097Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block097Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block097Part010CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block097Part010SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block097Part010] using hcert

def TailChunk000Sub001Block097Part011SupportExplicit : Finset ℕ :=
  ([12286] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block097Part011 : ℚ :=
  (589632015625 : ℚ) / 889623232505497362

def SurrogateDiagonalTailChunk000Sub001Block097Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12286
    = surrogateDiagTailX0RatChunk000Sub001Block097Part011

theorem surrogateDiagonalTailChunk000Sub001Block097Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block097Part011CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block097Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block097Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block097Part011CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block097Part011SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block097Part011] using hcert

def TailChunk000Sub001Block097Part012SupportExplicit : Finset ℕ :=
  ([12287] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block097Part012 : ℚ :=
  (323985772081 : ℚ) / 1551470880065587200

def SurrogateDiagonalTailChunk000Sub001Block097Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12287
    = surrogateDiagTailX0RatChunk000Sub001Block097Part012

theorem surrogateDiagonalTailChunk000Sub001Block097Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block097Part012CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block097Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block097Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block097Part012CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block097Part012SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block097Part012] using hcert

def TailChunk000Sub001Block097Part013SupportExplicit : Finset ℕ :=
  ([12289] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block097Part013 : ℚ :=
  (2359680015625 : ℚ) / 14252520630116155392

def SurrogateDiagonalTailChunk000Sub001Block097Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12289
    = surrogateDiagTailX0RatChunk000Sub001Block097Part013

theorem surrogateDiagonalTailChunk000Sub001Block097Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block097Part013CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block097Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block097Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block097Part013CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block097Part013SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block097Part013] using hcert

def TailChunk000Sub001Block097Part014SupportExplicit : Finset ℕ :=
  ([12290] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block097Part014 : ℚ :=
  (896160225425 : ℚ) / 727830575169552384

def SurrogateDiagonalTailChunk000Sub001Block097Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12290
    = surrogateDiagTailX0RatChunk000Sub001Block097Part014

theorem surrogateDiagonalTailChunk000Sub001Block097Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block097Part014CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block097Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block097Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block097Part014CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block097Part014SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block097Part014] using hcert

def TailChunk000Sub001Block097Part015SupportExplicit : Finset ℕ :=
  ([12291] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block097Part015 : ℚ :=
  (76661147111 : ℚ) / 173980964723097600

def SurrogateDiagonalTailChunk000Sub001Block097Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12291
    = surrogateDiagTailX0RatChunk000Sub001Block097Part015

theorem surrogateDiagonalTailChunk000Sub001Block097Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block097Part015CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block097Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block097Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block097Part015CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block097Part015SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block097Part015] using hcert

def TailChunk000Sub001Block097Part016SupportExplicit : Finset ℕ :=
  ([12293] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block097Part016 : ℚ :=
  (8639919844675 : ℚ) / 45713760777539353728

def SurrogateDiagonalTailChunk000Sub001Block097Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12293
    = surrogateDiagTailX0RatChunk000Sub001Block097Part016

theorem surrogateDiagonalTailChunk000Sub001Block097Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block097Part016CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block097Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block097Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block097Part016CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block097Part016SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block097Part016] using hcert

def TailChunk000Sub001Block097Part017SupportExplicit : Finset ℕ :=
  ([12295] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block097Part017 : ℚ :=
  (6421228798225 : ℚ) / 23366536201051097088

def SurrogateDiagonalTailChunk000Sub001Block097Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12295
    = surrogateDiagTailX0RatChunk000Sub001Block097Part017

theorem surrogateDiagonalTailChunk000Sub001Block097Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block097Part017CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block097Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block097Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block097Part017CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block097Part017SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block097Part017] using hcert

def TailChunk000Sub001Block097Part018SupportExplicit : Finset ℕ :=
  ([12297] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block097Part018 : ℚ :=
  (328091610325 : ℚ) / 705203850839694408

def SurrogateDiagonalTailChunk000Sub001Block097Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12297
    = surrogateDiagTailX0RatChunk000Sub001Block097Part018

theorem surrogateDiagonalTailChunk000Sub001Block097Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block097Part018CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block097Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block097Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block097Part018CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block097Part018SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block097Part018] using hcert

def TailChunk000Sub001Block097Part019SupportExplicit : Finset ℕ :=
  ([12298] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block097Part019 : ℚ :=
  (1861597501 : ℚ) / 1613425827041280

def SurrogateDiagonalTailChunk000Sub001Block097Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12298
    = surrogateDiagTailX0RatChunk000Sub001Block097Part019

theorem surrogateDiagonalTailChunk000Sub001Block097Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block097Part019CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block097Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block097Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block097Part019CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block097Part019SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block097Part019] using hcert

def TailChunk000Sub001Block097Part020SupportExplicit : Finset ℕ :=
  ([12301] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block097Part020 : ℚ :=
  (151314601 : ℚ) / 915729673312800

def SurrogateDiagonalTailChunk000Sub001Block097Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12301
    = surrogateDiagTailX0RatChunk000Sub001Block097Part020

theorem surrogateDiagonalTailChunk000Sub001Block097Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block097Part020CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block097Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block097Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block097Part020CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block097Part020SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block097Part020] using hcert

def TailChunk000Sub001Block097Part021SupportExplicit : Finset ℕ :=
  ([12302] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block097Part021 : ℚ :=
  (37834801 : ℚ) / 57233104582050

def SurrogateDiagonalTailChunk000Sub001Block097Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12302
    = surrogateDiagTailX0RatChunk000Sub001Block097Part021

theorem surrogateDiagonalTailChunk000Sub001Block097Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block097Part021CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block097Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block097Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block097Part021CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block097Part021SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block097Part021] using hcert

def TailChunk000Sub001Block097Part022SupportExplicit : Finset ℕ :=
  ([12305] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block097Part022 : ℚ :=
  (5921660224225 : ℚ) / 18931324883347734528

def SurrogateDiagonalTailChunk000Sub001Block097Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12305
    = surrogateDiagTailX0RatChunk000Sub001Block097Part022

theorem surrogateDiagonalTailChunk000Sub001Block097Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block097Part022CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block097Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block097Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block097Part022CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block097Part022SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block097Part022] using hcert

def TailChunk000Sub001Block097Part023SupportExplicit : Finset ℕ :=
  ([12306] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block097Part023 : ℚ :=
  (327399839275 : ℚ) / 94237391769772032

def SurrogateDiagonalTailChunk000Sub001Block097Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12306
    = surrogateDiagTailX0RatChunk000Sub001Block097Part023

theorem surrogateDiagonalTailChunk000Sub001Block097Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block097Part023CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block097Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block097Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block097Part023CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block097Part023SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block097Part023] using hcert

def TailChunk000Sub001Block097Part024SupportExplicit : Finset ℕ :=
  ([12307] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block097Part024 : ℚ :=
  (178979264171 : ℚ) / 996145132356633600

def SurrogateDiagonalTailChunk000Sub001Block097Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12307
    = surrogateDiagTailX0RatChunk000Sub001Block097Part024

theorem surrogateDiagonalTailChunk000Sub001Block097Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block097Part024CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block097Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block097Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block097Part024CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block097Part024SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block097Part024] using hcert

def surrogateDiagonalTailChunk000Sub001Block097HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block097Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block097Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block097Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block097Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block097Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block097Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block097Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block097Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block097Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block097Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block097Head : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block097Part000
    + surrogateDiagTailX0RatChunk000Sub001Block097Part001
    + surrogateDiagTailX0RatChunk000Sub001Block097Part002
    + surrogateDiagTailX0RatChunk000Sub001Block097Part003
    + surrogateDiagTailX0RatChunk000Sub001Block097Part004
    + surrogateDiagTailX0RatChunk000Sub001Block097Part005
    + surrogateDiagTailX0RatChunk000Sub001Block097Part006
    + surrogateDiagTailX0RatChunk000Sub001Block097Part007
    + surrogateDiagTailX0RatChunk000Sub001Block097Part008
    + surrogateDiagTailX0RatChunk000Sub001Block097Part009

def surrogateDiagonalTailChunk000Sub001Block097MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block097Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block097Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block097Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block097Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block097Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block097Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block097Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block097Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block097Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block097Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block097Mid : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block097Part010
    + surrogateDiagTailX0RatChunk000Sub001Block097Part011
    + surrogateDiagTailX0RatChunk000Sub001Block097Part012
    + surrogateDiagTailX0RatChunk000Sub001Block097Part013
    + surrogateDiagTailX0RatChunk000Sub001Block097Part014
    + surrogateDiagTailX0RatChunk000Sub001Block097Part015
    + surrogateDiagTailX0RatChunk000Sub001Block097Part016
    + surrogateDiagTailX0RatChunk000Sub001Block097Part017
    + surrogateDiagTailX0RatChunk000Sub001Block097Part018
    + surrogateDiagTailX0RatChunk000Sub001Block097Part019

def surrogateDiagonalTailChunk000Sub001Block097TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block097Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block097Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block097Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block097Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block097Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block097Tail : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block097Part020
    + surrogateDiagTailX0RatChunk000Sub001Block097Part021
    + surrogateDiagTailX0RatChunk000Sub001Block097Part022
    + surrogateDiagTailX0RatChunk000Sub001Block097Part023
    + surrogateDiagTailX0RatChunk000Sub001Block097Part024

def surrogateDiagonalTailChunk000Sub001Block097Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub001Block097HeadSum X0
    + surrogateDiagonalTailChunk000Sub001Block097MidSum X0
    + surrogateDiagonalTailChunk000Sub001Block097TailSum X0

def surrogateDiagTailX0RatChunk000Sub001Block097 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block097Part000
    + surrogateDiagTailX0RatChunk000Sub001Block097Part001
    + surrogateDiagTailX0RatChunk000Sub001Block097Part002
    + surrogateDiagTailX0RatChunk000Sub001Block097Part003
    + surrogateDiagTailX0RatChunk000Sub001Block097Part004
    + surrogateDiagTailX0RatChunk000Sub001Block097Part005
    + surrogateDiagTailX0RatChunk000Sub001Block097Part006
    + surrogateDiagTailX0RatChunk000Sub001Block097Part007
    + surrogateDiagTailX0RatChunk000Sub001Block097Part008
    + surrogateDiagTailX0RatChunk000Sub001Block097Part009
    + surrogateDiagTailX0RatChunk000Sub001Block097Part010
    + surrogateDiagTailX0RatChunk000Sub001Block097Part011
    + surrogateDiagTailX0RatChunk000Sub001Block097Part012
    + surrogateDiagTailX0RatChunk000Sub001Block097Part013
    + surrogateDiagTailX0RatChunk000Sub001Block097Part014
    + surrogateDiagTailX0RatChunk000Sub001Block097Part015
    + surrogateDiagTailX0RatChunk000Sub001Block097Part016
    + surrogateDiagTailX0RatChunk000Sub001Block097Part017
    + surrogateDiagTailX0RatChunk000Sub001Block097Part018
    + surrogateDiagTailX0RatChunk000Sub001Block097Part019
    + surrogateDiagTailX0RatChunk000Sub001Block097Part020
    + surrogateDiagTailX0RatChunk000Sub001Block097Part021
    + surrogateDiagTailX0RatChunk000Sub001Block097Part022
    + surrogateDiagTailX0RatChunk000Sub001Block097Part023
    + surrogateDiagTailX0RatChunk000Sub001Block097Part024

theorem surrogateDiagTailX0RatChunk000Sub001Block097_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk000Sub001Block097Head + surrogateDiagTailX0RatChunk000Sub001Block097Mid + surrogateDiagTailX0RatChunk000Sub001Block097Tail =
      surrogateDiagTailX0RatChunk000Sub001Block097 := by
  unfold surrogateDiagTailX0RatChunk000Sub001Block097Head surrogateDiagTailX0RatChunk000Sub001Block097Mid surrogateDiagTailX0RatChunk000Sub001Block097Tail surrogateDiagTailX0RatChunk000Sub001Block097
  ring

def SurrogateDiagonalTailChunk000Sub001Block097HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block097HeadSum X0 = surrogateDiagTailX0RatChunk000Sub001Block097Head

def SurrogateDiagonalTailChunk000Sub001Block097MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block097MidSum X0 = surrogateDiagTailX0RatChunk000Sub001Block097Mid

def SurrogateDiagonalTailChunk000Sub001Block097TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block097TailSum X0 = surrogateDiagTailX0RatChunk000Sub001Block097Tail

theorem surrogateDiagonalTailChunk000Sub001Block097_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk000Sub001Block097HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk000Sub001Block097MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk000Sub001Block097TailCertificateAt X0) :
    surrogateDiagonalTailChunk000Sub001Block097Sum X0 = surrogateDiagTailX0RatChunk000Sub001Block097 := by
  unfold SurrogateDiagonalTailChunk000Sub001Block097HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk000Sub001Block097MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk000Sub001Block097TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk000Sub001Block097Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk000Sub001Block097_eq_head_add_mid_add_tail

/-- Block 098 covers tail-support indices [7450,7475) and q from 12309 to 12349. -/

def TailChunk000Sub001Block098Part000SupportExplicit : Finset ℕ :=
  ([12309] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block098Part000 : ℚ :=
  (11326055587 : ℚ) / 19153961482291200

def SurrogateDiagonalTailChunk000Sub001Block098Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12309
    = surrogateDiagTailX0RatChunk000Sub001Block098Part000

theorem surrogateDiagonalTailChunk000Sub001Block098Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block098Part000CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block098Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block098Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block098Part000CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block098Part000SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block098Part000] using hcert

def TailChunk000Sub001Block098Part001SupportExplicit : Finset ℕ :=
  ([12310] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block098Part001 : ℚ :=
  (5993864357 : ℚ) / 4883891591001600

def SurrogateDiagonalTailChunk000Sub001Block098Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12310
    = surrogateDiagTailX0RatChunk000Sub001Block098Part001

theorem surrogateDiagonalTailChunk000Sub001Block098Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block098Part001CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block098Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block098Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block098Part001CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block098Part001SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block098Part001] using hcert

def TailChunk000Sub001Block098Part002SupportExplicit : Finset ℕ :=
  ([12311] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block098Part002 : ℚ :=
  (8338768334575 : ℚ) / 41525645171723716608

def SurrogateDiagonalTailChunk000Sub001Block098Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12311
    = surrogateDiagTailX0RatChunk000Sub001Block098Part002

theorem surrogateDiagonalTailChunk000Sub001Block098Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block098Part002CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block098Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block098Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block098Part002CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block098Part002SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block098Part002] using hcert

def TailChunk000Sub001Block098Part003SupportExplicit : Finset ℕ :=
  ([12313] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block098Part003 : ℚ :=
  (458925663175 : ℚ) / 1934582971440882888

def SurrogateDiagonalTailChunk000Sub001Block098Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12313
    = surrogateDiagTailX0RatChunk000Sub001Block098Part003

theorem surrogateDiagonalTailChunk000Sub001Block098Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block098Part003CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block098Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block098Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block098Part003CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block098Part003SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block098Part003] using hcert

def TailChunk000Sub001Block098Part004SupportExplicit : Finset ℕ :=
  ([12314] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block098Part004 : ℚ :=
  (91549433767 : ℚ) / 127906196940163200

def SurrogateDiagonalTailChunk000Sub001Block098Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12314
    = surrogateDiagTailX0RatChunk000Sub001Block098Part004

theorem surrogateDiagonalTailChunk000Sub001Block098Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block098Part004CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block098Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block098Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block098Part004CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block098Part004SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block098Part004] using hcert

def TailChunk000Sub001Block098Part005SupportExplicit : Finset ℕ :=
  ([12315] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block098Part005 : ℚ :=
  (29273518049 : ℚ) / 37045222142115840

def SurrogateDiagonalTailChunk000Sub001Block098Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12315
    = surrogateDiagTailX0RatChunk000Sub001Block098Part005

theorem surrogateDiagonalTailChunk000Sub001Block098Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block098Part005CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block098Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block098Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block098Part005CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block098Part005SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block098Part005] using hcert

def TailChunk000Sub001Block098Part006SupportExplicit : Finset ℕ :=
  ([12317] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block098Part006 : ℚ :=
  (9213374949775 : ℚ) / 53529596719244771328

def SurrogateDiagonalTailChunk000Sub001Block098Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12317
    = surrogateDiagTailX0RatChunk000Sub001Block098Part006

theorem surrogateDiagonalTailChunk000Sub001Block098Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block098Part006CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block098Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block098Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block098Part006CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block098Part006SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block098Part006] using hcert

def TailChunk000Sub001Block098Part007SupportExplicit : Finset ℕ :=
  ([12318] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block098Part007 : ℚ :=
  (263428826075 : ℚ) / 354671483625022464

def SurrogateDiagonalTailChunk000Sub001Block098Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12318
    = surrogateDiagTailX0RatChunk000Sub001Block098Part007

theorem surrogateDiagonalTailChunk000Sub001Block098Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block098Part007CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block098Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block098Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block098Part007CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block098Part007SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block098Part007] using hcert

def TailChunk000Sub001Block098Part008SupportExplicit : Finset ℕ :=
  ([12319] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block098Part008 : ℚ :=
  (68658416125 : ℚ) / 53529596719244771328

def SurrogateDiagonalTailChunk000Sub001Block098Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12319
    = surrogateDiagTailX0RatChunk000Sub001Block098Part008

theorem surrogateDiagonalTailChunk000Sub001Block098Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block098Part008CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block098Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block098Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block098Part008CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block098Part008SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block098Part008] using hcert

def TailChunk000Sub001Block098Part009SupportExplicit : Finset ℕ :=
  ([12322] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block098Part009 : ℚ :=
  (993908117 : ℚ) / 64812960000000000

def SurrogateDiagonalTailChunk000Sub001Block098Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12322
    = surrogateDiagTailX0RatChunk000Sub001Block098Part009

theorem surrogateDiagonalTailChunk000Sub001Block098Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block098Part009CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block098Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block098Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block098Part009CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block098Part009SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block098Part009] using hcert

def TailChunk000Sub001Block098Part010SupportExplicit : Finset ℕ :=
  ([12323] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block098Part010 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block098Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12323
    = surrogateDiagTailX0RatChunk000Sub001Block098Part010

theorem surrogateDiagonalTailChunk000Sub001Block098Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block098Part010CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block098Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block098Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block098Part010CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block098Part010SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block098Part010] using hcert

def TailChunk000Sub001Block098Part011SupportExplicit : Finset ℕ :=
  ([12326] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block098Part011 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block098Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12326
    = surrogateDiagTailX0RatChunk000Sub001Block098Part011

theorem surrogateDiagonalTailChunk000Sub001Block098Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block098Part011CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block098Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block098Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block098Part011CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block098Part011SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block098Part011] using hcert

def TailChunk000Sub001Block098Part012SupportExplicit : Finset ℕ :=
  ([12327] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block098Part012 : ℚ :=
  (570631006475 : ℚ) / 3057118769684358144

def SurrogateDiagonalTailChunk000Sub001Block098Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12327
    = surrogateDiagTailX0RatChunk000Sub001Block098Part012

theorem surrogateDiagonalTailChunk000Sub001Block098Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block098Part012CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block098Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block098Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block098Part012CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block098Part012SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block098Part012] using hcert

def TailChunk000Sub001Block098Part013SupportExplicit : Finset ℕ :=
  ([12329] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block098Part013 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block098Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12329
    = surrogateDiagTailX0RatChunk000Sub001Block098Part013

theorem surrogateDiagonalTailChunk000Sub001Block098Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block098Part013CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block098Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block098Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block098Part013CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block098Part013SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block098Part013] using hcert

def TailChunk000Sub001Block098Part014SupportExplicit : Finset ℕ :=
  ([12331] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block098Part014 : ℚ :=
  (20485140907 : ℚ) / 1188198076192819200

def SurrogateDiagonalTailChunk000Sub001Block098Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12331
    = surrogateDiagTailX0RatChunk000Sub001Block098Part014

theorem surrogateDiagonalTailChunk000Sub001Block098Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block098Part014CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block098Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block098Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block098Part014CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block098Part014SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block098Part014] using hcert

def TailChunk000Sub001Block098Part015SupportExplicit : Finset ℕ :=
  ([12333] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block098Part015 : ℚ :=
  (4225525339 : ℚ) / 45664017762957120

def SurrogateDiagonalTailChunk000Sub001Block098Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12333
    = surrogateDiagTailX0RatChunk000Sub001Block098Part015

theorem surrogateDiagonalTailChunk000Sub001Block098Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block098Part015CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block098Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block098Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block098Part015CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block098Part015SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block098Part015] using hcert

def TailChunk000Sub001Block098Part016SupportExplicit : Finset ℕ :=
  ([12334] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block098Part016 : ℚ :=
  (81106567 : ℚ) / 539833769164800

def SurrogateDiagonalTailChunk000Sub001Block098Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12334
    = surrogateDiagTailX0RatChunk000Sub001Block098Part016

theorem surrogateDiagonalTailChunk000Sub001Block098Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block098Part016CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block098Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block098Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block098Part016CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block098Part016SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block098Part016] using hcert

def TailChunk000Sub001Block098Part017SupportExplicit : Finset ℕ :=
  ([12335] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block098Part017 : ℚ :=
  (253747618675 : ℚ) / 7890742269438990336

def SurrogateDiagonalTailChunk000Sub001Block098Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12335
    = surrogateDiagTailX0RatChunk000Sub001Block098Part017

theorem surrogateDiagonalTailChunk000Sub001Block098Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block098Part017CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block098Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block098Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block098Part017CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block098Part017SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block098Part017] using hcert

def TailChunk000Sub001Block098Part018SupportExplicit : Finset ℕ :=
  ([12338] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block098Part018 : ℚ :=
  (62506151 : ℚ) / 2767069812101760

def SurrogateDiagonalTailChunk000Sub001Block098Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12338
    = surrogateDiagTailX0RatChunk000Sub001Block098Part018

theorem surrogateDiagonalTailChunk000Sub001Block098Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block098Part018CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block098Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block098Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block098Part018CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block098Part018SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block098Part018] using hcert

def TailChunk000Sub001Block098Part019SupportExplicit : Finset ℕ :=
  ([12341] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block098Part019 : ℚ :=
  (2706098251 : ℚ) / 103259252930641920

def SurrogateDiagonalTailChunk000Sub001Block098Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12341
    = surrogateDiagTailX0RatChunk000Sub001Block098Part019

theorem surrogateDiagonalTailChunk000Sub001Block098Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block098Part019CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block098Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block098Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block098Part019CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block098Part019SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block098Part019] using hcert

def TailChunk000Sub001Block098Part020SupportExplicit : Finset ℕ :=
  ([12343] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block098Part020 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block098Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12343
    = surrogateDiagTailX0RatChunk000Sub001Block098Part020

theorem surrogateDiagonalTailChunk000Sub001Block098Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block098Part020CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block098Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block098Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block098Part020CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block098Part020SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block098Part020] using hcert

def TailChunk000Sub001Block098Part021SupportExplicit : Finset ℕ :=
  ([12345] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block098Part021 : ℚ :=
  (1142733092725 : ℚ) / 4675995418926809088

def SurrogateDiagonalTailChunk000Sub001Block098Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12345
    = surrogateDiagTailX0RatChunk000Sub001Block098Part021

theorem surrogateDiagonalTailChunk000Sub001Block098Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block098Part021CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block098Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block098Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block098Part021CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block098Part021SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block098Part021] using hcert

def TailChunk000Sub001Block098Part022SupportExplicit : Finset ℕ :=
  ([12346] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block098Part022 : ℚ :=
  (595405140625 : ℚ) / 907132103870905632

def SurrogateDiagonalTailChunk000Sub001Block098Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12346
    = surrogateDiagTailX0RatChunk000Sub001Block098Part022

theorem surrogateDiagonalTailChunk000Sub001Block098Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block098Part022CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block098Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block098Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block098Part022CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block098Part022SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block098Part022] using hcert

def TailChunk000Sub001Block098Part023SupportExplicit : Finset ℕ :=
  ([12347] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block098Part023 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block098Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12347
    = surrogateDiagTailX0RatChunk000Sub001Block098Part023

theorem surrogateDiagonalTailChunk000Sub001Block098Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block098Part023CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block098Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block098Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block098Part023CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block098Part023SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block098Part023] using hcert

def TailChunk000Sub001Block098Part024SupportExplicit : Finset ℕ :=
  ([12349] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block098Part024 : ℚ :=
  (15008917275 : ℚ) / 8827564969832480768

def SurrogateDiagonalTailChunk000Sub001Block098Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12349
    = surrogateDiagTailX0RatChunk000Sub001Block098Part024

theorem surrogateDiagonalTailChunk000Sub001Block098Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block098Part024CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block098Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block098Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block098Part024CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block098Part024SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block098Part024] using hcert

def surrogateDiagonalTailChunk000Sub001Block098HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block098Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block098Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block098Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block098Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block098Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block098Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block098Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block098Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block098Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block098Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block098Head : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block098Part000
    + surrogateDiagTailX0RatChunk000Sub001Block098Part001
    + surrogateDiagTailX0RatChunk000Sub001Block098Part002
    + surrogateDiagTailX0RatChunk000Sub001Block098Part003
    + surrogateDiagTailX0RatChunk000Sub001Block098Part004
    + surrogateDiagTailX0RatChunk000Sub001Block098Part005
    + surrogateDiagTailX0RatChunk000Sub001Block098Part006
    + surrogateDiagTailX0RatChunk000Sub001Block098Part007
    + surrogateDiagTailX0RatChunk000Sub001Block098Part008
    + surrogateDiagTailX0RatChunk000Sub001Block098Part009

def surrogateDiagonalTailChunk000Sub001Block098MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block098Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block098Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block098Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block098Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block098Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block098Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block098Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block098Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block098Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block098Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block098Mid : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block098Part010
    + surrogateDiagTailX0RatChunk000Sub001Block098Part011
    + surrogateDiagTailX0RatChunk000Sub001Block098Part012
    + surrogateDiagTailX0RatChunk000Sub001Block098Part013
    + surrogateDiagTailX0RatChunk000Sub001Block098Part014
    + surrogateDiagTailX0RatChunk000Sub001Block098Part015
    + surrogateDiagTailX0RatChunk000Sub001Block098Part016
    + surrogateDiagTailX0RatChunk000Sub001Block098Part017
    + surrogateDiagTailX0RatChunk000Sub001Block098Part018
    + surrogateDiagTailX0RatChunk000Sub001Block098Part019

def surrogateDiagonalTailChunk000Sub001Block098TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block098Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block098Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block098Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block098Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block098Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block098Tail : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block098Part020
    + surrogateDiagTailX0RatChunk000Sub001Block098Part021
    + surrogateDiagTailX0RatChunk000Sub001Block098Part022
    + surrogateDiagTailX0RatChunk000Sub001Block098Part023
    + surrogateDiagTailX0RatChunk000Sub001Block098Part024

def surrogateDiagonalTailChunk000Sub001Block098Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub001Block098HeadSum X0
    + surrogateDiagonalTailChunk000Sub001Block098MidSum X0
    + surrogateDiagonalTailChunk000Sub001Block098TailSum X0

def surrogateDiagTailX0RatChunk000Sub001Block098 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block098Part000
    + surrogateDiagTailX0RatChunk000Sub001Block098Part001
    + surrogateDiagTailX0RatChunk000Sub001Block098Part002
    + surrogateDiagTailX0RatChunk000Sub001Block098Part003
    + surrogateDiagTailX0RatChunk000Sub001Block098Part004
    + surrogateDiagTailX0RatChunk000Sub001Block098Part005
    + surrogateDiagTailX0RatChunk000Sub001Block098Part006
    + surrogateDiagTailX0RatChunk000Sub001Block098Part007
    + surrogateDiagTailX0RatChunk000Sub001Block098Part008
    + surrogateDiagTailX0RatChunk000Sub001Block098Part009
    + surrogateDiagTailX0RatChunk000Sub001Block098Part010
    + surrogateDiagTailX0RatChunk000Sub001Block098Part011
    + surrogateDiagTailX0RatChunk000Sub001Block098Part012
    + surrogateDiagTailX0RatChunk000Sub001Block098Part013
    + surrogateDiagTailX0RatChunk000Sub001Block098Part014
    + surrogateDiagTailX0RatChunk000Sub001Block098Part015
    + surrogateDiagTailX0RatChunk000Sub001Block098Part016
    + surrogateDiagTailX0RatChunk000Sub001Block098Part017
    + surrogateDiagTailX0RatChunk000Sub001Block098Part018
    + surrogateDiagTailX0RatChunk000Sub001Block098Part019
    + surrogateDiagTailX0RatChunk000Sub001Block098Part020
    + surrogateDiagTailX0RatChunk000Sub001Block098Part021
    + surrogateDiagTailX0RatChunk000Sub001Block098Part022
    + surrogateDiagTailX0RatChunk000Sub001Block098Part023
    + surrogateDiagTailX0RatChunk000Sub001Block098Part024

theorem surrogateDiagTailX0RatChunk000Sub001Block098_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk000Sub001Block098Head + surrogateDiagTailX0RatChunk000Sub001Block098Mid + surrogateDiagTailX0RatChunk000Sub001Block098Tail =
      surrogateDiagTailX0RatChunk000Sub001Block098 := by
  unfold surrogateDiagTailX0RatChunk000Sub001Block098Head surrogateDiagTailX0RatChunk000Sub001Block098Mid surrogateDiagTailX0RatChunk000Sub001Block098Tail surrogateDiagTailX0RatChunk000Sub001Block098
  ring

def SurrogateDiagonalTailChunk000Sub001Block098HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block098HeadSum X0 = surrogateDiagTailX0RatChunk000Sub001Block098Head

def SurrogateDiagonalTailChunk000Sub001Block098MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block098MidSum X0 = surrogateDiagTailX0RatChunk000Sub001Block098Mid

def SurrogateDiagonalTailChunk000Sub001Block098TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block098TailSum X0 = surrogateDiagTailX0RatChunk000Sub001Block098Tail

theorem surrogateDiagonalTailChunk000Sub001Block098_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk000Sub001Block098HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk000Sub001Block098MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk000Sub001Block098TailCertificateAt X0) :
    surrogateDiagonalTailChunk000Sub001Block098Sum X0 = surrogateDiagTailX0RatChunk000Sub001Block098 := by
  unfold SurrogateDiagonalTailChunk000Sub001Block098HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk000Sub001Block098MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk000Sub001Block098TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk000Sub001Block098Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk000Sub001Block098_eq_head_add_mid_add_tail

/-- Block 099 covers tail-support indices [7475,7500) and q from 12351 to 12387. -/

def TailChunk000Sub001Block099Part000SupportExplicit : Finset ℕ :=
  ([12351] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block099Part000 : ℚ :=
  (359687134875 : ℚ) / 3136146337488541696

def SurrogateDiagonalTailChunk000Sub001Block099Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12351
    = surrogateDiagTailX0RatChunk000Sub001Block099Part000

theorem surrogateDiagonalTailChunk000Sub001Block099Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block099Part000CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block099Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block099Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block099Part000CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block099Part000SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block099Part000] using hcert

def TailChunk000Sub001Block099Part001SupportExplicit : Finset ℕ :=
  ([12353] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block099Part001 : ℚ :=
  (12706380781 : ℚ) / 1585105883241091200

def SurrogateDiagonalTailChunk000Sub001Block099Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12353
    = surrogateDiagTailX0RatChunk000Sub001Block099Part001

theorem surrogateDiagonalTailChunk000Sub001Block099Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block099Part001CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block099Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block099Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block099Part001CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block099Part001SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block099Part001] using hcert

def TailChunk000Sub001Block099Part002SupportExplicit : Finset ℕ :=
  ([12354] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block099Part002 : ℚ :=
  (8564223931 : ℚ) / 3373906774425600

def SurrogateDiagonalTailChunk000Sub001Block099Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12354
    = surrogateDiagTailX0RatChunk000Sub001Block099Part002

theorem surrogateDiagonalTailChunk000Sub001Block099Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block099Part002CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block099Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block099Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block099Part002CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block099Part002SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block099Part002] using hcert

def TailChunk000Sub001Block099Part003SupportExplicit : Finset ℕ :=
  ([12355] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block099Part003 : ℚ :=
  (55906857475 : ℚ) / 707570917919686656

def SurrogateDiagonalTailChunk000Sub001Block099Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12355
    = surrogateDiagTailX0RatChunk000Sub001Block099Part003

theorem surrogateDiagonalTailChunk000Sub001Block099Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block099Part003CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block099Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block099Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block099Part003CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block099Part003SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block099Part003] using hcert

def TailChunk000Sub001Block099Part004SupportExplicit : Finset ℕ :=
  ([12358] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block099Part004 : ℚ :=
  (2291851146025 : ℚ) / 3189107905431717888

def SurrogateDiagonalTailChunk000Sub001Block099Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12358
    = surrogateDiagTailX0RatChunk000Sub001Block099Part004

theorem surrogateDiagonalTailChunk000Sub001Block099Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block099Part004CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block099Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block099Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block099Part004CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block099Part004SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block099Part004] using hcert

def TailChunk000Sub001Block099Part005SupportExplicit : Finset ℕ :=
  ([12359] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block099Part005 : ℚ :=
  (117658638125 : ℚ) / 22762673897304489984

def SurrogateDiagonalTailChunk000Sub001Block099Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12359
    = surrogateDiagTailX0RatChunk000Sub001Block099Part005

theorem surrogateDiagonalTailChunk000Sub001Block099Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block099Part005CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block099Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block099Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block099Part005CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block099Part005SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block099Part005] using hcert

def TailChunk000Sub001Block099Part006SupportExplicit : Finset ℕ :=
  ([12361] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block099Part006 : ℚ :=
  (47773705775 : ℚ) / 26377483207372643904

def SurrogateDiagonalTailChunk000Sub001Block099Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12361
    = surrogateDiagTailX0RatChunk000Sub001Block099Part006

theorem surrogateDiagonalTailChunk000Sub001Block099Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block099Part006CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block099Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block099Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block099Part006CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block099Part006SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block099Part006] using hcert

def TailChunk000Sub001Block099Part007SupportExplicit : Finset ℕ :=
  ([12362] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block099Part007 : ℚ :=
  (1947032156875 : ℚ) / 1961129176680094848

def SurrogateDiagonalTailChunk000Sub001Block099Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12362
    = surrogateDiagTailX0RatChunk000Sub001Block099Part007

theorem surrogateDiagonalTailChunk000Sub001Block099Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block099Part007CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block099Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block099Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block099Part007CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block099Part007SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block099Part007] using hcert

def TailChunk000Sub001Block099Part008SupportExplicit : Finset ℕ :=
  ([12363] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block099Part008 : ℚ :=
  (556042673375 : ℚ) / 4136091716566646784

def SurrogateDiagonalTailChunk000Sub001Block099Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12363
    = surrogateDiagTailX0RatChunk000Sub001Block099Part008

theorem surrogateDiagonalTailChunk000Sub001Block099Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block099Part008CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block099Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block099Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block099Part008CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block099Part008SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block099Part008] using hcert

def TailChunk000Sub001Block099Part009SupportExplicit : Finset ℕ :=
  ([12365] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block099Part009 : ℚ :=
  (254981871175 : ℚ) / 7967818545253318656

def SurrogateDiagonalTailChunk000Sub001Block099Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12365
    = surrogateDiagTailX0RatChunk000Sub001Block099Part009

theorem surrogateDiagonalTailChunk000Sub001Block099Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block099Part009CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block099Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block099Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block099Part009CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block099Part009SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block099Part009] using hcert

def TailChunk000Sub001Block099Part010SupportExplicit : Finset ℕ :=
  ([12367] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block099Part010 : ℚ :=
  (71763950725 : ℚ) / 54241180136789035008

def SurrogateDiagonalTailChunk000Sub001Block099Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12367
    = surrogateDiagTailX0RatChunk000Sub001Block099Part010

theorem surrogateDiagonalTailChunk000Sub001Block099Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block099Part010CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block099Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block099Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block099Part010CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block099Part010SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block099Part010] using hcert

def TailChunk000Sub001Block099Part011SupportExplicit : Finset ℕ :=
  ([12369] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block099Part011 : ℚ :=
  (1812145165 : ℚ) / 7054185323593728

def SurrogateDiagonalTailChunk000Sub001Block099Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12369
    = surrogateDiagTailX0RatChunk000Sub001Block099Part011

theorem surrogateDiagonalTailChunk000Sub001Block099Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block099Part011CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block099Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block099Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block099Part011CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block099Part011SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block099Part011] using hcert

def TailChunk000Sub001Block099Part012SupportExplicit : Finset ℕ :=
  ([12370] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block099Part012 : ℚ :=
  (302622147775 : ℚ) / 248994329539166208

def SurrogateDiagonalTailChunk000Sub001Block099Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12370
    = surrogateDiagTailX0RatChunk000Sub001Block099Part012

theorem surrogateDiagonalTailChunk000Sub001Block099Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block099Part012CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block099Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block099Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block099Part012CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block099Part012SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block099Part012] using hcert

def TailChunk000Sub001Block099Part013SupportExplicit : Finset ℕ :=
  ([12371] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block099Part013 : ℚ :=
  (3913101475 : ℚ) / 3021352435936935936

def SurrogateDiagonalTailChunk000Sub001Block099Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12371
    = surrogateDiagTailX0RatChunk000Sub001Block099Part013

theorem surrogateDiagonalTailChunk000Sub001Block099Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block099Part013CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block099Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block099Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block099Part013CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block099Part013SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block099Part013] using hcert

def TailChunk000Sub001Block099Part014SupportExplicit : Finset ℕ :=
  ([12373] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block099Part014 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block099Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12373
    = surrogateDiagTailX0RatChunk000Sub001Block099Part014

theorem surrogateDiagonalTailChunk000Sub001Block099Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block099Part014CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block099Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block099Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block099Part014CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block099Part014SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block099Part014] using hcert

def TailChunk000Sub001Block099Part015SupportExplicit : Finset ℕ :=
  ([12374] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block099Part015 : ℚ :=
  (753582398175 : ℚ) / 1007245889104254976

def SurrogateDiagonalTailChunk000Sub001Block099Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12374
    = surrogateDiagTailX0RatChunk000Sub001Block099Part015

theorem surrogateDiagonalTailChunk000Sub001Block099Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block099Part015CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block099Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block099Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block099Part015CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block099Part015SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block099Part015] using hcert

def TailChunk000Sub001Block099Part016SupportExplicit : Finset ℕ :=
  ([12377] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block099Part016 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block099Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12377
    = surrogateDiagTailX0RatChunk000Sub001Block099Part016

theorem surrogateDiagonalTailChunk000Sub001Block099Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block099Part016CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block099Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block099Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block099Part016CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block099Part016SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block099Part016] using hcert

def TailChunk000Sub001Block099Part017SupportExplicit : Finset ℕ :=
  ([12378] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block099Part017 : ℚ :=
  (332384682025 : ℚ) / 180817930358160672

def SurrogateDiagonalTailChunk000Sub001Block099Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12378
    = surrogateDiagTailX0RatChunk000Sub001Block099Part017

theorem surrogateDiagonalTailChunk000Sub001Block099Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block099Part017CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block099Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block099Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block099Part017CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block099Part017SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block099Part017] using hcert

def TailChunk000Sub001Block099Part018SupportExplicit : Finset ℕ :=
  ([12379] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block099Part018 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block099Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12379
    = surrogateDiagTailX0RatChunk000Sub001Block099Part018

theorem surrogateDiagonalTailChunk000Sub001Block099Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block099Part018CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block099Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block099Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block099Part018CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block099Part018SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block099Part018] using hcert

def TailChunk000Sub001Block099Part019SupportExplicit : Finset ℕ :=
  ([12381] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block099Part019 : ℚ :=
  (532308667175 : ℚ) / 5797406330683773504

def SurrogateDiagonalTailChunk000Sub001Block099Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12381
    = surrogateDiagTailX0RatChunk000Sub001Block099Part019

theorem surrogateDiagonalTailChunk000Sub001Block099Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block099Part019CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block099Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block099Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block099Part019CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block099Part019SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block099Part019] using hcert

def TailChunk000Sub001Block099Part020SupportExplicit : Finset ℕ :=
  ([12382] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block099Part020 : ℚ :=
  (92313848299 : ℚ) / 129625920000000000

def SurrogateDiagonalTailChunk000Sub001Block099Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12382
    = surrogateDiagTailX0RatChunk000Sub001Block099Part020

theorem surrogateDiagonalTailChunk000Sub001Block099Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block099Part020CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block099Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block099Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block099Part020CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block099Part020SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block099Part020] using hcert

def TailChunk000Sub001Block099Part021SupportExplicit : Finset ℕ :=
  ([12383] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block099Part021 : ℚ :=
  (230827097 : ℚ) / 8604937744220160

def SurrogateDiagonalTailChunk000Sub001Block099Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12383
    = surrogateDiagTailX0RatChunk000Sub001Block099Part021

theorem surrogateDiagonalTailChunk000Sub001Block099Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block099Part021CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block099Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block099Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block099Part021CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block099Part021SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block099Part021] using hcert

def TailChunk000Sub001Block099Part022SupportExplicit : Finset ℕ :=
  ([12385] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block099Part022 : ℚ :=
  (767419117525 : ℚ) / 24058546485884387328

def SurrogateDiagonalTailChunk000Sub001Block099Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12385
    = surrogateDiagTailX0RatChunk000Sub001Block099Part022

theorem surrogateDiagonalTailChunk000Sub001Block099Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block099Part022CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block099Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block099Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block099Part022CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block099Part022SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block099Part022] using hcert

def TailChunk000Sub001Block099Part023SupportExplicit : Finset ℕ :=
  ([12386] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block099Part023 : ℚ :=
  (84628620511 : ℚ) / 99777383822467200

def SurrogateDiagonalTailChunk000Sub001Block099Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12386
    = surrogateDiagTailX0RatChunk000Sub001Block099Part023

theorem surrogateDiagonalTailChunk000Sub001Block099Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block099Part023CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block099Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block099Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block099Part023CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block099Part023SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block099Part023] using hcert

def TailChunk000Sub001Block099Part024SupportExplicit : Finset ℕ :=
  ([12387] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block099Part024 : ℚ :=
  (266412271075 : ℚ) / 2904327618048294912

def SurrogateDiagonalTailChunk000Sub001Block099Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12387
    = surrogateDiagTailX0RatChunk000Sub001Block099Part024

theorem surrogateDiagonalTailChunk000Sub001Block099Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block099Part024CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block099Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block099Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block099Part024CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block099Part024SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block099Part024] using hcert

def surrogateDiagonalTailChunk000Sub001Block099HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block099Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block099Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block099Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block099Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block099Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block099Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block099Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block099Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block099Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block099Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block099Head : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block099Part000
    + surrogateDiagTailX0RatChunk000Sub001Block099Part001
    + surrogateDiagTailX0RatChunk000Sub001Block099Part002
    + surrogateDiagTailX0RatChunk000Sub001Block099Part003
    + surrogateDiagTailX0RatChunk000Sub001Block099Part004
    + surrogateDiagTailX0RatChunk000Sub001Block099Part005
    + surrogateDiagTailX0RatChunk000Sub001Block099Part006
    + surrogateDiagTailX0RatChunk000Sub001Block099Part007
    + surrogateDiagTailX0RatChunk000Sub001Block099Part008
    + surrogateDiagTailX0RatChunk000Sub001Block099Part009

def surrogateDiagonalTailChunk000Sub001Block099MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block099Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block099Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block099Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block099Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block099Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block099Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block099Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block099Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block099Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block099Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block099Mid : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block099Part010
    + surrogateDiagTailX0RatChunk000Sub001Block099Part011
    + surrogateDiagTailX0RatChunk000Sub001Block099Part012
    + surrogateDiagTailX0RatChunk000Sub001Block099Part013
    + surrogateDiagTailX0RatChunk000Sub001Block099Part014
    + surrogateDiagTailX0RatChunk000Sub001Block099Part015
    + surrogateDiagTailX0RatChunk000Sub001Block099Part016
    + surrogateDiagTailX0RatChunk000Sub001Block099Part017
    + surrogateDiagTailX0RatChunk000Sub001Block099Part018
    + surrogateDiagTailX0RatChunk000Sub001Block099Part019

def surrogateDiagonalTailChunk000Sub001Block099TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block099Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block099Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block099Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block099Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block099Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block099Tail : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block099Part020
    + surrogateDiagTailX0RatChunk000Sub001Block099Part021
    + surrogateDiagTailX0RatChunk000Sub001Block099Part022
    + surrogateDiagTailX0RatChunk000Sub001Block099Part023
    + surrogateDiagTailX0RatChunk000Sub001Block099Part024

def surrogateDiagonalTailChunk000Sub001Block099Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub001Block099HeadSum X0
    + surrogateDiagonalTailChunk000Sub001Block099MidSum X0
    + surrogateDiagonalTailChunk000Sub001Block099TailSum X0

def surrogateDiagTailX0RatChunk000Sub001Block099 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block099Part000
    + surrogateDiagTailX0RatChunk000Sub001Block099Part001
    + surrogateDiagTailX0RatChunk000Sub001Block099Part002
    + surrogateDiagTailX0RatChunk000Sub001Block099Part003
    + surrogateDiagTailX0RatChunk000Sub001Block099Part004
    + surrogateDiagTailX0RatChunk000Sub001Block099Part005
    + surrogateDiagTailX0RatChunk000Sub001Block099Part006
    + surrogateDiagTailX0RatChunk000Sub001Block099Part007
    + surrogateDiagTailX0RatChunk000Sub001Block099Part008
    + surrogateDiagTailX0RatChunk000Sub001Block099Part009
    + surrogateDiagTailX0RatChunk000Sub001Block099Part010
    + surrogateDiagTailX0RatChunk000Sub001Block099Part011
    + surrogateDiagTailX0RatChunk000Sub001Block099Part012
    + surrogateDiagTailX0RatChunk000Sub001Block099Part013
    + surrogateDiagTailX0RatChunk000Sub001Block099Part014
    + surrogateDiagTailX0RatChunk000Sub001Block099Part015
    + surrogateDiagTailX0RatChunk000Sub001Block099Part016
    + surrogateDiagTailX0RatChunk000Sub001Block099Part017
    + surrogateDiagTailX0RatChunk000Sub001Block099Part018
    + surrogateDiagTailX0RatChunk000Sub001Block099Part019
    + surrogateDiagTailX0RatChunk000Sub001Block099Part020
    + surrogateDiagTailX0RatChunk000Sub001Block099Part021
    + surrogateDiagTailX0RatChunk000Sub001Block099Part022
    + surrogateDiagTailX0RatChunk000Sub001Block099Part023
    + surrogateDiagTailX0RatChunk000Sub001Block099Part024

theorem surrogateDiagTailX0RatChunk000Sub001Block099_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk000Sub001Block099Head + surrogateDiagTailX0RatChunk000Sub001Block099Mid + surrogateDiagTailX0RatChunk000Sub001Block099Tail =
      surrogateDiagTailX0RatChunk000Sub001Block099 := by
  unfold surrogateDiagTailX0RatChunk000Sub001Block099Head surrogateDiagTailX0RatChunk000Sub001Block099Mid surrogateDiagTailX0RatChunk000Sub001Block099Tail surrogateDiagTailX0RatChunk000Sub001Block099
  ring

def SurrogateDiagonalTailChunk000Sub001Block099HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block099HeadSum X0 = surrogateDiagTailX0RatChunk000Sub001Block099Head

def SurrogateDiagonalTailChunk000Sub001Block099MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block099MidSum X0 = surrogateDiagTailX0RatChunk000Sub001Block099Mid

def SurrogateDiagonalTailChunk000Sub001Block099TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block099TailSum X0 = surrogateDiagTailX0RatChunk000Sub001Block099Tail

theorem surrogateDiagonalTailChunk000Sub001Block099_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk000Sub001Block099HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk000Sub001Block099MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk000Sub001Block099TailCertificateAt X0) :
    surrogateDiagonalTailChunk000Sub001Block099Sum X0 = surrogateDiagTailX0RatChunk000Sub001Block099 := by
  unfold SurrogateDiagonalTailChunk000Sub001Block099HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk000Sub001Block099MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk000Sub001Block099TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk000Sub001Block099Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk000Sub001Block099_eq_head_add_mid_add_tail

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

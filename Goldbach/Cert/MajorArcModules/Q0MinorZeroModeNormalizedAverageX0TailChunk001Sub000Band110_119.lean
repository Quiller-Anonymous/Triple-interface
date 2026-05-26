import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0TailPilot25

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

open scoped BigOperators

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

/- Generated direct-term certificate blocks for tail chunk 001, subchunk 000, blocks [110,120). -/

/-- Block 110 covers tail-support indices [12750,12775) and q from 21019 to 21061. -/

def TailChunk001Sub000Block110Part000SupportExplicit : Finset ℕ :=
  ([21019] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block110Part000 : ℚ :=
  (6903099390625 : ℚ) / 121992299702469859122

def SurrogateDiagonalTailChunk001Sub000Block110Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21019
    = surrogateDiagTailX0RatChunk001Sub000Block110Part000

theorem surrogateDiagonalTailChunk001Sub000Block110Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block110Part000CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block110Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block110Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block110Part000CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block110Part000SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block110Part000] using hcert

def TailChunk001Sub000Block110Part001SupportExplicit : Finset ℕ :=
  ([21022] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block110Part001 : ℚ :=
  (6427764445825 : ℚ) / 25326603587277324288

def SurrogateDiagonalTailChunk001Sub000Block110Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21022
    = surrogateDiagTailX0RatChunk001Sub000Block110Part001

theorem surrogateDiagonalTailChunk001Sub000Block110Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block110Part001CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block110Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block110Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block110Part001CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block110Part001SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block110Part001] using hcert

def TailChunk001Sub000Block110Part002SupportExplicit : Finset ℕ :=
  ([21023] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block110Part002 : ℚ :=
  (6905727015625 : ℚ) / 122085193130361243282

def SurrogateDiagonalTailChunk001Sub000Block110Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21023
    = surrogateDiagTailX0RatChunk001Sub000Block110Part002

theorem surrogateDiagonalTailChunk001Sub000Block110Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block110Part002CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block110Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block110Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block110Part002CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block110Part002SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block110Part002] using hcert

def TailChunk001Sub000Block110Part003SupportExplicit : Finset ℕ :=
  ([21026] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block110Part003 : ℚ :=
  (1726924515625 : ℚ) / 7633228733351534592

def SurrogateDiagonalTailChunk001Sub000Block110Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21026
    = surrogateDiagTailX0RatChunk001Sub000Block110Part003

theorem surrogateDiagonalTailChunk001Sub000Block110Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block110Part003CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block110Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block110Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block110Part003CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block110Part003SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block110Part003] using hcert

def TailChunk001Sub000Block110Part004SupportExplicit : Finset ℕ :=
  ([21027] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block110Part004 : ℚ :=
  (1299209726725 : ℚ) / 9527118166096054272

def SurrogateDiagonalTailChunk001Sub000Block110Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21027
    = surrogateDiagTailX0RatChunk001Sub000Block110Part004

theorem surrogateDiagonalTailChunk001Sub000Block110Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block110Part004CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block110Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block110Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block110Part004CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block110Part004SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block110Part004] using hcert

def TailChunk001Sub000Block110Part005SupportExplicit : Finset ℕ :=
  ([21029] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block110Part005 : ℚ :=
  (193252142375 : ℚ) / 2987931954469994496

def SurrogateDiagonalTailChunk001Sub000Block110Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21029
    = surrogateDiagTailX0RatChunk001Sub000Block110Part005

theorem surrogateDiagonalTailChunk001Sub000Block110Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block110Part005CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block110Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block110Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block110Part005CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block110Part005SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block110Part005] using hcert

def TailChunk001Sub000Block110Part006SupportExplicit : Finset ℕ :=
  ([21030] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block110Part006 : ℚ :=
  (111594860071 : ℚ) / 98364628992000000

def SurrogateDiagonalTailChunk001Sub000Block110Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21030
    = surrogateDiagTailX0RatChunk001Sub000Block110Part006

theorem surrogateDiagonalTailChunk001Sub000Block110Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block110Part006CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block110Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block110Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block110Part006CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block110Part006SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block110Part006] using hcert

def TailChunk001Sub000Block110Part007SupportExplicit : Finset ℕ :=
  ([21031] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block110Part007 : ℚ :=
  (11057574025 : ℚ) / 195633822609543762

def SurrogateDiagonalTailChunk001Sub000Block110Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21031
    = surrogateDiagTailX0RatChunk001Sub000Block110Part007

theorem surrogateDiagonalTailChunk001Sub000Block110Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block110Part007CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block110Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block110Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block110Part007CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block110Part007SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block110Part007] using hcert

def TailChunk001Sub000Block110Part008SupportExplicit : Finset ℕ :=
  ([21034] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block110Part008 : ℚ :=
  (6084356592025 : ℚ) / 22100255072573718528

def SurrogateDiagonalTailChunk001Sub000Block110Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21034
    = surrogateDiagTailX0RatChunk001Sub000Block110Part008

theorem surrogateDiagonalTailChunk001Sub000Block110Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block110Part008CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block110Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block110Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block110Part008CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block110Part008SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block110Part008] using hcert

def TailChunk001Sub000Block110Part009SupportExplicit : Finset ℕ :=
  ([21035] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block110Part009 : ℚ :=
  (570940593079 : ℚ) / 4300676923392000000

def SurrogateDiagonalTailChunk001Sub000Block110Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21035
    = surrogateDiagTailX0RatChunk001Sub000Block110Part009

theorem surrogateDiagonalTailChunk001Sub000Block110Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block110Part009CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block110Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block110Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block110Part009CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block110Part009SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block110Part009] using hcert

def TailChunk001Sub000Block110Part010SupportExplicit : Finset ℕ :=
  ([21037] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block110Part010 : ℚ :=
  (26966759638375 : ℚ) / 462303089367038558208

def SurrogateDiagonalTailChunk001Sub000Block110Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21037
    = surrogateDiagTailX0RatChunk001Sub000Block110Part010

theorem surrogateDiagonalTailChunk001Sub000Block110Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block110Part010CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block110Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block110Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block110Part010CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block110Part010SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block110Part010] using hcert

def TailChunk001Sub000Block110Part011SupportExplicit : Finset ℕ :=
  ([21038] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block110Part011 : ℚ :=
  (6694043905375 : ℚ) / 28099655432333641728

def SurrogateDiagonalTailChunk001Sub000Block110Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21038
    = surrogateDiagTailX0RatChunk001Sub000Block110Part011

theorem surrogateDiagonalTailChunk001Sub000Block110Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block110Part011CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block110Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block110Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block110Part011CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block110Part011SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block110Part011] using hcert

def TailChunk001Sub000Block110Part012SupportExplicit : Finset ℕ :=
  ([21039] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block110Part012 : ℚ :=
  (12292660298725 : ℚ) / 96719595427264677888

def SurrogateDiagonalTailChunk001Sub000Block110Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21039
    = surrogateDiagTailX0RatChunk001Sub000Block110Part012

theorem surrogateDiagonalTailChunk001Sub000Block110Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block110Part012CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block110Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block110Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block110Part012CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block110Part012SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block110Part012] using hcert

def TailChunk001Sub000Block110Part013SupportExplicit : Finset ℕ :=
  ([21041] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block110Part013 : ℚ :=
  (8879298773375 : ℚ) / 149864828972446089216

def SurrogateDiagonalTailChunk001Sub000Block110Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21041
    = surrogateDiagTailX0RatChunk001Sub000Block110Part013

theorem surrogateDiagonalTailChunk001Sub000Block110Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block110Part013CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block110Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block110Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block110Part013CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block110Part013SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block110Part013] using hcert

def TailChunk001Sub000Block110Part014SupportExplicit : Finset ℕ :=
  ([21043] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block110Part014 : ℚ :=
  (4600044079 : ℚ) / 3341784271593676800

def SurrogateDiagonalTailChunk001Sub000Block110Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21043
    = surrogateDiagTailX0RatChunk001Sub000Block110Part014

theorem surrogateDiagonalTailChunk001Sub000Block110Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block110Part014CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block110Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block110Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block110Part014CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block110Part014SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block110Part014] using hcert

def TailChunk001Sub000Block110Part015SupportExplicit : Finset ℕ :=
  ([21045] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block110Part015 : ℚ :=
  (5652066067 : ℚ) / 207296167359283200

def SurrogateDiagonalTailChunk001Sub000Block110Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21045
    = surrogateDiagTailX0RatChunk001Sub000Block110Part015

theorem surrogateDiagonalTailChunk001Sub000Block110Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block110Part015CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block110Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block110Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block110Part015CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block110Part015SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block110Part015] using hcert

def TailChunk001Sub000Block110Part016SupportExplicit : Finset ℕ :=
  ([21046] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block110Part016 : ℚ :=
  (195692721925 : ℚ) / 23903455635759955968

def SurrogateDiagonalTailChunk001Sub000Block110Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21046
    = surrogateDiagTailX0RatChunk001Sub000Block110Part016

theorem surrogateDiagonalTailChunk001Sub000Block110Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block110Part016CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block110Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block110Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block110Part016CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block110Part016SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block110Part016] using hcert

def TailChunk001Sub000Block110Part017SupportExplicit : Finset ℕ :=
  ([21047] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block110Part017 : ℚ :=
  (30901101175 : ℚ) / 22209865550967454848

def SurrogateDiagonalTailChunk001Sub000Block110Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21047
    = surrogateDiagTailX0RatChunk001Sub000Block110Part017

theorem surrogateDiagonalTailChunk001Sub000Block110Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block110Part017CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block110Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block110Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block110Part017CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block110Part017SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block110Part017] using hcert

def TailChunk001Sub000Block110Part018SupportExplicit : Finset ℕ :=
  ([21049] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block110Part018 : ℚ :=
  (14900587901 : ℚ) / 4458941834172825600

def SurrogateDiagonalTailChunk001Sub000Block110Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21049
    = surrogateDiagTailX0RatChunk001Sub000Block110Part018

theorem surrogateDiagonalTailChunk001Sub000Block110Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block110Part018CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block110Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block110Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block110Part018CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block110Part018SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block110Part018] using hcert

def TailChunk001Sub000Block110Part019SupportExplicit : Finset ℕ :=
  ([21053] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block110Part019 : ℚ :=
  (1781722825 : ℚ) / 4047682594862923776

def SurrogateDiagonalTailChunk001Sub000Block110Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21053
    = surrogateDiagTailX0RatChunk001Sub000Block110Part019

theorem surrogateDiagonalTailChunk001Sub000Block110Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block110Part019CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block110Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block110Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block110Part019CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block110Part019SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block110Part019] using hcert

def TailChunk001Sub000Block110Part020SupportExplicit : Finset ℕ :=
  ([21055] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block110Part020 : ℚ :=
  (2957351763 : ℚ) / 536245844572436480

def SurrogateDiagonalTailChunk001Sub000Block110Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21055
    = surrogateDiagTailX0RatChunk001Sub000Block110Part020

theorem surrogateDiagonalTailChunk001Sub000Block110Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block110Part020CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block110Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block110Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block110Part020CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block110Part020SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block110Part020] using hcert

def TailChunk001Sub000Block110Part021SupportExplicit : Finset ℕ :=
  ([21057] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block110Part021 : ℚ :=
  (125025 : ℚ) / 19406331355207808

def SurrogateDiagonalTailChunk001Sub000Block110Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21057
    = surrogateDiagTailX0RatChunk001Sub000Block110Part021

theorem surrogateDiagonalTailChunk001Sub000Block110Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block110Part021CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block110Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block110Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block110Part021CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block110Part021SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block110Part021] using hcert

def TailChunk001Sub000Block110Part022SupportExplicit : Finset ℕ :=
  ([21058] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block110Part022 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block110Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21058
    = surrogateDiagTailX0RatChunk001Sub000Block110Part022

theorem surrogateDiagonalTailChunk001Sub000Block110Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block110Part022CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block110Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block110Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block110Part022CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block110Part022SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block110Part022] using hcert

def TailChunk001Sub000Block110Part023SupportExplicit : Finset ℕ :=
  ([21059] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block110Part023 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block110Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21059
    = surrogateDiagTailX0RatChunk001Sub000Block110Part023

theorem surrogateDiagonalTailChunk001Sub000Block110Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block110Part023CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block110Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block110Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block110Part023CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block110Part023SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block110Part023] using hcert

def TailChunk001Sub000Block110Part024SupportExplicit : Finset ℕ :=
  ([21061] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block110Part024 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block110Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21061
    = surrogateDiagTailX0RatChunk001Sub000Block110Part024

theorem surrogateDiagonalTailChunk001Sub000Block110Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block110Part024CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block110Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block110Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block110Part024CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block110Part024SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block110Part024] using hcert

def surrogateDiagonalTailChunk001Sub000Block110HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block110Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block110Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block110Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block110Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block110Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block110Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block110Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block110Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block110Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block110Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block110Head : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block110Part000
    + surrogateDiagTailX0RatChunk001Sub000Block110Part001
    + surrogateDiagTailX0RatChunk001Sub000Block110Part002
    + surrogateDiagTailX0RatChunk001Sub000Block110Part003
    + surrogateDiagTailX0RatChunk001Sub000Block110Part004
    + surrogateDiagTailX0RatChunk001Sub000Block110Part005
    + surrogateDiagTailX0RatChunk001Sub000Block110Part006
    + surrogateDiagTailX0RatChunk001Sub000Block110Part007
    + surrogateDiagTailX0RatChunk001Sub000Block110Part008
    + surrogateDiagTailX0RatChunk001Sub000Block110Part009

def surrogateDiagonalTailChunk001Sub000Block110MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block110Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block110Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block110Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block110Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block110Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block110Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block110Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block110Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block110Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block110Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block110Mid : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block110Part010
    + surrogateDiagTailX0RatChunk001Sub000Block110Part011
    + surrogateDiagTailX0RatChunk001Sub000Block110Part012
    + surrogateDiagTailX0RatChunk001Sub000Block110Part013
    + surrogateDiagTailX0RatChunk001Sub000Block110Part014
    + surrogateDiagTailX0RatChunk001Sub000Block110Part015
    + surrogateDiagTailX0RatChunk001Sub000Block110Part016
    + surrogateDiagTailX0RatChunk001Sub000Block110Part017
    + surrogateDiagTailX0RatChunk001Sub000Block110Part018
    + surrogateDiagTailX0RatChunk001Sub000Block110Part019

def surrogateDiagonalTailChunk001Sub000Block110TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block110Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block110Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block110Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block110Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block110Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block110Tail : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block110Part020
    + surrogateDiagTailX0RatChunk001Sub000Block110Part021
    + surrogateDiagTailX0RatChunk001Sub000Block110Part022
    + surrogateDiagTailX0RatChunk001Sub000Block110Part023
    + surrogateDiagTailX0RatChunk001Sub000Block110Part024

def surrogateDiagonalTailChunk001Sub000Block110Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk001Sub000Block110HeadSum X0
    + surrogateDiagonalTailChunk001Sub000Block110MidSum X0
    + surrogateDiagonalTailChunk001Sub000Block110TailSum X0

def surrogateDiagTailX0RatChunk001Sub000Block110 : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block110Part000
    + surrogateDiagTailX0RatChunk001Sub000Block110Part001
    + surrogateDiagTailX0RatChunk001Sub000Block110Part002
    + surrogateDiagTailX0RatChunk001Sub000Block110Part003
    + surrogateDiagTailX0RatChunk001Sub000Block110Part004
    + surrogateDiagTailX0RatChunk001Sub000Block110Part005
    + surrogateDiagTailX0RatChunk001Sub000Block110Part006
    + surrogateDiagTailX0RatChunk001Sub000Block110Part007
    + surrogateDiagTailX0RatChunk001Sub000Block110Part008
    + surrogateDiagTailX0RatChunk001Sub000Block110Part009
    + surrogateDiagTailX0RatChunk001Sub000Block110Part010
    + surrogateDiagTailX0RatChunk001Sub000Block110Part011
    + surrogateDiagTailX0RatChunk001Sub000Block110Part012
    + surrogateDiagTailX0RatChunk001Sub000Block110Part013
    + surrogateDiagTailX0RatChunk001Sub000Block110Part014
    + surrogateDiagTailX0RatChunk001Sub000Block110Part015
    + surrogateDiagTailX0RatChunk001Sub000Block110Part016
    + surrogateDiagTailX0RatChunk001Sub000Block110Part017
    + surrogateDiagTailX0RatChunk001Sub000Block110Part018
    + surrogateDiagTailX0RatChunk001Sub000Block110Part019
    + surrogateDiagTailX0RatChunk001Sub000Block110Part020
    + surrogateDiagTailX0RatChunk001Sub000Block110Part021
    + surrogateDiagTailX0RatChunk001Sub000Block110Part022
    + surrogateDiagTailX0RatChunk001Sub000Block110Part023
    + surrogateDiagTailX0RatChunk001Sub000Block110Part024

theorem surrogateDiagTailX0RatChunk001Sub000Block110_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk001Sub000Block110Head + surrogateDiagTailX0RatChunk001Sub000Block110Mid + surrogateDiagTailX0RatChunk001Sub000Block110Tail =
      surrogateDiagTailX0RatChunk001Sub000Block110 := by
  unfold surrogateDiagTailX0RatChunk001Sub000Block110Head surrogateDiagTailX0RatChunk001Sub000Block110Mid surrogateDiagTailX0RatChunk001Sub000Block110Tail surrogateDiagTailX0RatChunk001Sub000Block110
  ring

def SurrogateDiagonalTailChunk001Sub000Block110HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block110HeadSum X0 = surrogateDiagTailX0RatChunk001Sub000Block110Head

def SurrogateDiagonalTailChunk001Sub000Block110MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block110MidSum X0 = surrogateDiagTailX0RatChunk001Sub000Block110Mid

def SurrogateDiagonalTailChunk001Sub000Block110TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block110TailSum X0 = surrogateDiagTailX0RatChunk001Sub000Block110Tail

theorem surrogateDiagonalTailChunk001Sub000Block110_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk001Sub000Block110HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk001Sub000Block110MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk001Sub000Block110TailCertificateAt X0) :
    surrogateDiagonalTailChunk001Sub000Block110Sum X0 = surrogateDiagTailX0RatChunk001Sub000Block110 := by
  unfold SurrogateDiagonalTailChunk001Sub000Block110HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk001Sub000Block110MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk001Sub000Block110TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk001Sub000Block110Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk001Sub000Block110_eq_head_add_mid_add_tail

/-- Block 111 covers tail-support indices [12775,12800) and q from 21062 to 21102. -/

def TailChunk001Sub000Block111Part000SupportExplicit : Finset ℕ :=
  ([21062] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block111Part000 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block111Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21062
    = surrogateDiagTailX0RatChunk001Sub000Block111Part000

theorem surrogateDiagonalTailChunk001Sub000Block111Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block111Part000CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block111Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block111Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block111Part000CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block111Part000SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block111Part000] using hcert

def TailChunk001Sub000Block111Part001SupportExplicit : Finset ℕ :=
  ([21063] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block111Part001 : ℚ :=
  (77950280725 : ℚ) / 4272688566330458112

def SurrogateDiagonalTailChunk001Sub000Block111Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21063
    = surrogateDiagTailX0RatChunk001Sub000Block111Part001

theorem surrogateDiagonalTailChunk001Sub000Block111Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block111Part001CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block111Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block111Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block111Part001CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block111Part001SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block111Part001] using hcert

def TailChunk001Sub000Block111Part002SupportExplicit : Finset ℕ :=
  ([21065] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block111Part002 : ℚ :=
  (17436311277 : ℚ) / 1817435523307110400

def SurrogateDiagonalTailChunk001Sub000Block111Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21065
    = surrogateDiagTailX0RatChunk001Sub000Block111Part002

theorem surrogateDiagonalTailChunk001Sub000Block111Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block111Part002CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block111Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block111Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block111Part002CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block111Part002SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block111Part002] using hcert

def TailChunk001Sub000Block111Part003SupportExplicit : Finset ℕ :=
  ([21066] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block111Part003 : ℚ :=
  (3082525399 : ℚ) / 24290435357248320

def SurrogateDiagonalTailChunk001Sub000Block111Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21066
    = surrogateDiagTailX0RatChunk001Sub000Block111Part003

theorem surrogateDiagonalTailChunk001Sub000Block111Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block111Part003CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block111Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block111Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block111Part003CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block111Part003SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block111Part003] using hcert

def TailChunk001Sub000Block111Part004SupportExplicit : Finset ℕ :=
  ([21067] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block111Part004 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block111Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21067
    = surrogateDiagTailX0RatChunk001Sub000Block111Part004

theorem surrogateDiagonalTailChunk001Sub000Block111Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block111Part004CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block111Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block111Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block111Part004CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block111Part004SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block111Part004] using hcert

def TailChunk001Sub000Block111Part005SupportExplicit : Finset ℕ :=
  ([21071] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block111Part005 : ℚ :=
  (32413386025 : ℚ) / 32968157388130543104

def SurrogateDiagonalTailChunk001Sub000Block111Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21071
    = surrogateDiagTailX0RatChunk001Sub000Block111Part005

theorem surrogateDiagonalTailChunk001Sub000Block111Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block111Part005CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block111Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block111Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block111Part005CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block111Part005SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block111Part005] using hcert

def TailChunk001Sub000Block111Part006SupportExplicit : Finset ℕ :=
  ([21073] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block111Part006 : ℚ :=
  (9912627641 : ℚ) / 7142362640138649600

def SurrogateDiagonalTailChunk001Sub000Block111Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21073
    = surrogateDiagTailX0RatChunk001Sub000Block111Part006

theorem surrogateDiagonalTailChunk001Sub000Block111Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block111Part006CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block111Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block111Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block111Part006CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block111Part006SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block111Part006] using hcert

def TailChunk001Sub000Block111Part007SupportExplicit : Finset ℕ :=
  ([21074] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block111Part007 : ℚ :=
  (600317649 : ℚ) / 183288588350259200

def SurrogateDiagonalTailChunk001Sub000Block111Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21074
    = surrogateDiagTailX0RatChunk001Sub000Block111Part007

theorem surrogateDiagonalTailChunk001Sub000Block111Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block111Part007CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block111Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block111Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block111Part007CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block111Part007SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block111Part007] using hcert

def TailChunk001Sub000Block111Part008SupportExplicit : Finset ℕ :=
  ([21077] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block111Part008 : ℚ :=
  (22725246013 : ℚ) / 10640397050375299200

def SurrogateDiagonalTailChunk001Sub000Block111Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21077
    = surrogateDiagTailX0RatChunk001Sub000Block111Part008

theorem surrogateDiagonalTailChunk001Sub000Block111Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block111Part008CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block111Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block111Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block111Part008CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block111Part008SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block111Part008] using hcert

def TailChunk001Sub000Block111Part009SupportExplicit : Finset ℕ :=
  ([21079] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block111Part009 : ℚ :=
  (15508471275 : ℚ) / 77646762956514741248

def SurrogateDiagonalTailChunk001Sub000Block111Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21079
    = surrogateDiagTailX0RatChunk001Sub000Block111Part009

theorem surrogateDiagonalTailChunk001Sub000Block111Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block111Part009CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block111Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block111Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block111Part009CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block111Part009SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block111Part009] using hcert

def TailChunk001Sub000Block111Part010SupportExplicit : Finset ℕ :=
  ([21081] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block111Part010 : ℚ :=
  (41675 : ℚ) / 6498323297559936

def SurrogateDiagonalTailChunk001Sub000Block111Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21081
    = surrogateDiagTailX0RatChunk001Sub000Block111Part010

theorem surrogateDiagonalTailChunk001Sub000Block111Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block111Part010CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block111Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block111Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block111Part010CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block111Part010SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block111Part010] using hcert

def TailChunk001Sub000Block111Part011SupportExplicit : Finset ℕ :=
  ([21082] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block111Part011 : ℚ :=
  (7103101225 : ℚ) / 3166080401698607232

def SurrogateDiagonalTailChunk001Sub000Block111Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21082
    = surrogateDiagTailX0RatChunk001Sub000Block111Part011

theorem surrogateDiagonalTailChunk001Sub000Block111Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block111Part011CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block111Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block111Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block111Part011CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block111Part011SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block111Part011] using hcert

def TailChunk001Sub000Block111Part012SupportExplicit : Finset ℕ :=
  ([21083] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block111Part012 : ℚ :=
  (79683639275 : ℚ) / 142325989654760626176

def SurrogateDiagonalTailChunk001Sub000Block111Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21083
    = surrogateDiagTailX0RatChunk001Sub000Block111Part012

theorem surrogateDiagonalTailChunk001Sub000Block111Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block111Part012CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block111Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block111Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block111Part012CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block111Part012SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block111Part012] using hcert

def TailChunk001Sub000Block111Part013SupportExplicit : Finset ℕ :=
  ([21085] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block111Part013 : ℚ :=
  (370722220125 : ℚ) / 67413671167470862336

def SurrogateDiagonalTailChunk001Sub000Block111Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21085
    = surrogateDiagTailX0RatChunk001Sub000Block111Part013

theorem surrogateDiagonalTailChunk001Sub000Block111Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block111Part013CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block111Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block111Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block111Part013CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block111Part013SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block111Part013] using hcert

def TailChunk001Sub000Block111Part014SupportExplicit : Finset ℕ :=
  ([21086] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block111Part014 : ℚ :=
  (399270595 : ℚ) / 35711813200693248

def SurrogateDiagonalTailChunk001Sub000Block111Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21086
    = surrogateDiagTailX0RatChunk001Sub000Block111Part014

theorem surrogateDiagonalTailChunk001Sub000Block111Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block111Part014CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block111Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block111Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block111Part014CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block111Part014SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block111Part014] using hcert

def TailChunk001Sub000Block111Part015SupportExplicit : Finset ℕ :=
  ([21089] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block111Part015 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block111Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21089
    = surrogateDiagTailX0RatChunk001Sub000Block111Part015

theorem surrogateDiagonalTailChunk001Sub000Block111Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block111Part015CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block111Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block111Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block111Part015CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block111Part015SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block111Part015] using hcert

def TailChunk001Sub000Block111Part016SupportExplicit : Finset ℕ :=
  ([21090] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block111Part016 : ℚ :=
  (863820957175 : ℚ) / 1805871442839994368

def SurrogateDiagonalTailChunk001Sub000Block111Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21090
    = surrogateDiagTailX0RatChunk001Sub000Block111Part016

theorem surrogateDiagonalTailChunk001Sub000Block111Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block111Part016CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block111Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block111Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block111Part016CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block111Part016SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block111Part016] using hcert

def TailChunk001Sub000Block111Part017SupportExplicit : Finset ℕ :=
  ([21091] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block111Part017 : ℚ :=
  (4677395831 : ℚ) / 788430287102515200

def SurrogateDiagonalTailChunk001Sub000Block111Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21091
    = surrogateDiagTailX0RatChunk001Sub000Block111Part017

theorem surrogateDiagonalTailChunk001Sub000Block111Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block111Part017CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block111Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block111Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block111Part017CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block111Part017SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block111Part017] using hcert

def TailChunk001Sub000Block111Part018SupportExplicit : Finset ℕ :=
  ([21093] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block111Part018 : ℚ :=
  (6913175 : ℚ) / 5919401955557376

def SurrogateDiagonalTailChunk001Sub000Block111Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21093
    = surrogateDiagTailX0RatChunk001Sub000Block111Part018

theorem surrogateDiagonalTailChunk001Sub000Block111Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block111Part018CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block111Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block111Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block111Part018CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block111Part018SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block111Part018] using hcert

def TailChunk001Sub000Block111Part019SupportExplicit : Finset ℕ :=
  ([21094] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block111Part019 : ℚ :=
  (38659104875 : ℚ) / 14049827716166820864

def SurrogateDiagonalTailChunk001Sub000Block111Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21094
    = surrogateDiagTailX0RatChunk001Sub000Block111Part019

theorem surrogateDiagonalTailChunk001Sub000Block111Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block111Part019CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block111Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block111Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block111Part019CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block111Part019SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block111Part019] using hcert

def TailChunk001Sub000Block111Part020SupportExplicit : Finset ℕ :=
  ([21095] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block111Part020 : ℚ :=
  (30087051625 : ℚ) / 5476352586513721344

def SurrogateDiagonalTailChunk001Sub000Block111Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21095
    = surrogateDiagTailX0RatChunk001Sub000Block111Part020

theorem surrogateDiagonalTailChunk001Sub000Block111Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block111Part020CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block111Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block111Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block111Part020CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block111Part020SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block111Part020] using hcert

def TailChunk001Sub000Block111Part021SupportExplicit : Finset ℕ :=
  ([21098] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block111Part021 : ℚ :=
  (1602902977 : ℚ) / 24636271421030400

def SurrogateDiagonalTailChunk001Sub000Block111Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21098
    = surrogateDiagTailX0RatChunk001Sub000Block111Part021

theorem surrogateDiagonalTailChunk001Sub000Block111Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block111Part021CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block111Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block111Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block111Part021CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block111Part021SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block111Part021] using hcert

def TailChunk001Sub000Block111Part022SupportExplicit : Finset ℕ :=
  ([21099] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block111Part022 : ℚ :=
  (13424561791 : ℚ) / 2821674129437491200

def SurrogateDiagonalTailChunk001Sub000Block111Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21099
    = surrogateDiagTailX0RatChunk001Sub000Block111Part022

theorem surrogateDiagonalTailChunk001Sub000Block111Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block111Part022CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block111Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block111Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block111Part022CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block111Part022SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block111Part022] using hcert

def TailChunk001Sub000Block111Part023SupportExplicit : Finset ℕ :=
  ([21101] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block111Part023 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block111Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21101
    = surrogateDiagTailX0RatChunk001Sub000Block111Part023

theorem surrogateDiagonalTailChunk001Sub000Block111Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block111Part023CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block111Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block111Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block111Part023CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block111Part023SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block111Part023] using hcert

def TailChunk001Sub000Block111Part024SupportExplicit : Finset ℕ :=
  ([21102] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block111Part024 : ℚ :=
  (48329131225 : ℚ) / 382139846210544768

def SurrogateDiagonalTailChunk001Sub000Block111Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21102
    = surrogateDiagTailX0RatChunk001Sub000Block111Part024

theorem surrogateDiagonalTailChunk001Sub000Block111Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block111Part024CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block111Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block111Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block111Part024CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block111Part024SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block111Part024] using hcert

def surrogateDiagonalTailChunk001Sub000Block111HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block111Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block111Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block111Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block111Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block111Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block111Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block111Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block111Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block111Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block111Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block111Head : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block111Part000
    + surrogateDiagTailX0RatChunk001Sub000Block111Part001
    + surrogateDiagTailX0RatChunk001Sub000Block111Part002
    + surrogateDiagTailX0RatChunk001Sub000Block111Part003
    + surrogateDiagTailX0RatChunk001Sub000Block111Part004
    + surrogateDiagTailX0RatChunk001Sub000Block111Part005
    + surrogateDiagTailX0RatChunk001Sub000Block111Part006
    + surrogateDiagTailX0RatChunk001Sub000Block111Part007
    + surrogateDiagTailX0RatChunk001Sub000Block111Part008
    + surrogateDiagTailX0RatChunk001Sub000Block111Part009

def surrogateDiagonalTailChunk001Sub000Block111MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block111Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block111Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block111Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block111Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block111Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block111Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block111Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block111Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block111Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block111Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block111Mid : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block111Part010
    + surrogateDiagTailX0RatChunk001Sub000Block111Part011
    + surrogateDiagTailX0RatChunk001Sub000Block111Part012
    + surrogateDiagTailX0RatChunk001Sub000Block111Part013
    + surrogateDiagTailX0RatChunk001Sub000Block111Part014
    + surrogateDiagTailX0RatChunk001Sub000Block111Part015
    + surrogateDiagTailX0RatChunk001Sub000Block111Part016
    + surrogateDiagTailX0RatChunk001Sub000Block111Part017
    + surrogateDiagTailX0RatChunk001Sub000Block111Part018
    + surrogateDiagTailX0RatChunk001Sub000Block111Part019

def surrogateDiagonalTailChunk001Sub000Block111TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block111Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block111Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block111Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block111Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block111Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block111Tail : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block111Part020
    + surrogateDiagTailX0RatChunk001Sub000Block111Part021
    + surrogateDiagTailX0RatChunk001Sub000Block111Part022
    + surrogateDiagTailX0RatChunk001Sub000Block111Part023
    + surrogateDiagTailX0RatChunk001Sub000Block111Part024

def surrogateDiagonalTailChunk001Sub000Block111Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk001Sub000Block111HeadSum X0
    + surrogateDiagonalTailChunk001Sub000Block111MidSum X0
    + surrogateDiagonalTailChunk001Sub000Block111TailSum X0

def surrogateDiagTailX0RatChunk001Sub000Block111 : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block111Part000
    + surrogateDiagTailX0RatChunk001Sub000Block111Part001
    + surrogateDiagTailX0RatChunk001Sub000Block111Part002
    + surrogateDiagTailX0RatChunk001Sub000Block111Part003
    + surrogateDiagTailX0RatChunk001Sub000Block111Part004
    + surrogateDiagTailX0RatChunk001Sub000Block111Part005
    + surrogateDiagTailX0RatChunk001Sub000Block111Part006
    + surrogateDiagTailX0RatChunk001Sub000Block111Part007
    + surrogateDiagTailX0RatChunk001Sub000Block111Part008
    + surrogateDiagTailX0RatChunk001Sub000Block111Part009
    + surrogateDiagTailX0RatChunk001Sub000Block111Part010
    + surrogateDiagTailX0RatChunk001Sub000Block111Part011
    + surrogateDiagTailX0RatChunk001Sub000Block111Part012
    + surrogateDiagTailX0RatChunk001Sub000Block111Part013
    + surrogateDiagTailX0RatChunk001Sub000Block111Part014
    + surrogateDiagTailX0RatChunk001Sub000Block111Part015
    + surrogateDiagTailX0RatChunk001Sub000Block111Part016
    + surrogateDiagTailX0RatChunk001Sub000Block111Part017
    + surrogateDiagTailX0RatChunk001Sub000Block111Part018
    + surrogateDiagTailX0RatChunk001Sub000Block111Part019
    + surrogateDiagTailX0RatChunk001Sub000Block111Part020
    + surrogateDiagTailX0RatChunk001Sub000Block111Part021
    + surrogateDiagTailX0RatChunk001Sub000Block111Part022
    + surrogateDiagTailX0RatChunk001Sub000Block111Part023
    + surrogateDiagTailX0RatChunk001Sub000Block111Part024

theorem surrogateDiagTailX0RatChunk001Sub000Block111_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk001Sub000Block111Head + surrogateDiagTailX0RatChunk001Sub000Block111Mid + surrogateDiagTailX0RatChunk001Sub000Block111Tail =
      surrogateDiagTailX0RatChunk001Sub000Block111 := by
  unfold surrogateDiagTailX0RatChunk001Sub000Block111Head surrogateDiagTailX0RatChunk001Sub000Block111Mid surrogateDiagTailX0RatChunk001Sub000Block111Tail surrogateDiagTailX0RatChunk001Sub000Block111
  ring

def SurrogateDiagonalTailChunk001Sub000Block111HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block111HeadSum X0 = surrogateDiagTailX0RatChunk001Sub000Block111Head

def SurrogateDiagonalTailChunk001Sub000Block111MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block111MidSum X0 = surrogateDiagTailX0RatChunk001Sub000Block111Mid

def SurrogateDiagonalTailChunk001Sub000Block111TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block111TailSum X0 = surrogateDiagTailX0RatChunk001Sub000Block111Tail

theorem surrogateDiagonalTailChunk001Sub000Block111_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk001Sub000Block111HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk001Sub000Block111MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk001Sub000Block111TailCertificateAt X0) :
    surrogateDiagonalTailChunk001Sub000Block111Sum X0 = surrogateDiagTailX0RatChunk001Sub000Block111 := by
  unfold SurrogateDiagonalTailChunk001Sub000Block111HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk001Sub000Block111MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk001Sub000Block111TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk001Sub000Block111Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk001Sub000Block111_eq_head_add_mid_add_tail

/-- Block 112 covers tail-support indices [12800,12825) and q from 21103 to 21145. -/

def TailChunk001Sub000Block112Part000SupportExplicit : Finset ℕ :=
  ([21103] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block112Part000 : ℚ :=
  (47900325 : ℚ) / 142089936177201152

def SurrogateDiagonalTailChunk001Sub000Block112Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21103
    = surrogateDiagTailX0RatChunk001Sub000Block112Part000

theorem surrogateDiagonalTailChunk001Sub000Block112Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block112Part000CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block112Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block112Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block112Part000CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block112Part000SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block112Part000] using hcert

def TailChunk001Sub000Block112Part001SupportExplicit : Finset ℕ :=
  ([21106] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block112Part001 : ℚ :=
  (2883053851 : ℚ) / 1134502975800115200

def SurrogateDiagonalTailChunk001Sub000Block112Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21106
    = surrogateDiagTailX0RatChunk001Sub000Block112Part001

theorem surrogateDiagonalTailChunk001Sub000Block112Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block112Part001CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block112Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block112Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block112Part001CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block112Part001SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block112Part001] using hcert

def TailChunk001Sub000Block112Part002SupportExplicit : Finset ℕ :=
  ([21107] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block112Part002 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block112Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21107
    = surrogateDiagTailX0RatChunk001Sub000Block112Part002

theorem surrogateDiagonalTailChunk001Sub000Block112Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block112Part002CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block112Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block112Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block112Part002CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block112Part002SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block112Part002] using hcert

def TailChunk001Sub000Block112Part003SupportExplicit : Finset ℕ :=
  ([21109] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block112Part003 : ℚ :=
  (1567572989 : ℚ) / 437487480000000000

def SurrogateDiagonalTailChunk001Sub000Block112Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21109
    = surrogateDiagTailX0RatChunk001Sub000Block112Part003

theorem surrogateDiagonalTailChunk001Sub000Block112Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block112Part003CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block112Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block112Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block112Part003CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block112Part003SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block112Part003] using hcert

def TailChunk001Sub000Block112Part004SupportExplicit : Finset ℕ :=
  ([21110] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block112Part004 : ℚ :=
  (261151499 : ℚ) / 3965031729776400

def SurrogateDiagonalTailChunk001Sub000Block112Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21110
    = surrogateDiagTailX0RatChunk001Sub000Block112Part004

theorem surrogateDiagonalTailChunk001Sub000Block112Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block112Part004CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block112Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block112Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block112Part004CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block112Part004SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block112Part004] using hcert

def TailChunk001Sub000Block112Part005SupportExplicit : Finset ℕ :=
  ([21111] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block112Part005 : ℚ :=
  (3121369547 : ℚ) / 1690813133855769600

def SurrogateDiagonalTailChunk001Sub000Block112Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21111
    = surrogateDiagTailX0RatChunk001Sub000Block112Part005

theorem surrogateDiagonalTailChunk001Sub000Block112Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block112Part005CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block112Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block112Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block112Part005CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block112Part005SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block112Part005] using hcert

def TailChunk001Sub000Block112Part006SupportExplicit : Finset ℕ :=
  ([21113] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block112Part006 : ℚ :=
  (6519759331 : ℚ) / 17941895874138499200

def SurrogateDiagonalTailChunk001Sub000Block112Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21113
    = surrogateDiagTailX0RatChunk001Sub000Block112Part006

theorem surrogateDiagonalTailChunk001Sub000Block112Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block112Part006CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block112Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block112Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block112Part006CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block112Part006SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block112Part006] using hcert

def TailChunk001Sub000Block112Part007SupportExplicit : Finset ℕ :=
  ([21115] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block112Part007 : ℚ :=
  (24356312069 : ℚ) / 3547623084628377600

def SurrogateDiagonalTailChunk001Sub000Block112Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21115
    = surrogateDiagTailX0RatChunk001Sub000Block112Part007

theorem surrogateDiagonalTailChunk001Sub000Block112Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block112Part007CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block112Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block112Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block112Part007CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block112Part007SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block112Part007] using hcert

def TailChunk001Sub000Block112Part008SupportExplicit : Finset ℕ :=
  ([21117] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block112Part008 : ℚ :=
  (41675 : ℚ) / 6542832198669696

def SurrogateDiagonalTailChunk001Sub000Block112Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21117
    = surrogateDiagTailX0RatChunk001Sub000Block112Part008

theorem surrogateDiagonalTailChunk001Sub000Block112Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block112Part008CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block112Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block112Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block112Part008CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block112Part008SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block112Part008] using hcert

def TailChunk001Sub000Block112Part009SupportExplicit : Finset ℕ :=
  ([21118] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block112Part009 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block112Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21118
    = surrogateDiagTailX0RatChunk001Sub000Block112Part009

theorem surrogateDiagonalTailChunk001Sub000Block112Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block112Part009CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block112Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block112Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block112Part009CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block112Part009SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block112Part009] using hcert

def TailChunk001Sub000Block112Part010SupportExplicit : Finset ℕ :=
  ([21121] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block112Part010 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block112Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21121
    = surrogateDiagTailX0RatChunk001Sub000Block112Part010

theorem surrogateDiagonalTailChunk001Sub000Block112Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block112Part010CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block112Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block112Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block112Part010CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block112Part010SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block112Part010] using hcert

def TailChunk001Sub000Block112Part011SupportExplicit : Finset ℕ :=
  ([21122] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block112Part011 : ℚ :=
  (18330679075 : ℚ) / 7101643237713975072

def SurrogateDiagonalTailChunk001Sub000Block112Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21122
    = surrogateDiagTailX0RatChunk001Sub000Block112Part011

theorem surrogateDiagonalTailChunk001Sub000Block112Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block112Part011CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block112Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block112Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block112Part011CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block112Part011SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block112Part011] using hcert

def TailChunk001Sub000Block112Part012SupportExplicit : Finset ℕ :=
  ([21126] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block112Part012 : ℚ :=
  (419260773125 : ℚ) / 1646405150321746944

def SurrogateDiagonalTailChunk001Sub000Block112Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21126
    = surrogateDiagTailX0RatChunk001Sub000Block112Part012

theorem surrogateDiagonalTailChunk001Sub000Block112Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block112Part012CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block112Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block112Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block112Part012CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block112Part012SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block112Part012] using hcert

def TailChunk001Sub000Block112Part013SupportExplicit : Finset ℕ :=
  ([21127] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block112Part013 : ℚ :=
  (143484641 : ℚ) / 328399521875020800

def SurrogateDiagonalTailChunk001Sub000Block112Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21127
    = surrogateDiagTailX0RatChunk001Sub000Block112Part013

theorem surrogateDiagonalTailChunk001Sub000Block112Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block112Part013CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block112Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block112Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block112Part013CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block112Part013SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block112Part013] using hcert

def TailChunk001Sub000Block112Part014SupportExplicit : Finset ℕ :=
  ([21129] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block112Part014 : ℚ :=
  (221427518675 : ℚ) / 7027532921469746112

def SurrogateDiagonalTailChunk001Sub000Block112Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21129
    = surrogateDiagTailX0RatChunk001Sub000Block112Part014

theorem surrogateDiagonalTailChunk001Sub000Block112Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block112Part014CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block112Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block112Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block112Part014CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block112Part014SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block112Part014] using hcert

def TailChunk001Sub000Block112Part015SupportExplicit : Finset ℕ :=
  ([21130] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block112Part015 : ℚ :=
  (186235659175 : ℚ) / 4245425507518119936

def SurrogateDiagonalTailChunk001Sub000Block112Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21130
    = surrogateDiagTailX0RatChunk001Sub000Block112Part015

theorem surrogateDiagonalTailChunk001Sub000Block112Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block112Part015CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block112Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block112Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block112Part015CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block112Part015SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block112Part015] using hcert

def TailChunk001Sub000Block112Part016SupportExplicit : Finset ℕ :=
  ([21131] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block112Part016 : ℚ :=
  (3979599803 : ℚ) / 1289284865123942400

def SurrogateDiagonalTailChunk001Sub000Block112Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21131
    = surrogateDiagTailX0RatChunk001Sub000Block112Part016

theorem surrogateDiagonalTailChunk001Sub000Block112Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block112Part016CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block112Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block112Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block112Part016CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block112Part016SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block112Part016] using hcert

def TailChunk001Sub000Block112Part017SupportExplicit : Finset ℕ :=
  ([21133] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block112Part017 : ℚ :=
  (570093815075 : ℚ) / 134424616611553948224

def SurrogateDiagonalTailChunk001Sub000Block112Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21133
    = surrogateDiagTailX0RatChunk001Sub000Block112Part017

theorem surrogateDiagonalTailChunk001Sub000Block112Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block112Part017CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block112Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block112Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block112Part017CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block112Part017SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block112Part017] using hcert

def TailChunk001Sub000Block112Part018SupportExplicit : Finset ℕ :=
  ([21134] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block112Part018 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block112Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21134
    = surrogateDiagTailX0RatChunk001Sub000Block112Part018

theorem surrogateDiagonalTailChunk001Sub000Block112Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block112Part018CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block112Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block112Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block112Part018CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block112Part018SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block112Part018] using hcert

def TailChunk001Sub000Block112Part019SupportExplicit : Finset ℕ :=
  ([21135] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block112Part019 : ℚ :=
  (682134194725 : ℚ) / 10063230832635543552

def SurrogateDiagonalTailChunk001Sub000Block112Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21135
    = surrogateDiagTailX0RatChunk001Sub000Block112Part019

theorem surrogateDiagonalTailChunk001Sub000Block112Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block112Part019CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block112Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block112Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block112Part019CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block112Part019SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block112Part019] using hcert

def TailChunk001Sub000Block112Part020SupportExplicit : Finset ℕ :=
  ([21137] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block112Part020 : ℚ :=
  (270005452525 : ℚ) / 415995187997791974528

def SurrogateDiagonalTailChunk001Sub000Block112Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21137
    = surrogateDiagTailX0RatChunk001Sub000Block112Part020

theorem surrogateDiagonalTailChunk001Sub000Block112Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block112Part020CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block112Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block112Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block112Part020CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block112Part020SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block112Part020] using hcert

def TailChunk001Sub000Block112Part021SupportExplicit : Finset ℕ :=
  ([21138] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block112Part021 : ℚ :=
  (58970682679 : ℚ) / 176354633089843200

def SurrogateDiagonalTailChunk001Sub000Block112Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21138
    = surrogateDiagTailX0RatChunk001Sub000Block112Part021

theorem surrogateDiagonalTailChunk001Sub000Block112Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block112Part021CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block112Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block112Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block112Part021CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block112Part021SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block112Part021] using hcert

def TailChunk001Sub000Block112Part022SupportExplicit : Finset ℕ :=
  ([21139] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block112Part022 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block112Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21139
    = surrogateDiagTailX0RatChunk001Sub000Block112Part022

theorem surrogateDiagonalTailChunk001Sub000Block112Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block112Part022CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block112Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block112Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block112Part022CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block112Part022SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block112Part022] using hcert

def TailChunk001Sub000Block112Part023SupportExplicit : Finset ℕ :=
  ([21143] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block112Part023 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block112Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21143
    = surrogateDiagTailX0RatChunk001Sub000Block112Part023

theorem surrogateDiagonalTailChunk001Sub000Block112Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block112Part023CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block112Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block112Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block112Part023CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block112Part023SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block112Part023] using hcert

def TailChunk001Sub000Block112Part024SupportExplicit : Finset ℕ :=
  ([21145] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block112Part024 : ℚ :=
  (372833219625 : ℚ) / 68184472347530592256

def SurrogateDiagonalTailChunk001Sub000Block112Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21145
    = surrogateDiagTailX0RatChunk001Sub000Block112Part024

theorem surrogateDiagonalTailChunk001Sub000Block112Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block112Part024CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block112Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block112Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block112Part024CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block112Part024SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block112Part024] using hcert

def surrogateDiagonalTailChunk001Sub000Block112HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block112Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block112Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block112Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block112Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block112Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block112Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block112Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block112Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block112Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block112Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block112Head : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block112Part000
    + surrogateDiagTailX0RatChunk001Sub000Block112Part001
    + surrogateDiagTailX0RatChunk001Sub000Block112Part002
    + surrogateDiagTailX0RatChunk001Sub000Block112Part003
    + surrogateDiagTailX0RatChunk001Sub000Block112Part004
    + surrogateDiagTailX0RatChunk001Sub000Block112Part005
    + surrogateDiagTailX0RatChunk001Sub000Block112Part006
    + surrogateDiagTailX0RatChunk001Sub000Block112Part007
    + surrogateDiagTailX0RatChunk001Sub000Block112Part008
    + surrogateDiagTailX0RatChunk001Sub000Block112Part009

def surrogateDiagonalTailChunk001Sub000Block112MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block112Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block112Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block112Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block112Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block112Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block112Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block112Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block112Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block112Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block112Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block112Mid : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block112Part010
    + surrogateDiagTailX0RatChunk001Sub000Block112Part011
    + surrogateDiagTailX0RatChunk001Sub000Block112Part012
    + surrogateDiagTailX0RatChunk001Sub000Block112Part013
    + surrogateDiagTailX0RatChunk001Sub000Block112Part014
    + surrogateDiagTailX0RatChunk001Sub000Block112Part015
    + surrogateDiagTailX0RatChunk001Sub000Block112Part016
    + surrogateDiagTailX0RatChunk001Sub000Block112Part017
    + surrogateDiagTailX0RatChunk001Sub000Block112Part018
    + surrogateDiagTailX0RatChunk001Sub000Block112Part019

def surrogateDiagonalTailChunk001Sub000Block112TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block112Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block112Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block112Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block112Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block112Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block112Tail : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block112Part020
    + surrogateDiagTailX0RatChunk001Sub000Block112Part021
    + surrogateDiagTailX0RatChunk001Sub000Block112Part022
    + surrogateDiagTailX0RatChunk001Sub000Block112Part023
    + surrogateDiagTailX0RatChunk001Sub000Block112Part024

def surrogateDiagonalTailChunk001Sub000Block112Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk001Sub000Block112HeadSum X0
    + surrogateDiagonalTailChunk001Sub000Block112MidSum X0
    + surrogateDiagonalTailChunk001Sub000Block112TailSum X0

def surrogateDiagTailX0RatChunk001Sub000Block112 : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block112Part000
    + surrogateDiagTailX0RatChunk001Sub000Block112Part001
    + surrogateDiagTailX0RatChunk001Sub000Block112Part002
    + surrogateDiagTailX0RatChunk001Sub000Block112Part003
    + surrogateDiagTailX0RatChunk001Sub000Block112Part004
    + surrogateDiagTailX0RatChunk001Sub000Block112Part005
    + surrogateDiagTailX0RatChunk001Sub000Block112Part006
    + surrogateDiagTailX0RatChunk001Sub000Block112Part007
    + surrogateDiagTailX0RatChunk001Sub000Block112Part008
    + surrogateDiagTailX0RatChunk001Sub000Block112Part009
    + surrogateDiagTailX0RatChunk001Sub000Block112Part010
    + surrogateDiagTailX0RatChunk001Sub000Block112Part011
    + surrogateDiagTailX0RatChunk001Sub000Block112Part012
    + surrogateDiagTailX0RatChunk001Sub000Block112Part013
    + surrogateDiagTailX0RatChunk001Sub000Block112Part014
    + surrogateDiagTailX0RatChunk001Sub000Block112Part015
    + surrogateDiagTailX0RatChunk001Sub000Block112Part016
    + surrogateDiagTailX0RatChunk001Sub000Block112Part017
    + surrogateDiagTailX0RatChunk001Sub000Block112Part018
    + surrogateDiagTailX0RatChunk001Sub000Block112Part019
    + surrogateDiagTailX0RatChunk001Sub000Block112Part020
    + surrogateDiagTailX0RatChunk001Sub000Block112Part021
    + surrogateDiagTailX0RatChunk001Sub000Block112Part022
    + surrogateDiagTailX0RatChunk001Sub000Block112Part023
    + surrogateDiagTailX0RatChunk001Sub000Block112Part024

theorem surrogateDiagTailX0RatChunk001Sub000Block112_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk001Sub000Block112Head + surrogateDiagTailX0RatChunk001Sub000Block112Mid + surrogateDiagTailX0RatChunk001Sub000Block112Tail =
      surrogateDiagTailX0RatChunk001Sub000Block112 := by
  unfold surrogateDiagTailX0RatChunk001Sub000Block112Head surrogateDiagTailX0RatChunk001Sub000Block112Mid surrogateDiagTailX0RatChunk001Sub000Block112Tail surrogateDiagTailX0RatChunk001Sub000Block112
  ring

def SurrogateDiagonalTailChunk001Sub000Block112HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block112HeadSum X0 = surrogateDiagTailX0RatChunk001Sub000Block112Head

def SurrogateDiagonalTailChunk001Sub000Block112MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block112MidSum X0 = surrogateDiagTailX0RatChunk001Sub000Block112Mid

def SurrogateDiagonalTailChunk001Sub000Block112TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block112TailSum X0 = surrogateDiagTailX0RatChunk001Sub000Block112Tail

theorem surrogateDiagonalTailChunk001Sub000Block112_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk001Sub000Block112HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk001Sub000Block112MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk001Sub000Block112TailCertificateAt X0) :
    surrogateDiagonalTailChunk001Sub000Block112Sum X0 = surrogateDiagTailX0RatChunk001Sub000Block112 := by
  unfold SurrogateDiagonalTailChunk001Sub000Block112HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk001Sub000Block112MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk001Sub000Block112TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk001Sub000Block112Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk001Sub000Block112_eq_head_add_mid_add_tail

/-- Block 113 covers tail-support indices [12825,12850) and q from 21146 to 21183. -/

def TailChunk001Sub000Block113Part000SupportExplicit : Finset ℕ :=
  ([21146] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block113Part000 : ℚ :=
  (63485530375 : ℚ) / 28893943085439909888

def SurrogateDiagonalTailChunk001Sub000Block113Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21146
    = surrogateDiagTailX0RatChunk001Sub000Block113Part000

theorem surrogateDiagonalTailChunk001Sub000Block113Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block113Part000CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block113Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block113Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block113Part000CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block113Part000SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block113Part000] using hcert

def TailChunk001Sub000Block113Part001SupportExplicit : Finset ℕ :=
  ([21147] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block113Part001 : ℚ :=
  (1380980498525 : ℚ) / 19898724644657823744

def SurrogateDiagonalTailChunk001Sub000Block113Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21147
    = surrogateDiagTailX0RatChunk001Sub000Block113Part001

theorem surrogateDiagonalTailChunk001Sub000Block113Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block113Part001CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block113Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block113Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block113Part001CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block113Part001SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block113Part001] using hcert

def TailChunk001Sub000Block113Part002SupportExplicit : Finset ℕ :=
  ([21149] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block113Part002 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block113Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21149
    = surrogateDiagTailX0RatChunk001Sub000Block113Part002

theorem surrogateDiagonalTailChunk001Sub000Block113Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block113Part002CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block113Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block113Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block113Part002CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block113Part002SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block113Part002] using hcert

def TailChunk001Sub000Block113Part003SupportExplicit : Finset ℕ :=
  ([21151] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block113Part003 : ℚ :=
  (62410208525 : ℚ) / 45304779509949655296

def SurrogateDiagonalTailChunk001Sub000Block113Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21151
    = surrogateDiagTailX0RatChunk001Sub000Block113Part003

theorem surrogateDiagonalTailChunk001Sub000Block113Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block113Part003CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block113Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block113Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block113Part003CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block113Part003SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block113Part003] using hcert

def TailChunk001Sub000Block113Part004SupportExplicit : Finset ℕ :=
  ([21153] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block113Part004 : ℚ :=
  (114940570519 : ℚ) / 2684891430912000000

def SurrogateDiagonalTailChunk001Sub000Block113Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21153
    = surrogateDiagTailX0RatChunk001Sub000Block113Part004

theorem surrogateDiagonalTailChunk001Sub000Block113Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block113Part004CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block113Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block113Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block113Part004CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block113Part004SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block113Part004] using hcert

def TailChunk001Sub000Block113Part005SupportExplicit : Finset ℕ :=
  ([21154] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block113Part005 : ℚ :=
  (22862295853 : ℚ) / 673906493243779200

def SurrogateDiagonalTailChunk001Sub000Block113Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21154
    = surrogateDiagTailX0RatChunk001Sub000Block113Part005

theorem surrogateDiagonalTailChunk001Sub000Block113Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block113Part005CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block113Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block113Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block113Part005CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block113Part005SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block113Part005] using hcert

def TailChunk001Sub000Block113Part006SupportExplicit : Finset ℕ :=
  ([21155] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block113Part006 : ℚ :=
  (8956455269 : ℚ) / 1639525896110499840

def SurrogateDiagonalTailChunk001Sub000Block113Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21155
    = surrogateDiagTailX0RatChunk001Sub000Block113Part006

theorem surrogateDiagonalTailChunk001Sub000Block113Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block113Part006CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block113Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block113Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block113Part006CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block113Part006SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block113Part006] using hcert

def TailChunk001Sub000Block113Part007SupportExplicit : Finset ℕ :=
  ([21157] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block113Part007 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block113Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21157
    = surrogateDiagTailX0RatChunk001Sub000Block113Part007

theorem surrogateDiagonalTailChunk001Sub000Block113Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block113Part007CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block113Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block113Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block113Part007CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block113Part007SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block113Part007] using hcert

def TailChunk001Sub000Block113Part008SupportExplicit : Finset ℕ :=
  ([21158] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block113Part008 : ℚ :=
  (679863301 : ℚ) / 288048674119180800

def SurrogateDiagonalTailChunk001Sub000Block113Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21158
    = surrogateDiagTailX0RatChunk001Sub000Block113Part008

theorem surrogateDiagonalTailChunk001Sub000Block113Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block113Part008CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block113Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block113Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block113Part008CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block113Part008SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block113Part008] using hcert

def TailChunk001Sub000Block113Part009SupportExplicit : Finset ℕ :=
  ([21161] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block113Part009 : ℚ :=
  (571603513175 : ℚ) / 135138690030154042944

def SurrogateDiagonalTailChunk001Sub000Block113Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21161
    = surrogateDiagTailX0RatChunk001Sub000Block113Part009

theorem surrogateDiagonalTailChunk001Sub000Block113Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block113Part009CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block113Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block113Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block113Part009CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block113Part009SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block113Part009] using hcert

def TailChunk001Sub000Block113Part010SupportExplicit : Finset ℕ :=
  ([21162] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block113Part010 : ℚ :=
  (18956078725 : ℚ) / 75415778930478144

def SurrogateDiagonalTailChunk001Sub000Block113Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21162
    = surrogateDiagTailX0RatChunk001Sub000Block113Part010

theorem surrogateDiagonalTailChunk001Sub000Block113Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block113Part010CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block113Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block113Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block113Part010CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block113Part010SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block113Part010] using hcert

def TailChunk001Sub000Block113Part011SupportExplicit : Finset ℕ :=
  ([21163] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block113Part011 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block113Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21163
    = surrogateDiagTailX0RatChunk001Sub000Block113Part011

theorem surrogateDiagonalTailChunk001Sub000Block113Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block113Part011CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block113Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block113Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block113Part011CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block113Part011SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block113Part011] using hcert

def TailChunk001Sub000Block113Part012SupportExplicit : Finset ℕ :=
  ([21165] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block113Part012 : ℚ :=
  (2491973266525 : ℚ) / 30347445978821296128

def SurrogateDiagonalTailChunk001Sub000Block113Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21165
    = surrogateDiagTailX0RatChunk001Sub000Block113Part012

theorem surrogateDiagonalTailChunk001Sub000Block113Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block113Part012CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block113Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block113Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block113Part012CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block113Part012SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block113Part012] using hcert

def TailChunk001Sub000Block113Part013SupportExplicit : Finset ℕ :=
  ([21166] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block113Part013 : ℚ :=
  (89616294275 : ℚ) / 12542556035210241024

def SurrogateDiagonalTailChunk001Sub000Block113Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21166
    = surrogateDiagTailX0RatChunk001Sub000Block113Part013

theorem surrogateDiagonalTailChunk001Sub000Block113Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block113Part013CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block113Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block113Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block113Part013CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block113Part013SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block113Part013] using hcert

def TailChunk001Sub000Block113Part014SupportExplicit : Finset ℕ :=
  ([21167] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block113Part014 : ℚ :=
  (326694169 : ℚ) / 1161117750250627200

def SurrogateDiagonalTailChunk001Sub000Block113Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21167
    = surrogateDiagTailX0RatChunk001Sub000Block113Part014

theorem surrogateDiagonalTailChunk001Sub000Block113Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block113Part014CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block113Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block113Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block113Part014CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block113Part014SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block113Part014] using hcert

def TailChunk001Sub000Block113Part015SupportExplicit : Finset ℕ :=
  ([21169] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block113Part015 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block113Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21169
    = surrogateDiagTailX0RatChunk001Sub000Block113Part015

theorem surrogateDiagonalTailChunk001Sub000Block113Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block113Part015CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block113Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block113Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block113Part015CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block113Part015SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block113Part015] using hcert

def TailChunk001Sub000Block113Part016SupportExplicit : Finset ℕ :=
  ([21170] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block113Part016 : ℚ :=
  (631860454375 : ℚ) / 10573747500097732608

def SurrogateDiagonalTailChunk001Sub000Block113Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21170
    = surrogateDiagTailX0RatChunk001Sub000Block113Part016

theorem surrogateDiagonalTailChunk001Sub000Block113Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block113Part016CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block113Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block113Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block113Part016CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block113Part016SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block113Part016] using hcert

def TailChunk001Sub000Block113Part017SupportExplicit : Finset ℕ :=
  ([21171] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block113Part017 : ℚ :=
  (111154321825 : ℚ) / 3541792375521017856

def SurrogateDiagonalTailChunk001Sub000Block113Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21171
    = surrogateDiagTailX0RatChunk001Sub000Block113Part017

theorem surrogateDiagonalTailChunk001Sub000Block113Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block113Part017CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block113Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block113Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block113Part017CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block113Part017SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block113Part017] using hcert

def TailChunk001Sub000Block113Part018SupportExplicit : Finset ℕ :=
  ([21173] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block113Part018 : ℚ :=
  (106304051 : ℚ) / 219088398486113640

def SurrogateDiagonalTailChunk001Sub000Block113Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21173
    = surrogateDiagTailX0RatChunk001Sub000Block113Part018

theorem surrogateDiagonalTailChunk001Sub000Block113Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block113Part018CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block113Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block113Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block113Part018CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block113Part018SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block113Part018] using hcert

def TailChunk001Sub000Block113Part019SupportExplicit : Finset ℕ :=
  ([21174] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block113Part019 : ℚ :=
  (778080801275 : ℚ) / 3099068328580890624

def SurrogateDiagonalTailChunk001Sub000Block113Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21174
    = surrogateDiagTailX0RatChunk001Sub000Block113Part019

theorem surrogateDiagonalTailChunk001Sub000Block113Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block113Part019CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block113Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block113Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block113Part019CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block113Part019SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block113Part019] using hcert

def TailChunk001Sub000Block113Part020SupportExplicit : Finset ℕ :=
  ([21178] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block113Part020 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block113Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21178
    = surrogateDiagTailX0RatChunk001Sub000Block113Part020

theorem surrogateDiagonalTailChunk001Sub000Block113Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block113Part020CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block113Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block113Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block113Part020CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block113Part020SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block113Part020] using hcert

def TailChunk001Sub000Block113Part021SupportExplicit : Finset ℕ :=
  ([21179] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block113Part021 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block113Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21179
    = surrogateDiagTailX0RatChunk001Sub000Block113Part021

theorem surrogateDiagonalTailChunk001Sub000Block113Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block113Part021CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block113Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block113Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block113Part021CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block113Part021SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block113Part021] using hcert

def TailChunk001Sub000Block113Part022SupportExplicit : Finset ℕ :=
  ([21181] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block113Part022 : ℚ :=
  (43343223075 : ℚ) / 154935052981550436736

def SurrogateDiagonalTailChunk001Sub000Block113Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21181
    = surrogateDiagTailX0RatChunk001Sub000Block113Part022

theorem surrogateDiagonalTailChunk001Sub000Block113Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block113Part022CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block113Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block113Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block113Part022CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block113Part022SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block113Part022] using hcert

def TailChunk001Sub000Block113Part023SupportExplicit : Finset ℕ :=
  ([21182] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block113Part023 : ℚ :=
  (281576052425 : ℚ) / 6368138261277179904

def SurrogateDiagonalTailChunk001Sub000Block113Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21182
    = surrogateDiagTailX0RatChunk001Sub000Block113Part023

theorem surrogateDiagonalTailChunk001Sub000Block113Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block113Part023CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block113Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block113Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block113Part023CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block113Part023SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block113Part023] using hcert

def TailChunk001Sub000Block113Part024SupportExplicit : Finset ℕ :=
  ([21183] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block113Part024 : ℚ :=
  (1519576595825 : ℚ) / 41085944493609083904

def SurrogateDiagonalTailChunk001Sub000Block113Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21183
    = surrogateDiagTailX0RatChunk001Sub000Block113Part024

theorem surrogateDiagonalTailChunk001Sub000Block113Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block113Part024CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block113Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block113Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block113Part024CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block113Part024SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block113Part024] using hcert

def surrogateDiagonalTailChunk001Sub000Block113HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block113Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block113Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block113Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block113Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block113Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block113Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block113Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block113Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block113Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block113Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block113Head : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block113Part000
    + surrogateDiagTailX0RatChunk001Sub000Block113Part001
    + surrogateDiagTailX0RatChunk001Sub000Block113Part002
    + surrogateDiagTailX0RatChunk001Sub000Block113Part003
    + surrogateDiagTailX0RatChunk001Sub000Block113Part004
    + surrogateDiagTailX0RatChunk001Sub000Block113Part005
    + surrogateDiagTailX0RatChunk001Sub000Block113Part006
    + surrogateDiagTailX0RatChunk001Sub000Block113Part007
    + surrogateDiagTailX0RatChunk001Sub000Block113Part008
    + surrogateDiagTailX0RatChunk001Sub000Block113Part009

def surrogateDiagonalTailChunk001Sub000Block113MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block113Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block113Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block113Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block113Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block113Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block113Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block113Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block113Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block113Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block113Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block113Mid : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block113Part010
    + surrogateDiagTailX0RatChunk001Sub000Block113Part011
    + surrogateDiagTailX0RatChunk001Sub000Block113Part012
    + surrogateDiagTailX0RatChunk001Sub000Block113Part013
    + surrogateDiagTailX0RatChunk001Sub000Block113Part014
    + surrogateDiagTailX0RatChunk001Sub000Block113Part015
    + surrogateDiagTailX0RatChunk001Sub000Block113Part016
    + surrogateDiagTailX0RatChunk001Sub000Block113Part017
    + surrogateDiagTailX0RatChunk001Sub000Block113Part018
    + surrogateDiagTailX0RatChunk001Sub000Block113Part019

def surrogateDiagonalTailChunk001Sub000Block113TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block113Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block113Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block113Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block113Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block113Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block113Tail : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block113Part020
    + surrogateDiagTailX0RatChunk001Sub000Block113Part021
    + surrogateDiagTailX0RatChunk001Sub000Block113Part022
    + surrogateDiagTailX0RatChunk001Sub000Block113Part023
    + surrogateDiagTailX0RatChunk001Sub000Block113Part024

def surrogateDiagonalTailChunk001Sub000Block113Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk001Sub000Block113HeadSum X0
    + surrogateDiagonalTailChunk001Sub000Block113MidSum X0
    + surrogateDiagonalTailChunk001Sub000Block113TailSum X0

def surrogateDiagTailX0RatChunk001Sub000Block113 : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block113Part000
    + surrogateDiagTailX0RatChunk001Sub000Block113Part001
    + surrogateDiagTailX0RatChunk001Sub000Block113Part002
    + surrogateDiagTailX0RatChunk001Sub000Block113Part003
    + surrogateDiagTailX0RatChunk001Sub000Block113Part004
    + surrogateDiagTailX0RatChunk001Sub000Block113Part005
    + surrogateDiagTailX0RatChunk001Sub000Block113Part006
    + surrogateDiagTailX0RatChunk001Sub000Block113Part007
    + surrogateDiagTailX0RatChunk001Sub000Block113Part008
    + surrogateDiagTailX0RatChunk001Sub000Block113Part009
    + surrogateDiagTailX0RatChunk001Sub000Block113Part010
    + surrogateDiagTailX0RatChunk001Sub000Block113Part011
    + surrogateDiagTailX0RatChunk001Sub000Block113Part012
    + surrogateDiagTailX0RatChunk001Sub000Block113Part013
    + surrogateDiagTailX0RatChunk001Sub000Block113Part014
    + surrogateDiagTailX0RatChunk001Sub000Block113Part015
    + surrogateDiagTailX0RatChunk001Sub000Block113Part016
    + surrogateDiagTailX0RatChunk001Sub000Block113Part017
    + surrogateDiagTailX0RatChunk001Sub000Block113Part018
    + surrogateDiagTailX0RatChunk001Sub000Block113Part019
    + surrogateDiagTailX0RatChunk001Sub000Block113Part020
    + surrogateDiagTailX0RatChunk001Sub000Block113Part021
    + surrogateDiagTailX0RatChunk001Sub000Block113Part022
    + surrogateDiagTailX0RatChunk001Sub000Block113Part023
    + surrogateDiagTailX0RatChunk001Sub000Block113Part024

theorem surrogateDiagTailX0RatChunk001Sub000Block113_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk001Sub000Block113Head + surrogateDiagTailX0RatChunk001Sub000Block113Mid + surrogateDiagTailX0RatChunk001Sub000Block113Tail =
      surrogateDiagTailX0RatChunk001Sub000Block113 := by
  unfold surrogateDiagTailX0RatChunk001Sub000Block113Head surrogateDiagTailX0RatChunk001Sub000Block113Mid surrogateDiagTailX0RatChunk001Sub000Block113Tail surrogateDiagTailX0RatChunk001Sub000Block113
  ring

def SurrogateDiagonalTailChunk001Sub000Block113HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block113HeadSum X0 = surrogateDiagTailX0RatChunk001Sub000Block113Head

def SurrogateDiagonalTailChunk001Sub000Block113MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block113MidSum X0 = surrogateDiagTailX0RatChunk001Sub000Block113Mid

def SurrogateDiagonalTailChunk001Sub000Block113TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block113TailSum X0 = surrogateDiagTailX0RatChunk001Sub000Block113Tail

theorem surrogateDiagonalTailChunk001Sub000Block113_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk001Sub000Block113HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk001Sub000Block113MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk001Sub000Block113TailCertificateAt X0) :
    surrogateDiagonalTailChunk001Sub000Block113Sum X0 = surrogateDiagTailX0RatChunk001Sub000Block113 := by
  unfold SurrogateDiagonalTailChunk001Sub000Block113HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk001Sub000Block113MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk001Sub000Block113TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk001Sub000Block113Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk001Sub000Block113_eq_head_add_mid_add_tail

/-- Block 114 covers tail-support indices [12850,12875) and q from 21185 to 21226. -/

def TailChunk001Sub000Block114Part000SupportExplicit : Finset ℕ :=
  ([21185] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block114Part000 : ℚ :=
  (634931272625 : ℚ) / 81609129754640400384

def SurrogateDiagonalTailChunk001Sub000Block114Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21185
    = surrogateDiagTailX0RatChunk001Sub000Block114Part000

theorem surrogateDiagonalTailChunk001Sub000Block114Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block114Part000CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block114Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block114Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block114Part000CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block114Part000SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block114Part000] using hcert

def TailChunk001Sub000Block114Part001SupportExplicit : Finset ℕ :=
  ([21187] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block114Part001 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block114Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21187
    = surrogateDiagTailX0RatChunk001Sub000Block114Part001

theorem surrogateDiagonalTailChunk001Sub000Block114Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block114Part001CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block114Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block114Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block114Part001CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block114Part001SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block114Part001] using hcert

def TailChunk001Sub000Block114Part002SupportExplicit : Finset ℕ :=
  ([21189] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block114Part002 : ℚ :=
  (2734646920825 : ℚ) / 53529596719244771328

def SurrogateDiagonalTailChunk001Sub000Block114Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21189
    = surrogateDiagTailX0RatChunk001Sub000Block114Part002

theorem surrogateDiagonalTailChunk001Sub000Block114Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block114Part002CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block114Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block114Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block114Part002CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block114Part002SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block114Part002] using hcert

def TailChunk001Sub000Block114Part003SupportExplicit : Finset ℕ :=
  ([21190] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block114Part003 : ℚ :=
  (916822347325 : ℚ) / 9142224179377471488

def SurrogateDiagonalTailChunk001Sub000Block114Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21190
    = surrogateDiagTailX0RatChunk001Sub000Block114Part003

theorem surrogateDiagonalTailChunk001Sub000Block114Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block114Part003CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block114Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block114Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block114Part003CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block114Part003SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block114Part003] using hcert

def TailChunk001Sub000Block114Part004SupportExplicit : Finset ℕ :=
  ([21191] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block114Part004 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block114Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21191
    = surrogateDiagTailX0RatChunk001Sub000Block114Part004

theorem surrogateDiagonalTailChunk001Sub000Block114Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block114Part004CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block114Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block114Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block114Part004CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block114Part004SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block114Part004] using hcert

def TailChunk001Sub000Block114Part005SupportExplicit : Finset ℕ :=
  ([21193] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block114Part005 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block114Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21193
    = surrogateDiagTailX0RatChunk001Sub000Block114Part005

theorem surrogateDiagonalTailChunk001Sub000Block114Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block114Part005CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block114Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block114Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block114Part005CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block114Part005SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block114Part005] using hcert

def TailChunk001Sub000Block114Part006SupportExplicit : Finset ℕ :=
  ([21194] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block114Part006 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block114Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21194
    = surrogateDiagTailX0RatChunk001Sub000Block114Part006

theorem surrogateDiagonalTailChunk001Sub000Block114Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block114Part006CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block114Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block114Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block114Part006CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block114Part006SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block114Part006] using hcert

def TailChunk001Sub000Block114Part007SupportExplicit : Finset ℕ :=
  ([21197] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block114Part007 : ℚ :=
  (4449295631 : ℚ) / 1433072477184000000

def SurrogateDiagonalTailChunk001Sub000Block114Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21197
    = surrogateDiagTailX0RatChunk001Sub000Block114Part007

theorem surrogateDiagonalTailChunk001Sub000Block114Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block114Part007CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block114Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block114Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block114Part007CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block114Part007SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block114Part007] using hcert

def TailChunk001Sub000Block114Part008SupportExplicit : Finset ℕ :=
  ([21198] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block114Part008 : ℚ :=
  (1524050975 : ℚ) / 12160730394166884

def SurrogateDiagonalTailChunk001Sub000Block114Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21198
    = surrogateDiagTailX0RatChunk001Sub000Block114Part008

theorem surrogateDiagonalTailChunk001Sub000Block114Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block114Part008CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block114Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block114Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block114Part008CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block114Part008SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block114Part008] using hcert

def TailChunk001Sub000Block114Part009SupportExplicit : Finset ℕ :=
  ([21199] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block114Part009 : ℚ :=
  (76968181775 : ℚ) / 34825195813079089152

def SurrogateDiagonalTailChunk001Sub000Block114Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21199
    = surrogateDiagTailX0RatChunk001Sub000Block114Part009

theorem surrogateDiagonalTailChunk001Sub000Block114Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block114Part009CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block114Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block114Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block114Part009CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block114Part009SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block114Part009] using hcert

def TailChunk001Sub000Block114Part010SupportExplicit : Finset ℕ :=
  ([21201] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block114Part010 : ℚ :=
  (12255093127 : ℚ) / 350292823333355520

def SurrogateDiagonalTailChunk001Sub000Block114Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21201
    = surrogateDiagTailX0RatChunk001Sub000Block114Part010

theorem surrogateDiagonalTailChunk001Sub000Block114Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block114Part010CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block114Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block114Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block114Part010CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block114Part010SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block114Part010] using hcert

def TailChunk001Sub000Block114Part011SupportExplicit : Finset ℕ :=
  ([21202] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block114Part011 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block114Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21202
    = surrogateDiagTailX0RatChunk001Sub000Block114Part011

theorem surrogateDiagonalTailChunk001Sub000Block114Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block114Part011CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block114Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block114Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block114Part011CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block114Part011SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block114Part011] using hcert

def TailChunk001Sub000Block114Part012SupportExplicit : Finset ℕ :=
  ([21203] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block114Part012 : ℚ :=
  (103430157125 : ℚ) / 21630485867047944192

def SurrogateDiagonalTailChunk001Sub000Block114Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21203
    = surrogateDiagTailX0RatChunk001Sub000Block114Part012

theorem surrogateDiagonalTailChunk001Sub000Block114Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block114Part012CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block114Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block114Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block114Part012CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block114Part012SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block114Part012] using hcert

def TailChunk001Sub000Block114Part013SupportExplicit : Finset ℕ :=
  ([21205] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block114Part013 : ℚ :=
  (89920016509 : ℚ) / 8275423758857011200

def SurrogateDiagonalTailChunk001Sub000Block114Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21205
    = surrogateDiagTailX0RatChunk001Sub000Block114Part013

theorem surrogateDiagonalTailChunk001Sub000Block114Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block114Part013CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block114Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block114Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block114Part013CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block114Part013SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block114Part013] using hcert

def TailChunk001Sub000Block114Part014SupportExplicit : Finset ℕ :=
  ([21206] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block114Part014 : ℚ :=
  (101365239 : ℚ) / 17484678448709120

def SurrogateDiagonalTailChunk001Sub000Block114Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21206
    = surrogateDiagTailX0RatChunk001Sub000Block114Part014

theorem surrogateDiagonalTailChunk001Sub000Block114Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block114Part014CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block114Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block114Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block114Part014CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block114Part014SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block114Part014] using hcert

def TailChunk001Sub000Block114Part015SupportExplicit : Finset ℕ :=
  ([21207] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block114Part015 : ℚ :=
  (195182125675 : ℚ) / 6240408535834178688

def SurrogateDiagonalTailChunk001Sub000Block114Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21207
    = surrogateDiagTailX0RatChunk001Sub000Block114Part015

theorem surrogateDiagonalTailChunk001Sub000Block114Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block114Part015CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block114Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block114Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block114Part015CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block114Part015SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block114Part015] using hcert

def TailChunk001Sub000Block114Part016SupportExplicit : Finset ℕ :=
  ([21209] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block114Part016 : ℚ :=
  (44340851225 : ℚ) / 239282752529423582784

def SurrogateDiagonalTailChunk001Sub000Block114Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21209
    = surrogateDiagTailX0RatChunk001Sub000Block114Part016

theorem surrogateDiagonalTailChunk001Sub000Block114Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block114Part016CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block114Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block114Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block114Part016CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block114Part016SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block114Part016] using hcert

def TailChunk001Sub000Block114Part017SupportExplicit : Finset ℕ :=
  ([21210] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block114Part017 : ℚ :=
  (18647214677 : ℚ) / 26547388416000000

def SurrogateDiagonalTailChunk001Sub000Block114Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21210
    = surrogateDiagTailX0RatChunk001Sub000Block114Part017

theorem surrogateDiagonalTailChunk001Sub000Block114Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block114Part017CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block114Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block114Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block114Part017CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block114Part017SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block114Part017] using hcert

def TailChunk001Sub000Block114Part018SupportExplicit : Finset ℕ :=
  ([21211] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block114Part018 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block114Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21211
    = surrogateDiagTailX0RatChunk001Sub000Block114Part018

theorem surrogateDiagonalTailChunk001Sub000Block114Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block114Part018CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block114Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block114Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block114Part018CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block114Part018SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block114Part018] using hcert

def TailChunk001Sub000Block114Part019SupportExplicit : Finset ℕ :=
  ([21214] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block114Part019 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block114Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21214
    = surrogateDiagTailX0RatChunk001Sub000Block114Part019

theorem surrogateDiagonalTailChunk001Sub000Block114Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block114Part019CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block114Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block114Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block114Part019CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block114Part019SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block114Part019] using hcert

def TailChunk001Sub000Block114Part020SupportExplicit : Finset ℕ :=
  ([21215] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block114Part020 : ℚ :=
  (750040162675 : ℚ) / 69092073475585284096

def SurrogateDiagonalTailChunk001Sub000Block114Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21215
    = surrogateDiagTailX0RatChunk001Sub000Block114Part020

theorem surrogateDiagonalTailChunk001Sub000Block114Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block114Part020CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block114Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block114Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block114Part020CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block114Part020SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block114Part020] using hcert

def TailChunk001Sub000Block114Part021SupportExplicit : Finset ℕ :=
  ([21219] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block114Part021 : ℚ :=
  (116693053903 : ℚ) / 2718610219657267200

def SurrogateDiagonalTailChunk001Sub000Block114Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21219
    = surrogateDiagTailX0RatChunk001Sub000Block114Part021

theorem surrogateDiagonalTailChunk001Sub000Block114Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block114Part021CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block114Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block114Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block114Part021CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block114Part021SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block114Part021] using hcert

def TailChunk001Sub000Block114Part022SupportExplicit : Finset ℕ :=
  ([21221] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block114Part022 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block114Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21221
    = surrogateDiagTailX0RatChunk001Sub000Block114Part022

theorem surrogateDiagonalTailChunk001Sub000Block114Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block114Part022CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block114Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block114Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block114Part022CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block114Part022SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block114Part022] using hcert

def TailChunk001Sub000Block114Part023SupportExplicit : Finset ℕ :=
  ([21223] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block114Part023 : ℚ :=
  (98629045825 : ℚ) / 101792004441103176192

def SurrogateDiagonalTailChunk001Sub000Block114Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21223
    = surrogateDiagTailX0RatChunk001Sub000Block114Part023

theorem surrogateDiagonalTailChunk001Sub000Block114Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block114Part023CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block114Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block114Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block114Part023CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block114Part023SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block114Part023] using hcert

def TailChunk001Sub000Block114Part024SupportExplicit : Finset ℕ :=
  ([21226] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block114Part024 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block114Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21226
    = surrogateDiagTailX0RatChunk001Sub000Block114Part024

theorem surrogateDiagonalTailChunk001Sub000Block114Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block114Part024CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block114Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block114Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block114Part024CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block114Part024SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block114Part024] using hcert

def surrogateDiagonalTailChunk001Sub000Block114HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block114Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block114Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block114Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block114Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block114Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block114Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block114Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block114Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block114Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block114Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block114Head : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block114Part000
    + surrogateDiagTailX0RatChunk001Sub000Block114Part001
    + surrogateDiagTailX0RatChunk001Sub000Block114Part002
    + surrogateDiagTailX0RatChunk001Sub000Block114Part003
    + surrogateDiagTailX0RatChunk001Sub000Block114Part004
    + surrogateDiagTailX0RatChunk001Sub000Block114Part005
    + surrogateDiagTailX0RatChunk001Sub000Block114Part006
    + surrogateDiagTailX0RatChunk001Sub000Block114Part007
    + surrogateDiagTailX0RatChunk001Sub000Block114Part008
    + surrogateDiagTailX0RatChunk001Sub000Block114Part009

def surrogateDiagonalTailChunk001Sub000Block114MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block114Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block114Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block114Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block114Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block114Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block114Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block114Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block114Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block114Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block114Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block114Mid : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block114Part010
    + surrogateDiagTailX0RatChunk001Sub000Block114Part011
    + surrogateDiagTailX0RatChunk001Sub000Block114Part012
    + surrogateDiagTailX0RatChunk001Sub000Block114Part013
    + surrogateDiagTailX0RatChunk001Sub000Block114Part014
    + surrogateDiagTailX0RatChunk001Sub000Block114Part015
    + surrogateDiagTailX0RatChunk001Sub000Block114Part016
    + surrogateDiagTailX0RatChunk001Sub000Block114Part017
    + surrogateDiagTailX0RatChunk001Sub000Block114Part018
    + surrogateDiagTailX0RatChunk001Sub000Block114Part019

def surrogateDiagonalTailChunk001Sub000Block114TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block114Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block114Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block114Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block114Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block114Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block114Tail : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block114Part020
    + surrogateDiagTailX0RatChunk001Sub000Block114Part021
    + surrogateDiagTailX0RatChunk001Sub000Block114Part022
    + surrogateDiagTailX0RatChunk001Sub000Block114Part023
    + surrogateDiagTailX0RatChunk001Sub000Block114Part024

def surrogateDiagonalTailChunk001Sub000Block114Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk001Sub000Block114HeadSum X0
    + surrogateDiagonalTailChunk001Sub000Block114MidSum X0
    + surrogateDiagonalTailChunk001Sub000Block114TailSum X0

def surrogateDiagTailX0RatChunk001Sub000Block114 : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block114Part000
    + surrogateDiagTailX0RatChunk001Sub000Block114Part001
    + surrogateDiagTailX0RatChunk001Sub000Block114Part002
    + surrogateDiagTailX0RatChunk001Sub000Block114Part003
    + surrogateDiagTailX0RatChunk001Sub000Block114Part004
    + surrogateDiagTailX0RatChunk001Sub000Block114Part005
    + surrogateDiagTailX0RatChunk001Sub000Block114Part006
    + surrogateDiagTailX0RatChunk001Sub000Block114Part007
    + surrogateDiagTailX0RatChunk001Sub000Block114Part008
    + surrogateDiagTailX0RatChunk001Sub000Block114Part009
    + surrogateDiagTailX0RatChunk001Sub000Block114Part010
    + surrogateDiagTailX0RatChunk001Sub000Block114Part011
    + surrogateDiagTailX0RatChunk001Sub000Block114Part012
    + surrogateDiagTailX0RatChunk001Sub000Block114Part013
    + surrogateDiagTailX0RatChunk001Sub000Block114Part014
    + surrogateDiagTailX0RatChunk001Sub000Block114Part015
    + surrogateDiagTailX0RatChunk001Sub000Block114Part016
    + surrogateDiagTailX0RatChunk001Sub000Block114Part017
    + surrogateDiagTailX0RatChunk001Sub000Block114Part018
    + surrogateDiagTailX0RatChunk001Sub000Block114Part019
    + surrogateDiagTailX0RatChunk001Sub000Block114Part020
    + surrogateDiagTailX0RatChunk001Sub000Block114Part021
    + surrogateDiagTailX0RatChunk001Sub000Block114Part022
    + surrogateDiagTailX0RatChunk001Sub000Block114Part023
    + surrogateDiagTailX0RatChunk001Sub000Block114Part024

theorem surrogateDiagTailX0RatChunk001Sub000Block114_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk001Sub000Block114Head + surrogateDiagTailX0RatChunk001Sub000Block114Mid + surrogateDiagTailX0RatChunk001Sub000Block114Tail =
      surrogateDiagTailX0RatChunk001Sub000Block114 := by
  unfold surrogateDiagTailX0RatChunk001Sub000Block114Head surrogateDiagTailX0RatChunk001Sub000Block114Mid surrogateDiagTailX0RatChunk001Sub000Block114Tail surrogateDiagTailX0RatChunk001Sub000Block114
  ring

def SurrogateDiagonalTailChunk001Sub000Block114HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block114HeadSum X0 = surrogateDiagTailX0RatChunk001Sub000Block114Head

def SurrogateDiagonalTailChunk001Sub000Block114MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block114MidSum X0 = surrogateDiagTailX0RatChunk001Sub000Block114Mid

def SurrogateDiagonalTailChunk001Sub000Block114TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block114TailSum X0 = surrogateDiagTailX0RatChunk001Sub000Block114Tail

theorem surrogateDiagonalTailChunk001Sub000Block114_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk001Sub000Block114HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk001Sub000Block114MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk001Sub000Block114TailCertificateAt X0) :
    surrogateDiagonalTailChunk001Sub000Block114Sum X0 = surrogateDiagTailX0RatChunk001Sub000Block114 := by
  unfold SurrogateDiagonalTailChunk001Sub000Block114HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk001Sub000Block114MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk001Sub000Block114TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk001Sub000Block114Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk001Sub000Block114_eq_head_add_mid_add_tail

/-- Block 115 covers tail-support indices [12875,12900) and q from 21227 to 21265. -/

def TailChunk001Sub000Block115Part000SupportExplicit : Finset ℕ :=
  ([21227] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block115Part000 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block115Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21227
    = surrogateDiagTailX0RatChunk001Sub000Block115Part000

theorem surrogateDiagonalTailChunk001Sub000Block115Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block115Part000CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block115Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block115Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block115Part000CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block115Part000SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block115Part000] using hcert

def TailChunk001Sub000Block115Part001SupportExplicit : Finset ℕ :=
  ([21229] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block115Part001 : ℚ :=
  (10759959893 : ℚ) / 3888422639294054400

def SurrogateDiagonalTailChunk001Sub000Block115Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21229
    = surrogateDiagTailX0RatChunk001Sub000Block115Part001

theorem surrogateDiagonalTailChunk001Sub000Block115Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block115Part001CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block115Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block115Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block115Part001CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block115Part001SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block115Part001] using hcert

def TailChunk001Sub000Block115Part002SupportExplicit : Finset ℕ :=
  ([21230] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block115Part002 : ℚ :=
  (438328069 : ℚ) / 5436905147596800

def SurrogateDiagonalTailChunk001Sub000Block115Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21230
    = surrogateDiagTailX0RatChunk001Sub000Block115Part002

theorem surrogateDiagonalTailChunk001Sub000Block115Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block115Part002CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block115Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block115Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block115Part002CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block115Part002SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block115Part002] using hcert

def TailChunk001Sub000Block115Part003SupportExplicit : Finset ℕ :=
  ([21233] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block115Part003 : ℚ :=
  (394141186675 : ℚ) / 397525626676511244288

def SurrogateDiagonalTailChunk001Sub000Block115Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21233
    = surrogateDiagTailX0RatChunk001Sub000Block115Part003

theorem surrogateDiagonalTailChunk001Sub000Block115Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block115Part003CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block115Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block115Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block115Part003CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block115Part003SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block115Part003] using hcert

def TailChunk001Sub000Block115Part004SupportExplicit : Finset ℕ :=
  ([21234] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block115Part004 : ℚ :=
  (391482674525 : ℚ) / 3134354831479892544

def SurrogateDiagonalTailChunk001Sub000Block115Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21234
    = surrogateDiagTailX0RatChunk001Sub000Block115Part004

theorem surrogateDiagonalTailChunk001Sub000Block115Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block115Part004CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block115Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block115Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block115Part004CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block115Part004SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block115Part004] using hcert

def TailChunk001Sub000Block115Part005SupportExplicit : Finset ℕ :=
  ([21235] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block115Part005 : ℚ :=
  (25174927799 : ℚ) / 3547623084628377600

def SurrogateDiagonalTailChunk001Sub000Block115Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21235
    = surrogateDiagTailX0RatChunk001Sub000Block115Part005

theorem surrogateDiagonalTailChunk001Sub000Block115Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block115Part005CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block115Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block115Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block115Part005CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block115Part005SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block115Part005] using hcert

def TailChunk001Sub000Block115Part006SupportExplicit : Finset ℕ :=
  ([21237] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block115Part006 : ℚ :=
  (1565877630275 : ℚ) / 50206399681503004224

def SurrogateDiagonalTailChunk001Sub000Block115Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21237
    = surrogateDiagTailX0RatChunk001Sub000Block115Part006

theorem surrogateDiagonalTailChunk001Sub000Block115Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block115Part006CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block115Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block115Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block115Part006CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block115Part006SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block115Part006] using hcert

def TailChunk001Sub000Block115Part007SupportExplicit : Finset ℕ :=
  ([21238] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block115Part007 : ℚ :=
  (2105619307 : ℚ) / 55736772927160320

def SurrogateDiagonalTailChunk001Sub000Block115Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21238
    = surrogateDiagTailX0RatChunk001Sub000Block115Part007

theorem surrogateDiagonalTailChunk001Sub000Block115Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block115Part007CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block115Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block115Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block115Part007CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block115Part007SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block115Part007] using hcert

def TailChunk001Sub000Block115Part008SupportExplicit : Finset ℕ :=
  ([21239] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block115Part008 : ℚ :=
  (120281126125 : ℚ) / 473097803298845902848

def SurrogateDiagonalTailChunk001Sub000Block115Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21239
    = surrogateDiagTailX0RatChunk001Sub000Block115Part008

theorem surrogateDiagonalTailChunk001Sub000Block115Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block115Part008CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block115Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block115Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block115Part008CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block115Part008SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block115Part008] using hcert

def TailChunk001Sub000Block115Part009SupportExplicit : Finset ℕ :=
  ([21241] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block115Part009 : ℚ :=
  (28050667267 : ℚ) / 13877654986002000000

def SurrogateDiagonalTailChunk001Sub000Block115Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21241
    = surrogateDiagTailX0RatChunk001Sub000Block115Part009

theorem surrogateDiagonalTailChunk001Sub000Block115Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block115Part009CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block115Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block115Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block115Part009CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block115Part009SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block115Part009] using hcert

def TailChunk001Sub000Block115Part010SupportExplicit : Finset ℕ :=
  ([21242] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block115Part010 : ℚ :=
  (544363675 : ℚ) / 19603123798551552

def SurrogateDiagonalTailChunk001Sub000Block115Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21242
    = surrogateDiagTailX0RatChunk001Sub000Block115Part010

theorem surrogateDiagonalTailChunk001Sub000Block115Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block115Part010CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block115Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block115Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block115Part010CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block115Part010SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block115Part010] using hcert

def TailChunk001Sub000Block115Part011SupportExplicit : Finset ℕ :=
  ([21243] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block115Part011 : ℚ :=
  (3088471584625 : ℚ) / 91319128763859468288

def SurrogateDiagonalTailChunk001Sub000Block115Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21243
    = surrogateDiagTailX0RatChunk001Sub000Block115Part011

theorem surrogateDiagonalTailChunk001Sub000Block115Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block115Part011CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block115Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block115Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block115Part011CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block115Part011SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block115Part011] using hcert

def TailChunk001Sub000Block115Part012SupportExplicit : Finset ℕ :=
  ([21245] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block115Part012 : ℚ :=
  (140248157375 : ℚ) / 9323545108742037504

def SurrogateDiagonalTailChunk001Sub000Block115Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21245
    = surrogateDiagTailX0RatChunk001Sub000Block115Part012

theorem surrogateDiagonalTailChunk001Sub000Block115Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block115Part012CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block115Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block115Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block115Part012CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block115Part012SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block115Part012] using hcert

def TailChunk001Sub000Block115Part013SupportExplicit : Finset ℕ :=
  ([21246] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block115Part013 : ℚ :=
  (783850099 : ℚ) / 6282896270388480

def SurrogateDiagonalTailChunk001Sub000Block115Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21246
    = surrogateDiagTailX0RatChunk001Sub000Block115Part013

theorem surrogateDiagonalTailChunk001Sub000Block115Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block115Part013CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block115Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block115Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block115Part013CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block115Part013SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block115Part013] using hcert

def TailChunk001Sub000Block115Part014SupportExplicit : Finset ℕ :=
  ([21247] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block115Part014 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block115Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21247
    = surrogateDiagTailX0RatChunk001Sub000Block115Part014

theorem surrogateDiagonalTailChunk001Sub000Block115Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block115Part014CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block115Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block115Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block115Part014CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block115Part014SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block115Part014] using hcert

def TailChunk001Sub000Block115Part015SupportExplicit : Finset ℕ :=
  ([21251] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block115Part015 : ℚ :=
  (109252628725 : ℚ) / 477468192801428195328

def SurrogateDiagonalTailChunk001Sub000Block115Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21251
    = surrogateDiagTailX0RatChunk001Sub000Block115Part015

theorem surrogateDiagonalTailChunk001Sub000Block115Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block115Part015CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block115Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block115Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block115Part015CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block115Part015SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block115Part015] using hcert

def TailChunk001Sub000Block115Part016SupportExplicit : Finset ℕ :=
  ([21253] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block115Part016 : ℚ :=
  (973639647 : ℚ) / 3120246751232000000

def SurrogateDiagonalTailChunk001Sub000Block115Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21253
    = surrogateDiagTailX0RatChunk001Sub000Block115Part016

theorem surrogateDiagonalTailChunk001Sub000Block115Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block115Part016CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block115Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block115Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block115Part016CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block115Part016SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block115Part016] using hcert

def TailChunk001Sub000Block115Part017SupportExplicit : Finset ℕ :=
  ([21254] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block115Part017 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block115Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21254
    = surrogateDiagTailX0RatChunk001Sub000Block115Part017

theorem surrogateDiagonalTailChunk001Sub000Block115Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block115Part017CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block115Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block115Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block115Part017CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block115Part017SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block115Part017] using hcert

def TailChunk001Sub000Block115Part018SupportExplicit : Finset ℕ :=
  ([21255] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block115Part018 : ℚ :=
  (862083246875 : ℚ) / 9631314361813303296

def SurrogateDiagonalTailChunk001Sub000Block115Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21255
    = surrogateDiagTailX0RatChunk001Sub000Block115Part018

theorem surrogateDiagonalTailChunk001Sub000Block115Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block115Part018CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block115Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block115Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block115Part018CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block115Part018SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block115Part018] using hcert

def TailChunk001Sub000Block115Part019SupportExplicit : Finset ℕ :=
  ([21257] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block115Part019 : ℚ :=
  (209465017375 : ℚ) / 441268888227300016128

def SurrogateDiagonalTailChunk001Sub000Block115Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21257
    = surrogateDiagTailX0RatChunk001Sub000Block115Part019

theorem surrogateDiagonalTailChunk001Sub000Block115Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block115Part019CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block115Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block115Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block115Part019CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block115Part019SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block115Part019] using hcert

def TailChunk001Sub000Block115Part020SupportExplicit : Finset ℕ :=
  ([21259] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block115Part020 : ℚ :=
  (576903203375 : ℚ) / 137660370362376643584

def SurrogateDiagonalTailChunk001Sub000Block115Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21259
    = surrogateDiagTailX0RatChunk001Sub000Block115Part020

theorem surrogateDiagonalTailChunk001Sub000Block115Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block115Part020CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block115Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block115Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block115Part020CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block115Part020SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block115Part020] using hcert

def TailChunk001Sub000Block115Part021SupportExplicit : Finset ℕ :=
  ([21261] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block115Part021 : ℚ :=
  (23803747925 : ℚ) / 628345706426562816

def SurrogateDiagonalTailChunk001Sub000Block115Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21261
    = surrogateDiagTailX0RatChunk001Sub000Block115Part021

theorem surrogateDiagonalTailChunk001Sub000Block115Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block115Part021CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block115Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block115Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block115Part021CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block115Part021SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block115Part021] using hcert

def TailChunk001Sub000Block115Part022SupportExplicit : Finset ℕ :=
  ([21262] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block115Part022 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block115Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21262
    = surrogateDiagTailX0RatChunk001Sub000Block115Part022

theorem surrogateDiagonalTailChunk001Sub000Block115Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block115Part022CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block115Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block115Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block115Part022CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block115Part022SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block115Part022] using hcert

def TailChunk001Sub000Block115Part023SupportExplicit : Finset ℕ :=
  ([21263] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block115Part023 : ℚ :=
  (4015510579 : ℚ) / 1990752631680153600

def SurrogateDiagonalTailChunk001Sub000Block115Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21263
    = surrogateDiagTailX0RatChunk001Sub000Block115Part023

theorem surrogateDiagonalTailChunk001Sub000Block115Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block115Part023CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block115Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block115Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block115Part023CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block115Part023SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block115Part023] using hcert

def TailChunk001Sub000Block115Part024SupportExplicit : Finset ℕ :=
  ([21265] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block115Part024 : ℚ :=
  (377073218625 : ℚ) / 69745885563518550016

def SurrogateDiagonalTailChunk001Sub000Block115Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21265
    = surrogateDiagTailX0RatChunk001Sub000Block115Part024

theorem surrogateDiagonalTailChunk001Sub000Block115Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block115Part024CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block115Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block115Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block115Part024CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block115Part024SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block115Part024] using hcert

def surrogateDiagonalTailChunk001Sub000Block115HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block115Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block115Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block115Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block115Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block115Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block115Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block115Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block115Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block115Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block115Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block115Head : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block115Part000
    + surrogateDiagTailX0RatChunk001Sub000Block115Part001
    + surrogateDiagTailX0RatChunk001Sub000Block115Part002
    + surrogateDiagTailX0RatChunk001Sub000Block115Part003
    + surrogateDiagTailX0RatChunk001Sub000Block115Part004
    + surrogateDiagTailX0RatChunk001Sub000Block115Part005
    + surrogateDiagTailX0RatChunk001Sub000Block115Part006
    + surrogateDiagTailX0RatChunk001Sub000Block115Part007
    + surrogateDiagTailX0RatChunk001Sub000Block115Part008
    + surrogateDiagTailX0RatChunk001Sub000Block115Part009

def surrogateDiagonalTailChunk001Sub000Block115MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block115Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block115Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block115Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block115Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block115Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block115Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block115Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block115Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block115Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block115Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block115Mid : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block115Part010
    + surrogateDiagTailX0RatChunk001Sub000Block115Part011
    + surrogateDiagTailX0RatChunk001Sub000Block115Part012
    + surrogateDiagTailX0RatChunk001Sub000Block115Part013
    + surrogateDiagTailX0RatChunk001Sub000Block115Part014
    + surrogateDiagTailX0RatChunk001Sub000Block115Part015
    + surrogateDiagTailX0RatChunk001Sub000Block115Part016
    + surrogateDiagTailX0RatChunk001Sub000Block115Part017
    + surrogateDiagTailX0RatChunk001Sub000Block115Part018
    + surrogateDiagTailX0RatChunk001Sub000Block115Part019

def surrogateDiagonalTailChunk001Sub000Block115TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block115Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block115Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block115Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block115Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block115Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block115Tail : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block115Part020
    + surrogateDiagTailX0RatChunk001Sub000Block115Part021
    + surrogateDiagTailX0RatChunk001Sub000Block115Part022
    + surrogateDiagTailX0RatChunk001Sub000Block115Part023
    + surrogateDiagTailX0RatChunk001Sub000Block115Part024

def surrogateDiagonalTailChunk001Sub000Block115Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk001Sub000Block115HeadSum X0
    + surrogateDiagonalTailChunk001Sub000Block115MidSum X0
    + surrogateDiagonalTailChunk001Sub000Block115TailSum X0

def surrogateDiagTailX0RatChunk001Sub000Block115 : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block115Part000
    + surrogateDiagTailX0RatChunk001Sub000Block115Part001
    + surrogateDiagTailX0RatChunk001Sub000Block115Part002
    + surrogateDiagTailX0RatChunk001Sub000Block115Part003
    + surrogateDiagTailX0RatChunk001Sub000Block115Part004
    + surrogateDiagTailX0RatChunk001Sub000Block115Part005
    + surrogateDiagTailX0RatChunk001Sub000Block115Part006
    + surrogateDiagTailX0RatChunk001Sub000Block115Part007
    + surrogateDiagTailX0RatChunk001Sub000Block115Part008
    + surrogateDiagTailX0RatChunk001Sub000Block115Part009
    + surrogateDiagTailX0RatChunk001Sub000Block115Part010
    + surrogateDiagTailX0RatChunk001Sub000Block115Part011
    + surrogateDiagTailX0RatChunk001Sub000Block115Part012
    + surrogateDiagTailX0RatChunk001Sub000Block115Part013
    + surrogateDiagTailX0RatChunk001Sub000Block115Part014
    + surrogateDiagTailX0RatChunk001Sub000Block115Part015
    + surrogateDiagTailX0RatChunk001Sub000Block115Part016
    + surrogateDiagTailX0RatChunk001Sub000Block115Part017
    + surrogateDiagTailX0RatChunk001Sub000Block115Part018
    + surrogateDiagTailX0RatChunk001Sub000Block115Part019
    + surrogateDiagTailX0RatChunk001Sub000Block115Part020
    + surrogateDiagTailX0RatChunk001Sub000Block115Part021
    + surrogateDiagTailX0RatChunk001Sub000Block115Part022
    + surrogateDiagTailX0RatChunk001Sub000Block115Part023
    + surrogateDiagTailX0RatChunk001Sub000Block115Part024

theorem surrogateDiagTailX0RatChunk001Sub000Block115_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk001Sub000Block115Head + surrogateDiagTailX0RatChunk001Sub000Block115Mid + surrogateDiagTailX0RatChunk001Sub000Block115Tail =
      surrogateDiagTailX0RatChunk001Sub000Block115 := by
  unfold surrogateDiagTailX0RatChunk001Sub000Block115Head surrogateDiagTailX0RatChunk001Sub000Block115Mid surrogateDiagTailX0RatChunk001Sub000Block115Tail surrogateDiagTailX0RatChunk001Sub000Block115
  ring

def SurrogateDiagonalTailChunk001Sub000Block115HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block115HeadSum X0 = surrogateDiagTailX0RatChunk001Sub000Block115Head

def SurrogateDiagonalTailChunk001Sub000Block115MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block115MidSum X0 = surrogateDiagTailX0RatChunk001Sub000Block115Mid

def SurrogateDiagonalTailChunk001Sub000Block115TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block115TailSum X0 = surrogateDiagTailX0RatChunk001Sub000Block115Tail

theorem surrogateDiagonalTailChunk001Sub000Block115_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk001Sub000Block115HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk001Sub000Block115MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk001Sub000Block115TailCertificateAt X0) :
    surrogateDiagonalTailChunk001Sub000Block115Sum X0 = surrogateDiagTailX0RatChunk001Sub000Block115 := by
  unfold SurrogateDiagonalTailChunk001Sub000Block115HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk001Sub000Block115MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk001Sub000Block115TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk001Sub000Block115Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk001Sub000Block115_eq_head_add_mid_add_tail

/-- Block 116 covers tail-support indices [12900,12925) and q from 21269 to 21307. -/

def TailChunk001Sub000Block116Part000SupportExplicit : Finset ℕ :=
  ([21269] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block116Part000 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block116Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21269
    = surrogateDiagTailX0RatChunk001Sub000Block116Part000

theorem surrogateDiagonalTailChunk001Sub000Block116Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block116Part000CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block116Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block116Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block116Part000CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block116Part000SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block116Part000] using hcert

def TailChunk001Sub000Block116Part001SupportExplicit : Finset ℕ :=
  ([21270] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block116Part001 : ℚ :=
  (293262162875 : ℚ) / 857824770783707136

def SurrogateDiagonalTailChunk001Sub000Block116Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21270
    = surrogateDiagTailX0RatChunk001Sub000Block116Part001

theorem surrogateDiagonalTailChunk001Sub000Block116Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block116Part001CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block116Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block116Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block116Part001CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block116Part001SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block116Part001] using hcert

def TailChunk001Sub000Block116Part002SupportExplicit : Finset ℕ :=
  ([21271] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block116Part002 : ℚ :=
  (639131275 : ℚ) / 3124241916849242112

def SurrogateDiagonalTailChunk001Sub000Block116Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21271
    = surrogateDiagTailX0RatChunk001Sub000Block116Part002

theorem surrogateDiagonalTailChunk001Sub000Block116Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block116Part002CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block116Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block116Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block116Part002CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block116Part002SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block116Part002] using hcert

def TailChunk001Sub000Block116Part003SupportExplicit : Finset ℕ :=
  ([21273] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block116Part003 : ℚ :=
  (92122771775 : ℚ) / 1699510745214526464

def SurrogateDiagonalTailChunk001Sub000Block116Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21273
    = surrogateDiagTailX0RatChunk001Sub000Block116Part003

theorem surrogateDiagonalTailChunk001Sub000Block116Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block116Part003CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block116Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block116Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block116Part003CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block116Part003SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block116Part003] using hcert

def TailChunk001Sub000Block116Part004SupportExplicit : Finset ℕ :=
  ([21274] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block116Part004 : ℚ :=
  (78534683 : ℚ) / 5806361842400448

def SurrogateDiagonalTailChunk001Sub000Block116Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21274
    = surrogateDiagTailX0RatChunk001Sub000Block116Part004

theorem surrogateDiagonalTailChunk001Sub000Block116Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block116Part004CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block116Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block116Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block116Part004CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block116Part004SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block116Part004] using hcert

def TailChunk001Sub000Block116Part005SupportExplicit : Finset ℕ :=
  ([21277] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block116Part005 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block116Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21277
    = surrogateDiagTailX0RatChunk001Sub000Block116Part005

theorem surrogateDiagonalTailChunk001Sub000Block116Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block116Part005CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block116Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block116Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block116Part005CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block116Part005SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block116Part005] using hcert

def TailChunk001Sub000Block116Part006SupportExplicit : Finset ℕ :=
  ([21278] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block116Part006 : ℚ :=
  (1768567515625 : ℚ) / 8005838252292172242

def SurrogateDiagonalTailChunk001Sub000Block116Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21278
    = surrogateDiagTailX0RatChunk001Sub000Block116Part006

theorem surrogateDiagonalTailChunk001Sub000Block116Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block116Part006CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block116Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block116Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block116Part006CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block116Part006SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block116Part006] using hcert

def TailChunk001Sub000Block116Part007SupportExplicit : Finset ℕ :=
  ([21279] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block116Part007 : ℚ :=
  (123612852859 : ℚ) / 3585589651911475200

def SurrogateDiagonalTailChunk001Sub000Block116Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21279
    = surrogateDiagTailX0RatChunk001Sub000Block116Part007

theorem surrogateDiagonalTailChunk001Sub000Block116Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block116Part007CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block116Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block116Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block116Part007CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block116Part007SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block116Part007] using hcert

def TailChunk001Sub000Block116Part008SupportExplicit : Finset ℕ :=
  ([21281] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block116Part008 : ℚ :=
  (252697733225 : ℚ) / 185718447583638994944

def SurrogateDiagonalTailChunk001Sub000Block116Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21281
    = surrogateDiagTailX0RatChunk001Sub000Block116Part008

theorem surrogateDiagonalTailChunk001Sub000Block116Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block116Part008CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block116Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block116Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block116Part008CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block116Part008SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block116Part008] using hcert

def TailChunk001Sub000Block116Part009SupportExplicit : Finset ℕ :=
  ([21282] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block116Part009 : ℚ :=
  (491333100575 : ℚ) / 790700074300461456

def SurrogateDiagonalTailChunk001Sub000Block116Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21282
    = surrogateDiagTailX0RatChunk001Sub000Block116Part009

theorem surrogateDiagonalTailChunk001Sub000Block116Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block116Part009CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block116Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block116Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block116Part009CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block116Part009SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block116Part009] using hcert

def TailChunk001Sub000Block116Part010SupportExplicit : Finset ℕ :=
  ([21283] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block116Part010 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block116Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21283
    = surrogateDiagTailX0RatChunk001Sub000Block116Part010

theorem surrogateDiagonalTailChunk001Sub000Block116Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block116Part010CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block116Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block116Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block116Part010CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block116Part010SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block116Part010] using hcert

def TailChunk001Sub000Block116Part011SupportExplicit : Finset ℕ :=
  ([21286] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block116Part011 : ℚ :=
  (835289864825 : ℚ) / 3447413189275781376

def SurrogateDiagonalTailChunk001Sub000Block116Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21286
    = surrogateDiagTailX0RatChunk001Sub000Block116Part011

theorem surrogateDiagonalTailChunk001Sub000Block116Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block116Part011CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block116Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block116Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block116Part011CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block116Part011SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block116Part011] using hcert

def TailChunk001Sub000Block116Part012SupportExplicit : Finset ℕ :=
  ([21287] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block116Part012 : ℚ :=
  (23136875987 : ℚ) / 5535491529218457600

def SurrogateDiagonalTailChunk001Sub000Block116Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21287
    = surrogateDiagTailX0RatChunk001Sub000Block116Part012

theorem surrogateDiagonalTailChunk001Sub000Block116Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block116Part012CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block116Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block116Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block116Part012CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block116Part012SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block116Part012] using hcert

def TailChunk001Sub000Block116Part013SupportExplicit : Finset ℕ :=
  ([21289] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block116Part013 : ℚ :=
  (11523053 : ℚ) / 44007336155289600

def SurrogateDiagonalTailChunk001Sub000Block116Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21289
    = surrogateDiagTailX0RatChunk001Sub000Block116Part013

theorem surrogateDiagonalTailChunk001Sub000Block116Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block116Part013CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block116Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block116Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block116Part013CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block116Part013SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block116Part013] using hcert

def TailChunk001Sub000Block116Part014SupportExplicit : Finset ℕ :=
  ([21290] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block116Part014 : ℚ :=
  (242689276425 : ℚ) / 625077726591582208

def SurrogateDiagonalTailChunk001Sub000Block116Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21290
    = surrogateDiagTailX0RatChunk001Sub000Block116Part014

theorem surrogateDiagonalTailChunk001Sub000Block116Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block116Part014CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block116Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block116Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block116Part014CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block116Part014SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block116Part014] using hcert

def TailChunk001Sub000Block116Part015SupportExplicit : Finset ℕ :=
  ([21291] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block116Part015 : ℚ :=
  (598146749 : ℚ) / 17523984096000000

def SurrogateDiagonalTailChunk001Sub000Block116Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21291
    = surrogateDiagTailX0RatChunk001Sub000Block116Part015

theorem surrogateDiagonalTailChunk001Sub000Block116Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block116Part015CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block116Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block116Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block116Part015CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block116Part015SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block116Part015] using hcert

def TailChunk001Sub000Block116Part016SupportExplicit : Finset ℕ :=
  ([21293] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block116Part016 : ℚ :=
  (11784512675 : ℚ) / 60648643827951409296

def SurrogateDiagonalTailChunk001Sub000Block116Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21293
    = surrogateDiagTailX0RatChunk001Sub000Block116Part016

theorem surrogateDiagonalTailChunk001Sub000Block116Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block116Part016CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block116Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block116Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block116Part016CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block116Part016SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block116Part016] using hcert

def TailChunk001Sub000Block116Part017SupportExplicit : Finset ℕ :=
  ([21295] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block116Part017 : ℚ :=
  (378136968375 : ℚ) / 70140393478034692096

def SurrogateDiagonalTailChunk001Sub000Block116Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21295
    = surrogateDiagTailX0RatChunk001Sub000Block116Part017

theorem surrogateDiagonalTailChunk001Sub000Block116Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block116Part017CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block116Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block116Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block116Part017CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block116Part017SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block116Part017] using hcert

def TailChunk001Sub000Block116Part018SupportExplicit : Finset ℕ :=
  ([21297] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block116Part018 : ℚ :=
  (24711341657 : ℚ) / 700585646666711040

def SurrogateDiagonalTailChunk001Sub000Block116Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21297
    = surrogateDiagTailX0RatChunk001Sub000Block116Part018

theorem surrogateDiagonalTailChunk001Sub000Block116Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block116Part018CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block116Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block116Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block116Part018CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block116Part018SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block116Part018] using hcert

def TailChunk001Sub000Block116Part019SupportExplicit : Finset ℕ :=
  ([21298] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block116Part019 : ℚ :=
  (599804363975 : ℚ) / 2426011187297056128

def SurrogateDiagonalTailChunk001Sub000Block116Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21298
    = surrogateDiagTailX0RatChunk001Sub000Block116Part019

theorem surrogateDiagonalTailChunk001Sub000Block116Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block116Part019CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block116Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block116Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block116Part019CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block116Part019SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block116Part019] using hcert

def TailChunk001Sub000Block116Part020SupportExplicit : Finset ℕ :=
  ([21301] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block116Part020 : ℚ :=
  (4874522725 : ℚ) / 1197765495311302656

def SurrogateDiagonalTailChunk001Sub000Block116Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21301
    = surrogateDiagTailX0RatChunk001Sub000Block116Part020

theorem surrogateDiagonalTailChunk001Sub000Block116Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block116Part020CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block116Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block116Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block116Part020CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block116Part020SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block116Part020] using hcert

def TailChunk001Sub000Block116Part021SupportExplicit : Finset ℕ :=
  ([21302] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block116Part021 : ℚ :=
  (113443801 : ℚ) / 514689457558050

def SurrogateDiagonalTailChunk001Sub000Block116Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21302
    = surrogateDiagTailX0RatChunk001Sub000Block116Part021

theorem surrogateDiagonalTailChunk001Sub000Block116Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block116Part021CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block116Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block116Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block116Part021CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block116Part021SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block116Part021] using hcert

def TailChunk001Sub000Block116Part022SupportExplicit : Finset ℕ :=
  ([21305] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block116Part022 : ℚ :=
  (9083805239 : ℚ) / 1686534414526218240

def SurrogateDiagonalTailChunk001Sub000Block116Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21305
    = surrogateDiagTailX0RatChunk001Sub000Block116Part022

theorem surrogateDiagonalTailChunk001Sub000Block116Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block116Part022CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block116Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block116Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block116Part022CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block116Part022SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block116Part022] using hcert

def TailChunk001Sub000Block116Part023SupportExplicit : Finset ℕ :=
  ([21306] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block116Part023 : ℚ :=
  (138997477475 : ℚ) / 205575897081544704

def SurrogateDiagonalTailChunk001Sub000Block116Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21306
    = surrogateDiagTailX0RatChunk001Sub000Block116Part023

theorem surrogateDiagonalTailChunk001Sub000Block116Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block116Part023CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block116Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block116Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block116Part023CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block116Part023SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block116Part023] using hcert

def TailChunk001Sub000Block116Part024SupportExplicit : Finset ℕ :=
  ([21307] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block116Part024 : ℚ :=
  (35287001953 : ℚ) / 9950816004223795200

def SurrogateDiagonalTailChunk001Sub000Block116Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21307
    = surrogateDiagTailX0RatChunk001Sub000Block116Part024

theorem surrogateDiagonalTailChunk001Sub000Block116Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block116Part024CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block116Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block116Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block116Part024CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block116Part024SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block116Part024] using hcert

def surrogateDiagonalTailChunk001Sub000Block116HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block116Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block116Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block116Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block116Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block116Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block116Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block116Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block116Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block116Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block116Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block116Head : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block116Part000
    + surrogateDiagTailX0RatChunk001Sub000Block116Part001
    + surrogateDiagTailX0RatChunk001Sub000Block116Part002
    + surrogateDiagTailX0RatChunk001Sub000Block116Part003
    + surrogateDiagTailX0RatChunk001Sub000Block116Part004
    + surrogateDiagTailX0RatChunk001Sub000Block116Part005
    + surrogateDiagTailX0RatChunk001Sub000Block116Part006
    + surrogateDiagTailX0RatChunk001Sub000Block116Part007
    + surrogateDiagTailX0RatChunk001Sub000Block116Part008
    + surrogateDiagTailX0RatChunk001Sub000Block116Part009

def surrogateDiagonalTailChunk001Sub000Block116MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block116Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block116Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block116Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block116Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block116Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block116Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block116Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block116Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block116Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block116Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block116Mid : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block116Part010
    + surrogateDiagTailX0RatChunk001Sub000Block116Part011
    + surrogateDiagTailX0RatChunk001Sub000Block116Part012
    + surrogateDiagTailX0RatChunk001Sub000Block116Part013
    + surrogateDiagTailX0RatChunk001Sub000Block116Part014
    + surrogateDiagTailX0RatChunk001Sub000Block116Part015
    + surrogateDiagTailX0RatChunk001Sub000Block116Part016
    + surrogateDiagTailX0RatChunk001Sub000Block116Part017
    + surrogateDiagTailX0RatChunk001Sub000Block116Part018
    + surrogateDiagTailX0RatChunk001Sub000Block116Part019

def surrogateDiagonalTailChunk001Sub000Block116TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block116Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block116Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block116Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block116Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block116Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block116Tail : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block116Part020
    + surrogateDiagTailX0RatChunk001Sub000Block116Part021
    + surrogateDiagTailX0RatChunk001Sub000Block116Part022
    + surrogateDiagTailX0RatChunk001Sub000Block116Part023
    + surrogateDiagTailX0RatChunk001Sub000Block116Part024

def surrogateDiagonalTailChunk001Sub000Block116Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk001Sub000Block116HeadSum X0
    + surrogateDiagonalTailChunk001Sub000Block116MidSum X0
    + surrogateDiagonalTailChunk001Sub000Block116TailSum X0

def surrogateDiagTailX0RatChunk001Sub000Block116 : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block116Part000
    + surrogateDiagTailX0RatChunk001Sub000Block116Part001
    + surrogateDiagTailX0RatChunk001Sub000Block116Part002
    + surrogateDiagTailX0RatChunk001Sub000Block116Part003
    + surrogateDiagTailX0RatChunk001Sub000Block116Part004
    + surrogateDiagTailX0RatChunk001Sub000Block116Part005
    + surrogateDiagTailX0RatChunk001Sub000Block116Part006
    + surrogateDiagTailX0RatChunk001Sub000Block116Part007
    + surrogateDiagTailX0RatChunk001Sub000Block116Part008
    + surrogateDiagTailX0RatChunk001Sub000Block116Part009
    + surrogateDiagTailX0RatChunk001Sub000Block116Part010
    + surrogateDiagTailX0RatChunk001Sub000Block116Part011
    + surrogateDiagTailX0RatChunk001Sub000Block116Part012
    + surrogateDiagTailX0RatChunk001Sub000Block116Part013
    + surrogateDiagTailX0RatChunk001Sub000Block116Part014
    + surrogateDiagTailX0RatChunk001Sub000Block116Part015
    + surrogateDiagTailX0RatChunk001Sub000Block116Part016
    + surrogateDiagTailX0RatChunk001Sub000Block116Part017
    + surrogateDiagTailX0RatChunk001Sub000Block116Part018
    + surrogateDiagTailX0RatChunk001Sub000Block116Part019
    + surrogateDiagTailX0RatChunk001Sub000Block116Part020
    + surrogateDiagTailX0RatChunk001Sub000Block116Part021
    + surrogateDiagTailX0RatChunk001Sub000Block116Part022
    + surrogateDiagTailX0RatChunk001Sub000Block116Part023
    + surrogateDiagTailX0RatChunk001Sub000Block116Part024

theorem surrogateDiagTailX0RatChunk001Sub000Block116_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk001Sub000Block116Head + surrogateDiagTailX0RatChunk001Sub000Block116Mid + surrogateDiagTailX0RatChunk001Sub000Block116Tail =
      surrogateDiagTailX0RatChunk001Sub000Block116 := by
  unfold surrogateDiagTailX0RatChunk001Sub000Block116Head surrogateDiagTailX0RatChunk001Sub000Block116Mid surrogateDiagTailX0RatChunk001Sub000Block116Tail surrogateDiagTailX0RatChunk001Sub000Block116
  ring

def SurrogateDiagonalTailChunk001Sub000Block116HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block116HeadSum X0 = surrogateDiagTailX0RatChunk001Sub000Block116Head

def SurrogateDiagonalTailChunk001Sub000Block116MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block116MidSum X0 = surrogateDiagTailX0RatChunk001Sub000Block116Mid

def SurrogateDiagonalTailChunk001Sub000Block116TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block116TailSum X0 = surrogateDiagTailX0RatChunk001Sub000Block116Tail

theorem surrogateDiagonalTailChunk001Sub000Block116_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk001Sub000Block116HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk001Sub000Block116MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk001Sub000Block116TailCertificateAt X0) :
    surrogateDiagonalTailChunk001Sub000Block116Sum X0 = surrogateDiagTailX0RatChunk001Sub000Block116 := by
  unfold SurrogateDiagonalTailChunk001Sub000Block116HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk001Sub000Block116MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk001Sub000Block116TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk001Sub000Block116Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk001Sub000Block116_eq_head_add_mid_add_tail

/-- Block 117 covers tail-support indices [12925,12950) and q from 21309 to 21347. -/

def TailChunk001Sub000Block117Part000SupportExplicit : Finset ℕ :=
  ([21309] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block117Part000 : ℚ :=
  (1576512629975 : ℚ) / 50890828091736588864

def SurrogateDiagonalTailChunk001Sub000Block117Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21309
    = surrogateDiagTailX0RatChunk001Sub000Block117Part000

theorem surrogateDiagonalTailChunk001Sub000Block117Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block117Part000CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block117Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block117Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block117Part000CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block117Part000SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block117Part000] using hcert

def TailChunk001Sub000Block117Part001SupportExplicit : Finset ℕ :=
  ([21310] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block117Part001 : ℚ :=
  (192886411489 : ℚ) / 527042004539443200

def SurrogateDiagonalTailChunk001Sub000Block117Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21310
    = surrogateDiagTailX0RatChunk001Sub000Block117Part001

theorem surrogateDiagonalTailChunk001Sub000Block117Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block117Part001CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block117Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block117Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block117Part001CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block117Part001SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block117Part001] using hcert

def TailChunk001Sub000Block117Part002SupportExplicit : Finset ℕ :=
  ([21311] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block117Part002 : ℚ :=
  (79510771 : ℚ) / 396979380000000000

def SurrogateDiagonalTailChunk001Sub000Block117Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21311
    = surrogateDiagTailX0RatChunk001Sub000Block117Part002

theorem surrogateDiagonalTailChunk001Sub000Block117Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block117Part002CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block117Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block117Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block117Part002CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block117Part002SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block117Part002] using hcert

def TailChunk001Sub000Block117Part003SupportExplicit : Finset ℕ :=
  ([21313] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block117Part003 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block117Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21313
    = surrogateDiagTailX0RatChunk001Sub000Block117Part003

theorem surrogateDiagonalTailChunk001Sub000Block117Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block117Part003CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block117Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block117Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block117Part003CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block117Part003SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block117Part003] using hcert

def TailChunk001Sub000Block117Part004SupportExplicit : Finset ℕ :=
  ([21314] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block117Part004 : ℚ :=
  (1774557015625 : ℚ) / 8060160963421274112

def SurrogateDiagonalTailChunk001Sub000Block117Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21314
    = surrogateDiagTailX0RatChunk001Sub000Block117Part004

theorem surrogateDiagonalTailChunk001Sub000Block117Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block117Part004CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block117Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block117Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block117Part004CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block117Part004SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block117Part004] using hcert

def TailChunk001Sub000Block117Part005SupportExplicit : Finset ℕ :=
  ([21317] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block117Part005 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block117Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21317
    = surrogateDiagTailX0RatChunk001Sub000Block117Part005

theorem surrogateDiagonalTailChunk001Sub000Block117Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block117Part005CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block117Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block117Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block117Part005CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block117Part005SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block117Part005] using hcert

def TailChunk001Sub000Block117Part006SupportExplicit : Finset ℕ :=
  ([21318] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block117Part006 : ℚ :=
  (39081013099 : ℚ) / 36699109746278400

def SurrogateDiagonalTailChunk001Sub000Block117Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21318
    = surrogateDiagTailX0RatChunk001Sub000Block117Part006

theorem surrogateDiagonalTailChunk001Sub000Block117Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block117Part006CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block117Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block117Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block117Part006CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block117Part006SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block117Part006] using hcert

def TailChunk001Sub000Block117Part007SupportExplicit : Finset ℕ :=
  ([21319] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block117Part007 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block117Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21319
    = surrogateDiagTailX0RatChunk001Sub000Block117Part007

theorem surrogateDiagonalTailChunk001Sub000Block117Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block117Part007CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block117Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block117Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block117Part007CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block117Part007SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block117Part007] using hcert

def TailChunk001Sub000Block117Part008SupportExplicit : Finset ℕ :=
  ([21322] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block117Part008 : ℚ :=
  (43001233625 : ℚ) / 135856524591348921

def SurrogateDiagonalTailChunk001Sub000Block117Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21322
    = surrogateDiagTailX0RatChunk001Sub000Block117Part008

theorem surrogateDiagonalTailChunk001Sub000Block117Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block117Part008CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block117Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block117Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block117Part008CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block117Part008SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block117Part008] using hcert

def TailChunk001Sub000Block117Part009SupportExplicit : Finset ℕ :=
  ([21323] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block117Part009 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block117Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21323
    = surrogateDiagTailX0RatChunk001Sub000Block117Part009

theorem surrogateDiagonalTailChunk001Sub000Block117Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block117Part009CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block117Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block117Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block117Part009CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block117Part009SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block117Part009] using hcert

def TailChunk001Sub000Block117Part010SupportExplicit : Finset ℕ :=
  ([21326] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block117Part010 : ℚ :=
  (1776555765625 : ℚ) / 8078329817222075442

def SurrogateDiagonalTailChunk001Sub000Block117Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21326
    = surrogateDiagTailX0RatChunk001Sub000Block117Part010

theorem surrogateDiagonalTailChunk001Sub000Block117Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block117Part010CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block117Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block117Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block117Part010CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block117Part010SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block117Part010] using hcert

def TailChunk001Sub000Block117Part011SupportExplicit : Finset ℕ :=
  ([21327] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block117Part011 : ℚ :=
  (394794251225 : ℚ) / 12765755760548464896

def SurrogateDiagonalTailChunk001Sub000Block117Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21327
    = surrogateDiagTailX0RatChunk001Sub000Block117Part011

theorem surrogateDiagonalTailChunk001Sub000Block117Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block117Part011CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block117Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block117Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block117Part011CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block117Part011SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block117Part011] using hcert

def TailChunk001Sub000Block117Part012SupportExplicit : Finset ℕ :=
  ([21329] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block117Part012 : ℚ :=
  (1721154079 : ℚ) / 300876432729735168

def SurrogateDiagonalTailChunk001Sub000Block117Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21329
    = surrogateDiagTailX0RatChunk001Sub000Block117Part012

theorem surrogateDiagonalTailChunk001Sub000Block117Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block117Part012CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block117Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block117Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block117Part012CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block117Part012SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block117Part012] using hcert

def TailChunk001Sub000Block117Part013SupportExplicit : Finset ℕ :=
  ([21331] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block117Part013 : ℚ :=
  (103071806275 : ℚ) / 485559135661140738048

def SurrogateDiagonalTailChunk001Sub000Block117Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21331
    = surrogateDiagTailX0RatChunk001Sub000Block117Part013

theorem surrogateDiagonalTailChunk001Sub000Block117Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block117Part013CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block117Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block117Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block117Part013CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block117Part013SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block117Part013] using hcert

def TailChunk001Sub000Block117Part014SupportExplicit : Finset ℕ :=
  ([21333] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block117Part014 : ℚ :=
  (100402375 : ℚ) / 2461594820840064

def SurrogateDiagonalTailChunk001Sub000Block117Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21333
    = surrogateDiagTailX0RatChunk001Sub000Block117Part014

theorem surrogateDiagonalTailChunk001Sub000Block117Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block117Part014CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block117Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block117Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block117Part014CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block117Part014SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block117Part014] using hcert

def TailChunk001Sub000Block117Part015SupportExplicit : Finset ℕ :=
  ([21334] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block117Part015 : ℚ :=
  (1777888890625 : ℚ) / 8090459439437430642

def SurrogateDiagonalTailChunk001Sub000Block117Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21334
    = surrogateDiagTailX0RatChunk001Sub000Block117Part015

theorem surrogateDiagonalTailChunk001Sub000Block117Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block117Part015CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block117Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block117Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block117Part015CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block117Part015SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block117Part015] using hcert

def TailChunk001Sub000Block117Part016SupportExplicit : Finset ℕ :=
  ([21335] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block117Part016 : ℚ :=
  (52988650183 : ℚ) / 6554910720000000000

def SurrogateDiagonalTailChunk001Sub000Block117Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21335
    = surrogateDiagTailX0RatChunk001Sub000Block117Part016

theorem surrogateDiagonalTailChunk001Sub000Block117Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block117Part016CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block117Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block117Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block117Part016CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block117Part016SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block117Part016] using hcert

def TailChunk001Sub000Block117Part017SupportExplicit : Finset ℕ :=
  ([21337] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block117Part017 : ℚ :=
  (35572768525 : ℚ) / 46221687555310219392

def SurrogateDiagonalTailChunk001Sub000Block117Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21337
    = surrogateDiagTailX0RatChunk001Sub000Block117Part017

theorem surrogateDiagonalTailChunk001Sub000Block117Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block117Part017CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block117Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block117Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block117Part017CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block117Part017SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block117Part017] using hcert

def TailChunk001Sub000Block117Part018SupportExplicit : Finset ℕ :=
  ([21338] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block117Part018 : ℚ :=
  (2278997020125 : ℚ) / 9735778563607662976

def SurrogateDiagonalTailChunk001Sub000Block117Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21338
    = surrogateDiagTailX0RatChunk001Sub000Block117Part018

theorem surrogateDiagonalTailChunk001Sub000Block117Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block117Part018CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block117Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block117Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block117Part018CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block117Part018SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block117Part018] using hcert

def TailChunk001Sub000Block117Part019SupportExplicit : Finset ℕ :=
  ([21341] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block117Part019 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block117Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21341
    = surrogateDiagTailX0RatChunk001Sub000Block117Part019

theorem surrogateDiagonalTailChunk001Sub000Block117Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block117Part019CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block117Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block117Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block117Part019CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block117Part019SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block117Part019] using hcert

def TailChunk001Sub000Block117Part020SupportExplicit : Finset ℕ :=
  ([21342] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block117Part020 : ℚ :=
  (3161908644325 : ℚ) / 6397257774055507968

def SurrogateDiagonalTailChunk001Sub000Block117Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21342
    = surrogateDiagTailX0RatChunk001Sub000Block117Part020

theorem surrogateDiagonalTailChunk001Sub000Block117Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block117Part020CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block117Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block117Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block117Part020CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block117Part020SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block117Part020] using hcert

def TailChunk001Sub000Block117Part021SupportExplicit : Finset ℕ :=
  ([21343] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block117Part021 : ℚ :=
  (581465291075 : ℚ) / 139849756786599542784

def SurrogateDiagonalTailChunk001Sub000Block117Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21343
    = surrogateDiagTailX0RatChunk001Sub000Block117Part021

theorem surrogateDiagonalTailChunk001Sub000Block117Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block117Part021CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block117Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block117Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block117Part021CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block117Part021SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block117Part021] using hcert

def TailChunk001Sub000Block117Part022SupportExplicit : Finset ℕ :=
  ([21345] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block117Part022 : ℚ :=
  (95116675625 : ℚ) / 5234741078779662336

def SurrogateDiagonalTailChunk001Sub000Block117Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21345
    = surrogateDiagTailX0RatChunk001Sub000Block117Part022

theorem surrogateDiagonalTailChunk001Sub000Block117Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block117Part022CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block117Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block117Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block117Part022CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block117Part022SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block117Part022] using hcert

def TailChunk001Sub000Block117Part023SupportExplicit : Finset ℕ :=
  ([21346] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block117Part023 : ℚ :=
  (250652400229 : ℚ) / 937707185472307200

def SurrogateDiagonalTailChunk001Sub000Block117Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21346
    = surrogateDiagTailX0RatChunk001Sub000Block117Part023

theorem surrogateDiagonalTailChunk001Sub000Block117Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block117Part023CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block117Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block117Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block117Part023CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block117Part023SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block117Part023] using hcert

def TailChunk001Sub000Block117Part024SupportExplicit : Finset ℕ :=
  ([21347] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block117Part024 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block117Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21347
    = surrogateDiagTailX0RatChunk001Sub000Block117Part024

theorem surrogateDiagonalTailChunk001Sub000Block117Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block117Part024CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block117Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block117Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block117Part024CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block117Part024SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block117Part024] using hcert

def surrogateDiagonalTailChunk001Sub000Block117HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block117Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block117Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block117Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block117Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block117Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block117Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block117Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block117Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block117Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block117Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block117Head : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block117Part000
    + surrogateDiagTailX0RatChunk001Sub000Block117Part001
    + surrogateDiagTailX0RatChunk001Sub000Block117Part002
    + surrogateDiagTailX0RatChunk001Sub000Block117Part003
    + surrogateDiagTailX0RatChunk001Sub000Block117Part004
    + surrogateDiagTailX0RatChunk001Sub000Block117Part005
    + surrogateDiagTailX0RatChunk001Sub000Block117Part006
    + surrogateDiagTailX0RatChunk001Sub000Block117Part007
    + surrogateDiagTailX0RatChunk001Sub000Block117Part008
    + surrogateDiagTailX0RatChunk001Sub000Block117Part009

def surrogateDiagonalTailChunk001Sub000Block117MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block117Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block117Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block117Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block117Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block117Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block117Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block117Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block117Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block117Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block117Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block117Mid : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block117Part010
    + surrogateDiagTailX0RatChunk001Sub000Block117Part011
    + surrogateDiagTailX0RatChunk001Sub000Block117Part012
    + surrogateDiagTailX0RatChunk001Sub000Block117Part013
    + surrogateDiagTailX0RatChunk001Sub000Block117Part014
    + surrogateDiagTailX0RatChunk001Sub000Block117Part015
    + surrogateDiagTailX0RatChunk001Sub000Block117Part016
    + surrogateDiagTailX0RatChunk001Sub000Block117Part017
    + surrogateDiagTailX0RatChunk001Sub000Block117Part018
    + surrogateDiagTailX0RatChunk001Sub000Block117Part019

def surrogateDiagonalTailChunk001Sub000Block117TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block117Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block117Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block117Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block117Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block117Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block117Tail : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block117Part020
    + surrogateDiagTailX0RatChunk001Sub000Block117Part021
    + surrogateDiagTailX0RatChunk001Sub000Block117Part022
    + surrogateDiagTailX0RatChunk001Sub000Block117Part023
    + surrogateDiagTailX0RatChunk001Sub000Block117Part024

def surrogateDiagonalTailChunk001Sub000Block117Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk001Sub000Block117HeadSum X0
    + surrogateDiagonalTailChunk001Sub000Block117MidSum X0
    + surrogateDiagonalTailChunk001Sub000Block117TailSum X0

def surrogateDiagTailX0RatChunk001Sub000Block117 : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block117Part000
    + surrogateDiagTailX0RatChunk001Sub000Block117Part001
    + surrogateDiagTailX0RatChunk001Sub000Block117Part002
    + surrogateDiagTailX0RatChunk001Sub000Block117Part003
    + surrogateDiagTailX0RatChunk001Sub000Block117Part004
    + surrogateDiagTailX0RatChunk001Sub000Block117Part005
    + surrogateDiagTailX0RatChunk001Sub000Block117Part006
    + surrogateDiagTailX0RatChunk001Sub000Block117Part007
    + surrogateDiagTailX0RatChunk001Sub000Block117Part008
    + surrogateDiagTailX0RatChunk001Sub000Block117Part009
    + surrogateDiagTailX0RatChunk001Sub000Block117Part010
    + surrogateDiagTailX0RatChunk001Sub000Block117Part011
    + surrogateDiagTailX0RatChunk001Sub000Block117Part012
    + surrogateDiagTailX0RatChunk001Sub000Block117Part013
    + surrogateDiagTailX0RatChunk001Sub000Block117Part014
    + surrogateDiagTailX0RatChunk001Sub000Block117Part015
    + surrogateDiagTailX0RatChunk001Sub000Block117Part016
    + surrogateDiagTailX0RatChunk001Sub000Block117Part017
    + surrogateDiagTailX0RatChunk001Sub000Block117Part018
    + surrogateDiagTailX0RatChunk001Sub000Block117Part019
    + surrogateDiagTailX0RatChunk001Sub000Block117Part020
    + surrogateDiagTailX0RatChunk001Sub000Block117Part021
    + surrogateDiagTailX0RatChunk001Sub000Block117Part022
    + surrogateDiagTailX0RatChunk001Sub000Block117Part023
    + surrogateDiagTailX0RatChunk001Sub000Block117Part024

theorem surrogateDiagTailX0RatChunk001Sub000Block117_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk001Sub000Block117Head + surrogateDiagTailX0RatChunk001Sub000Block117Mid + surrogateDiagTailX0RatChunk001Sub000Block117Tail =
      surrogateDiagTailX0RatChunk001Sub000Block117 := by
  unfold surrogateDiagTailX0RatChunk001Sub000Block117Head surrogateDiagTailX0RatChunk001Sub000Block117Mid surrogateDiagTailX0RatChunk001Sub000Block117Tail surrogateDiagTailX0RatChunk001Sub000Block117
  ring

def SurrogateDiagonalTailChunk001Sub000Block117HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block117HeadSum X0 = surrogateDiagTailX0RatChunk001Sub000Block117Head

def SurrogateDiagonalTailChunk001Sub000Block117MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block117MidSum X0 = surrogateDiagTailX0RatChunk001Sub000Block117Mid

def SurrogateDiagonalTailChunk001Sub000Block117TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block117TailSum X0 = surrogateDiagTailX0RatChunk001Sub000Block117Tail

theorem surrogateDiagonalTailChunk001Sub000Block117_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk001Sub000Block117HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk001Sub000Block117MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk001Sub000Block117TailCertificateAt X0) :
    surrogateDiagonalTailChunk001Sub000Block117Sum X0 = surrogateDiagTailX0RatChunk001Sub000Block117 := by
  unfold SurrogateDiagonalTailChunk001Sub000Block117HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk001Sub000Block117MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk001Sub000Block117TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk001Sub000Block117Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk001Sub000Block117_eq_head_add_mid_add_tail

/-- Block 118 covers tail-support indices [12950,12975) and q from 21349 to 21387. -/

def TailChunk001Sub000Block118Part000SupportExplicit : Finset ℕ :=
  ([21349] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block118Part000 : ℚ :=
  (1829313175 : ℚ) / 4280584160805912576

def SurrogateDiagonalTailChunk001Sub000Block118Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21349
    = surrogateDiagTailX0RatChunk001Sub000Block118Part000

theorem surrogateDiagonalTailChunk001Sub000Block118Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block118Part000CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block118Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block118Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block118Part000CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block118Part000SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block118Part000] using hcert

def TailChunk001Sub000Block118Part001SupportExplicit : Finset ℕ :=
  ([21351] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block118Part001 : ℚ :=
  (17989745791 : ℚ) / 2786999590156339200

def SurrogateDiagonalTailChunk001Sub000Block118Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21351
    = surrogateDiagTailX0RatChunk001Sub000Block118Part001

theorem surrogateDiagonalTailChunk001Sub000Block118Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block118Part001CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block118Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block118Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block118Part001CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block118Part001SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block118Part001] using hcert

def TailChunk001Sub000Block118Part002SupportExplicit : Finset ℕ :=
  ([21353] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block118Part002 : ℚ :=
  (139993073 : ℚ) / 756740486129659200

def SurrogateDiagonalTailChunk001Sub000Block118Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21353
    = surrogateDiagTailX0RatChunk001Sub000Block118Part002

theorem surrogateDiagonalTailChunk001Sub000Block118Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block118Part002CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block118Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block118Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block118Part002CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block118Part002SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block118Part002] using hcert

def TailChunk001Sub000Block118Part003SupportExplicit : Finset ℕ :=
  ([21354] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block118Part003 : ℚ :=
  (3165465644125 : ℚ) / 6411661951354915968

def SurrogateDiagonalTailChunk001Sub000Block118Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21354
    = surrogateDiagTailX0RatChunk001Sub000Block118Part003

theorem surrogateDiagonalTailChunk001Sub000Block118Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block118Part003CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block118Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block118Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block118Part003CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block118Part003SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block118Part003] using hcert

def TailChunk001Sub000Block118Part004SupportExplicit : Finset ℕ :=
  ([21355] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block118Part004 : ℚ :=
  (3042151743 : ℚ) / 567475422103009280

def SurrogateDiagonalTailChunk001Sub000Block118Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21355
    = surrogateDiagTailX0RatChunk001Sub000Block118Part004

theorem surrogateDiagonalTailChunk001Sub000Block118Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block118Part004CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block118Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block118Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block118Part004CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block118Part004SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block118Part004] using hcert

def TailChunk001Sub000Block118Part005SupportExplicit : Finset ℕ :=
  ([21358] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block118Part005 : ℚ :=
  (68857269307 : ℚ) / 297049519048204800

def SurrogateDiagonalTailChunk001Sub000Block118Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21358
    = surrogateDiagTailX0RatChunk001Sub000Block118Part005

theorem surrogateDiagonalTailChunk001Sub000Block118Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block118Part005CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block118Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block118Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block118Part005CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block118Part005SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block118Part005] using hcert

def TailChunk001Sub000Block118Part006SupportExplicit : Finset ℕ :=
  ([21359] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block118Part006 : ℚ :=
  (30315045997 : ℚ) / 12283163360899891200

def SurrogateDiagonalTailChunk001Sub000Block118Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21359
    = surrogateDiagTailX0RatChunk001Sub000Block118Part006

theorem surrogateDiagonalTailChunk001Sub000Block118Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block118Part006CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block118Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block118Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block118Part006CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block118Part006SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block118Part006] using hcert

def TailChunk001Sub000Block118Part007SupportExplicit : Finset ℕ :=
  ([21361] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block118Part007 : ℚ :=
  (92923683 : ℚ) / 240018980864000000

def SurrogateDiagonalTailChunk001Sub000Block118Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21361
    = surrogateDiagTailX0RatChunk001Sub000Block118Part007

theorem surrogateDiagonalTailChunk001Sub000Block118Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block118Part007CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block118Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block118Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block118Part007CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block118Part007SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block118Part007] using hcert

def TailChunk001Sub000Block118Part008SupportExplicit : Finset ℕ :=
  ([21362] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block118Part008 : ℚ :=
  (4119145977 : ℚ) / 14757831142700000

def SurrogateDiagonalTailChunk001Sub000Block118Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21362
    = surrogateDiagTailX0RatChunk001Sub000Block118Part008

theorem surrogateDiagonalTailChunk001Sub000Block118Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block118Part008CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block118Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block118Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block118Part008CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block118Part008SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block118Part008] using hcert

def TailChunk001Sub000Block118Part009SupportExplicit : Finset ℕ :=
  ([21363] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block118Part009 : ℚ :=
  (5001 : ℚ) / 822375101235200

def SurrogateDiagonalTailChunk001Sub000Block118Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21363
    = surrogateDiagTailX0RatChunk001Sub000Block118Part009

theorem surrogateDiagonalTailChunk001Sub000Block118Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block118Part009CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block118Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block118Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block118Part009CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block118Part009SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block118Part009] using hcert

def TailChunk001Sub000Block118Part010SupportExplicit : Finset ℕ :=
  ([21365] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block118Part010 : ℚ :=
  (1141874653375 : ℚ) / 213202258165411872768

def SurrogateDiagonalTailChunk001Sub000Block118Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21365
    = surrogateDiagTailX0RatChunk001Sub000Block118Part010

theorem surrogateDiagonalTailChunk001Sub000Block118Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block118Part010CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block118Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block118Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block118Part010CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block118Part010SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block118Part010] using hcert

def TailChunk001Sub000Block118Part011SupportExplicit : Finset ℕ :=
  ([21367] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block118Part011 : ℚ :=
  (91923197925 : ℚ) / 144806558563991289856

def SurrogateDiagonalTailChunk001Sub000Block118Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21367
    = surrogateDiagTailX0RatChunk001Sub000Block118Part011

theorem surrogateDiagonalTailChunk001Sub000Block118Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block118Part011CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block118Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block118Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block118Part011CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block118Part011SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block118Part011] using hcert

def TailChunk001Sub000Block118Part012SupportExplicit : Finset ℕ :=
  ([21369] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block118Part012 : ℚ :=
  (4946925 : ℚ) / 1455064883396608

def SurrogateDiagonalTailChunk001Sub000Block118Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21369
    = surrogateDiagTailX0RatChunk001Sub000Block118Part012

theorem surrogateDiagonalTailChunk001Sub000Block118Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block118Part012CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block118Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block118Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block118Part012CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block118Part012SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block118Part012] using hcert

def TailChunk001Sub000Block118Part013SupportExplicit : Finset ℕ :=
  ([21370] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block118Part013 : ℚ :=
  (5134856775325 : ℚ) / 13325141135338242048

def SurrogateDiagonalTailChunk001Sub000Block118Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21370
    = surrogateDiagTailX0RatChunk001Sub000Block118Part013

theorem surrogateDiagonalTailChunk001Sub000Block118Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block118Part013CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block118Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block118Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block118Part013CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block118Part013SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block118Part013] using hcert

def TailChunk001Sub000Block118Part014SupportExplicit : Finset ℕ :=
  ([21371] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block118Part014 : ℚ :=
  (183501421 : ℚ) / 34587816167197440

def SurrogateDiagonalTailChunk001Sub000Block118Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21371
    = surrogateDiagTailX0RatChunk001Sub000Block118Part014

theorem surrogateDiagonalTailChunk001Sub000Block118Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block118Part014CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block118Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block118Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block118Part014CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block118Part014SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block118Part014] using hcert

def TailChunk001Sub000Block118Part015SupportExplicit : Finset ℕ :=
  ([21373] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block118Part015 : ℚ :=
  (2897116807 : ℚ) / 1166526791788216320

def SurrogateDiagonalTailChunk001Sub000Block118Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21373
    = surrogateDiagTailX0RatChunk001Sub000Block118Part015

theorem surrogateDiagonalTailChunk001Sub000Block118Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block118Part015CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block118Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block118Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block118Part015CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block118Part015SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block118Part015] using hcert

def TailChunk001Sub000Block118Part016SupportExplicit : Finset ℕ :=
  ([21374] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block118Part016 : ℚ :=
  (1784562015625 : ℚ) / 8151312570798864402

def SurrogateDiagonalTailChunk001Sub000Block118Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21374
    = surrogateDiagTailX0RatChunk001Sub000Block118Part016

theorem surrogateDiagonalTailChunk001Sub000Block118Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block118Part016CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block118Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block118Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block118Part016CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block118Part016SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block118Part016] using hcert

def TailChunk001Sub000Block118Part017SupportExplicit : Finset ℕ :=
  ([21377] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block118Part017 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block118Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21377
    = surrogateDiagTailX0RatChunk001Sub000Block118Part017

theorem surrogateDiagonalTailChunk001Sub000Block118Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block118Part017CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block118Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block118Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block118Part017CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block118Part017SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block118Part017] using hcert

def TailChunk001Sub000Block118Part018SupportExplicit : Finset ℕ :=
  ([21378] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block118Part018 : ℚ :=
  (95112404525 : ℚ) / 127891867203108864

def SurrogateDiagonalTailChunk001Sub000Block118Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21378
    = surrogateDiagTailX0RatChunk001Sub000Block118Part018

theorem surrogateDiagonalTailChunk001Sub000Block118Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block118Part018CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block118Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block118Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block118Part018CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block118Part018SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block118Part018] using hcert

def TailChunk001Sub000Block118Part019SupportExplicit : Finset ℕ :=
  ([21379] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block118Part019 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block118Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21379
    = surrogateDiagTailX0RatChunk001Sub000Block118Part019

theorem surrogateDiagonalTailChunk001Sub000Block118Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block118Part019CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block118Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block118Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block118Part019CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block118Part019SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block118Part019] using hcert

def TailChunk001Sub000Block118Part020SupportExplicit : Finset ℕ :=
  ([21381] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block118Part020 : ℚ :=
  (125025 : ℚ) / 20628766452603008

def SurrogateDiagonalTailChunk001Sub000Block118Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21381
    = surrogateDiagTailX0RatChunk001Sub000Block118Part020

theorem surrogateDiagonalTailChunk001Sub000Block118Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block118Part020CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block118Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block118Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block118Part020CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block118Part020SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block118Part020] using hcert

def TailChunk001Sub000Block118Part021SupportExplicit : Finset ℕ :=
  ([21382] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block118Part021 : ℚ :=
  (2857437025 : ℚ) / 13061638836616242

def SurrogateDiagonalTailChunk001Sub000Block118Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21382
    = surrogateDiagTailX0RatChunk001Sub000Block118Part021

theorem surrogateDiagonalTailChunk001Sub000Block118Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block118Part021CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block118Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block118Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block118Part021CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block118Part021SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block118Part021] using hcert

def TailChunk001Sub000Block118Part022SupportExplicit : Finset ℕ :=
  ([21383] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block118Part022 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block118Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21383
    = surrogateDiagTailX0RatChunk001Sub000Block118Part022

theorem surrogateDiagonalTailChunk001Sub000Block118Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block118Part022CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block118Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block118Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block118Part022CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block118Part022SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block118Part022] using hcert

def TailChunk001Sub000Block118Part023SupportExplicit : Finset ℕ :=
  ([21385] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block118Part023 : ℚ :=
  (308015445275 : ℚ) / 9628045847351525376

def SurrogateDiagonalTailChunk001Sub000Block118Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21385
    = surrogateDiagTailX0RatChunk001Sub000Block118Part023

theorem surrogateDiagonalTailChunk001Sub000Block118Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block118Part023CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block118Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block118Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block118Part023CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block118Part023SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block118Part023] using hcert

def TailChunk001Sub000Block118Part024SupportExplicit : Finset ℕ :=
  ([21387] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block118Part024 : ℚ :=
  (41675 : ℚ) / 6883978359177216

def SurrogateDiagonalTailChunk001Sub000Block118Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21387
    = surrogateDiagTailX0RatChunk001Sub000Block118Part024

theorem surrogateDiagonalTailChunk001Sub000Block118Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block118Part024CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block118Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block118Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block118Part024CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block118Part024SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block118Part024] using hcert

def surrogateDiagonalTailChunk001Sub000Block118HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block118Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block118Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block118Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block118Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block118Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block118Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block118Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block118Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block118Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block118Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block118Head : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block118Part000
    + surrogateDiagTailX0RatChunk001Sub000Block118Part001
    + surrogateDiagTailX0RatChunk001Sub000Block118Part002
    + surrogateDiagTailX0RatChunk001Sub000Block118Part003
    + surrogateDiagTailX0RatChunk001Sub000Block118Part004
    + surrogateDiagTailX0RatChunk001Sub000Block118Part005
    + surrogateDiagTailX0RatChunk001Sub000Block118Part006
    + surrogateDiagTailX0RatChunk001Sub000Block118Part007
    + surrogateDiagTailX0RatChunk001Sub000Block118Part008
    + surrogateDiagTailX0RatChunk001Sub000Block118Part009

def surrogateDiagonalTailChunk001Sub000Block118MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block118Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block118Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block118Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block118Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block118Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block118Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block118Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block118Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block118Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block118Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block118Mid : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block118Part010
    + surrogateDiagTailX0RatChunk001Sub000Block118Part011
    + surrogateDiagTailX0RatChunk001Sub000Block118Part012
    + surrogateDiagTailX0RatChunk001Sub000Block118Part013
    + surrogateDiagTailX0RatChunk001Sub000Block118Part014
    + surrogateDiagTailX0RatChunk001Sub000Block118Part015
    + surrogateDiagTailX0RatChunk001Sub000Block118Part016
    + surrogateDiagTailX0RatChunk001Sub000Block118Part017
    + surrogateDiagTailX0RatChunk001Sub000Block118Part018
    + surrogateDiagTailX0RatChunk001Sub000Block118Part019

def surrogateDiagonalTailChunk001Sub000Block118TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block118Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block118Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block118Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block118Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block118Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block118Tail : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block118Part020
    + surrogateDiagTailX0RatChunk001Sub000Block118Part021
    + surrogateDiagTailX0RatChunk001Sub000Block118Part022
    + surrogateDiagTailX0RatChunk001Sub000Block118Part023
    + surrogateDiagTailX0RatChunk001Sub000Block118Part024

def surrogateDiagonalTailChunk001Sub000Block118Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk001Sub000Block118HeadSum X0
    + surrogateDiagonalTailChunk001Sub000Block118MidSum X0
    + surrogateDiagonalTailChunk001Sub000Block118TailSum X0

def surrogateDiagTailX0RatChunk001Sub000Block118 : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block118Part000
    + surrogateDiagTailX0RatChunk001Sub000Block118Part001
    + surrogateDiagTailX0RatChunk001Sub000Block118Part002
    + surrogateDiagTailX0RatChunk001Sub000Block118Part003
    + surrogateDiagTailX0RatChunk001Sub000Block118Part004
    + surrogateDiagTailX0RatChunk001Sub000Block118Part005
    + surrogateDiagTailX0RatChunk001Sub000Block118Part006
    + surrogateDiagTailX0RatChunk001Sub000Block118Part007
    + surrogateDiagTailX0RatChunk001Sub000Block118Part008
    + surrogateDiagTailX0RatChunk001Sub000Block118Part009
    + surrogateDiagTailX0RatChunk001Sub000Block118Part010
    + surrogateDiagTailX0RatChunk001Sub000Block118Part011
    + surrogateDiagTailX0RatChunk001Sub000Block118Part012
    + surrogateDiagTailX0RatChunk001Sub000Block118Part013
    + surrogateDiagTailX0RatChunk001Sub000Block118Part014
    + surrogateDiagTailX0RatChunk001Sub000Block118Part015
    + surrogateDiagTailX0RatChunk001Sub000Block118Part016
    + surrogateDiagTailX0RatChunk001Sub000Block118Part017
    + surrogateDiagTailX0RatChunk001Sub000Block118Part018
    + surrogateDiagTailX0RatChunk001Sub000Block118Part019
    + surrogateDiagTailX0RatChunk001Sub000Block118Part020
    + surrogateDiagTailX0RatChunk001Sub000Block118Part021
    + surrogateDiagTailX0RatChunk001Sub000Block118Part022
    + surrogateDiagTailX0RatChunk001Sub000Block118Part023
    + surrogateDiagTailX0RatChunk001Sub000Block118Part024

theorem surrogateDiagTailX0RatChunk001Sub000Block118_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk001Sub000Block118Head + surrogateDiagTailX0RatChunk001Sub000Block118Mid + surrogateDiagTailX0RatChunk001Sub000Block118Tail =
      surrogateDiagTailX0RatChunk001Sub000Block118 := by
  unfold surrogateDiagTailX0RatChunk001Sub000Block118Head surrogateDiagTailX0RatChunk001Sub000Block118Mid surrogateDiagTailX0RatChunk001Sub000Block118Tail surrogateDiagTailX0RatChunk001Sub000Block118
  ring

def SurrogateDiagonalTailChunk001Sub000Block118HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block118HeadSum X0 = surrogateDiagTailX0RatChunk001Sub000Block118Head

def SurrogateDiagonalTailChunk001Sub000Block118MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block118MidSum X0 = surrogateDiagTailX0RatChunk001Sub000Block118Mid

def SurrogateDiagonalTailChunk001Sub000Block118TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block118TailSum X0 = surrogateDiagTailX0RatChunk001Sub000Block118Tail

theorem surrogateDiagonalTailChunk001Sub000Block118_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk001Sub000Block118HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk001Sub000Block118MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk001Sub000Block118TailCertificateAt X0) :
    surrogateDiagonalTailChunk001Sub000Block118Sum X0 = surrogateDiagTailX0RatChunk001Sub000Block118 := by
  unfold SurrogateDiagonalTailChunk001Sub000Block118HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk001Sub000Block118MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk001Sub000Block118TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk001Sub000Block118Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk001Sub000Block118_eq_head_add_mid_add_tail

/-- Block 119 covers tail-support indices [12975,13000) and q from 21389 to 21430. -/

def TailChunk001Sub000Block119Part000SupportExplicit : Finset ℕ :=
  ([21389] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block119Part000 : ℚ :=
  (18774882875 : ℚ) / 81421106489083035648

def SurrogateDiagonalTailChunk001Sub000Block119Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21389
    = surrogateDiagTailX0RatChunk001Sub000Block119Part000

theorem surrogateDiagonalTailChunk001Sub000Block119Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block119Part000CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block119Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block119Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block119Part000CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block119Part000SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block119Part000] using hcert

def TailChunk001Sub000Block119Part001SupportExplicit : Finset ℕ :=
  ([21390] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block119Part001 : ℚ :=
  (7966605203 : ℚ) / 7066914796339200

def SurrogateDiagonalTailChunk001Sub000Block119Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21390
    = surrogateDiagTailX0RatChunk001Sub000Block119Part001

theorem surrogateDiagonalTailChunk001Sub000Block119Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block119Part001CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block119Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block119Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block119Part001CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block119Part001SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block119Part001] using hcert

def TailChunk001Sub000Block119Part002SupportExplicit : Finset ℕ :=
  ([21391] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block119Part002 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block119Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21391
    = surrogateDiagTailX0RatChunk001Sub000Block119Part002

theorem surrogateDiagonalTailChunk001Sub000Block119Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block119Part002CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block119Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block119Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block119Part002CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block119Part002SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block119Part002] using hcert

def TailChunk001Sub000Block119Part003SupportExplicit : Finset ℕ :=
  ([21394] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block119Part003 : ℚ :=
  (6540451827175 : ℚ) / 26185576610368291968

def SurrogateDiagonalTailChunk001Sub000Block119Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21394
    = surrogateDiagTailX0RatChunk001Sub000Block119Part003

theorem surrogateDiagonalTailChunk001Sub000Block119Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block119Part003CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block119Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block119Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block119Part003CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block119Part003SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block119Part003] using hcert

def TailChunk001Sub000Block119Part004SupportExplicit : Finset ℕ :=
  ([21395] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block119Part004 : ℚ :=
  (18238720829 : ℚ) / 1160603066121584640

def SurrogateDiagonalTailChunk001Sub000Block119Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21395
    = surrogateDiagTailX0RatChunk001Sub000Block119Part004

theorem surrogateDiagonalTailChunk001Sub000Block119Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block119Part004CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block119Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block119Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block119Part004CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block119Part004SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block119Part004] using hcert

def TailChunk001Sub000Block119Part005SupportExplicit : Finset ℕ :=
  ([21397] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block119Part005 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block119Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21397
    = surrogateDiagTailX0RatChunk001Sub000Block119Part005

theorem surrogateDiagonalTailChunk001Sub000Block119Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block119Part005CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block119Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block119Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block119Part005CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block119Part005SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block119Part005] using hcert

def TailChunk001Sub000Block119Part006SupportExplicit : Finset ℕ :=
  ([21398] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block119Part006 : ℚ :=
  (699655151075 : ℚ) / 2630247423146330112

def SurrogateDiagonalTailChunk001Sub000Block119Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21398
    = surrogateDiagTailX0RatChunk001Sub000Block119Part006

theorem surrogateDiagonalTailChunk001Sub000Block119Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block119Part006CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block119Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block119Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block119Part006CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block119Part006SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block119Part006] using hcert

def TailChunk001Sub000Block119Part007SupportExplicit : Finset ℕ :=
  ([21399] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block119Part007 : ℚ :=
  (716351202175 : ℚ) / 55685606619820935168

def SurrogateDiagonalTailChunk001Sub000Block119Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21399
    = surrogateDiagTailX0RatChunk001Sub000Block119Part007

theorem surrogateDiagonalTailChunk001Sub000Block119Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block119Part007CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block119Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block119Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block119Part007CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block119Part007SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block119Part007] using hcert

def TailChunk001Sub000Block119Part008SupportExplicit : Finset ℕ :=
  ([21401] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block119Part008 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block119Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21401
    = surrogateDiagTailX0RatChunk001Sub000Block119Part008

theorem surrogateDiagonalTailChunk001Sub000Block119Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block119Part008CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block119Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block119Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block119Part008CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block119Part008SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block119Part008] using hcert

def TailChunk001Sub000Block119Part009SupportExplicit : Finset ℕ :=
  ([21403] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block119Part009 : ℚ :=
  (400402426675 : ℚ) / 410420791846308937728

def SurrogateDiagonalTailChunk001Sub000Block119Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21403
    = surrogateDiagTailX0RatChunk001Sub000Block119Part009

theorem surrogateDiagonalTailChunk001Sub000Block119Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block119Part009CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block119Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block119Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block119Part009CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block119Part009SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block119Part009] using hcert

def TailChunk001Sub000Block119Part010SupportExplicit : Finset ℕ :=
  ([21405] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block119Part010 : ℚ :=
  (95650782425 : ℚ) / 5293890108805779456

def SurrogateDiagonalTailChunk001Sub000Block119Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21405
    = surrogateDiagTailX0RatChunk001Sub000Block119Part010

theorem surrogateDiagonalTailChunk001Sub000Block119Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block119Part010CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block119Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block119Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block119Part010CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block119Part010SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block119Part010] using hcert

def TailChunk001Sub000Block119Part011SupportExplicit : Finset ℕ :=
  ([21406] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block119Part011 : ℚ :=
  (95792945441 : ℚ) / 235059713070105600

def SurrogateDiagonalTailChunk001Sub000Block119Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21406
    = surrogateDiagTailX0RatChunk001Sub000Block119Part011

theorem surrogateDiagonalTailChunk001Sub000Block119Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block119Part011CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block119Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block119Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block119Part011CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block119Part011SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block119Part011] using hcert

def TailChunk001Sub000Block119Part012SupportExplicit : Finset ℕ :=
  ([21407] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block119Part012 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block119Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21407
    = surrogateDiagTailX0RatChunk001Sub000Block119Part012

theorem surrogateDiagonalTailChunk001Sub000Block119Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block119Part012CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block119Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block119Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block119Part012CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block119Part012SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block119Part012] using hcert

def TailChunk001Sub000Block119Part013SupportExplicit : Finset ℕ :=
  ([21409] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block119Part013 : ℚ :=
  (13086727 : ℚ) / 60726088393120800

def SurrogateDiagonalTailChunk001Sub000Block119Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21409
    = surrogateDiagTailX0RatChunk001Sub000Block119Part013

theorem surrogateDiagonalTailChunk001Sub000Block119Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block119Part013CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block119Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block119Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block119Part013CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block119Part013SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block119Part013] using hcert

def TailChunk001Sub000Block119Part014SupportExplicit : Finset ℕ :=
  ([21410] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block119Part014 : ℚ :=
  (194701332319 : ℚ) / 537009426105139200

def SurrogateDiagonalTailChunk001Sub000Block119Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21410
    = surrogateDiagTailX0RatChunk001Sub000Block119Part014

theorem surrogateDiagonalTailChunk001Sub000Block119Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block119Part014CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block119Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block119Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block119Part014CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block119Part014SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block119Part014] using hcert

def TailChunk001Sub000Block119Part015SupportExplicit : Finset ℕ :=
  ([21414] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block119Part015 : ℚ :=
  (759991215175 : ℚ) / 1407146845199380992

def SurrogateDiagonalTailChunk001Sub000Block119Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21414
    = surrogateDiagTailX0RatChunk001Sub000Block119Part015

theorem surrogateDiagonalTailChunk001Sub000Block119Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block119Part015CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block119Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block119Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block119Part015CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block119Part015SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block119Part015] using hcert

def TailChunk001Sub000Block119Part016SupportExplicit : Finset ℕ :=
  ([21415] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block119Part016 : ℚ :=
  (382406967375 : ℚ) / 71735184777098008576

def SurrogateDiagonalTailChunk001Sub000Block119Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21415
    = surrogateDiagTailX0RatChunk001Sub000Block119Part016

theorem surrogateDiagonalTailChunk001Sub000Block119Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block119Part016CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block119Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block119Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block119Part016CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block119Part016SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block119Part016] using hcert

def TailChunk001Sub000Block119Part017SupportExplicit : Finset ℕ :=
  ([21418] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block119Part017 : ℚ :=
  (1791916890625 : ℚ) / 8218646814481319712

def SurrogateDiagonalTailChunk001Sub000Block119Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21418
    = surrogateDiagTailX0RatChunk001Sub000Block119Part017

theorem surrogateDiagonalTailChunk001Sub000Block119Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block119Part017CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block119Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block119Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block119Part017CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block119Part017SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block119Part017] using hcert

def TailChunk001Sub000Block119Part018SupportExplicit : Finset ℕ :=
  ([21419] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block119Part018 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block119Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21419
    = surrogateDiagTailX0RatChunk001Sub000Block119Part018

theorem surrogateDiagonalTailChunk001Sub000Block119Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block119Part018CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block119Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block119Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block119Part018CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block119Part018SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block119Part018] using hcert

def TailChunk001Sub000Block119Part019SupportExplicit : Finset ℕ :=
  ([21421] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block119Part019 : ℚ :=
  (120780191 : ℚ) / 255056112272250000

def SurrogateDiagonalTailChunk001Sub000Block119Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21421
    = surrogateDiagTailX0RatChunk001Sub000Block119Part019

theorem surrogateDiagonalTailChunk001Sub000Block119Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block119Part019CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block119Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block119Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block119Part019CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block119Part019SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block119Part019] using hcert

def TailChunk001Sub000Block119Part020SupportExplicit : Finset ℕ :=
  ([21422] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block119Part020 : ℚ :=
  (2868138025 : ℚ) / 13159661962921362

def SurrogateDiagonalTailChunk001Sub000Block119Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21422
    = surrogateDiagTailX0RatChunk001Sub000Block119Part020

theorem surrogateDiagonalTailChunk001Sub000Block119Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block119Part020CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block119Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block119Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block119Part020CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block119Part020SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block119Part020] using hcert

def TailChunk001Sub000Block119Part021SupportExplicit : Finset ℕ :=
  ([21423] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block119Part021 : ℚ :=
  (144615389275 : ℚ) / 91319128763859468288

def SurrogateDiagonalTailChunk001Sub000Block119Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21423
    = surrogateDiagTailX0RatChunk001Sub000Block119Part021

theorem surrogateDiagonalTailChunk001Sub000Block119Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block119Part021CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block119Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block119Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block119Part021CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block119Part021SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block119Part021] using hcert

def TailChunk001Sub000Block119Part022SupportExplicit : Finset ℕ :=
  ([21426] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block119Part022 : ℚ :=
  (127473985717 : ℚ) / 259943940008323200

def SurrogateDiagonalTailChunk001Sub000Block119Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21426
    = surrogateDiagTailX0RatChunk001Sub000Block119Part022

theorem surrogateDiagonalTailChunk001Sub000Block119Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block119Part022CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block119Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block119Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block119Part022CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block119Part022SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block119Part022] using hcert

def TailChunk001Sub000Block119Part023SupportExplicit : Finset ℕ :=
  ([21427] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block119Part023 : ℚ :=
  (23483996113 : ℚ) / 11365212430784563200

def SurrogateDiagonalTailChunk001Sub000Block119Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21427
    = surrogateDiagTailX0RatChunk001Sub000Block119Part023

theorem surrogateDiagonalTailChunk001Sub000Block119Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block119Part023CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block119Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block119Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block119Part023CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block119Part023SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block119Part023] using hcert

def TailChunk001Sub000Block119Part024SupportExplicit : Finset ℕ :=
  ([21430] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block119Part024 : ℚ :=
  (4876633414525 : ℚ) / 13475493850031474688

def SurrogateDiagonalTailChunk001Sub000Block119Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21430
    = surrogateDiagTailX0RatChunk001Sub000Block119Part024

theorem surrogateDiagonalTailChunk001Sub000Block119Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block119Part024CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block119Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block119Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block119Part024CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block119Part024SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block119Part024] using hcert

def surrogateDiagonalTailChunk001Sub000Block119HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block119Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block119Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block119Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block119Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block119Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block119Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block119Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block119Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block119Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block119Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block119Head : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block119Part000
    + surrogateDiagTailX0RatChunk001Sub000Block119Part001
    + surrogateDiagTailX0RatChunk001Sub000Block119Part002
    + surrogateDiagTailX0RatChunk001Sub000Block119Part003
    + surrogateDiagTailX0RatChunk001Sub000Block119Part004
    + surrogateDiagTailX0RatChunk001Sub000Block119Part005
    + surrogateDiagTailX0RatChunk001Sub000Block119Part006
    + surrogateDiagTailX0RatChunk001Sub000Block119Part007
    + surrogateDiagTailX0RatChunk001Sub000Block119Part008
    + surrogateDiagTailX0RatChunk001Sub000Block119Part009

def surrogateDiagonalTailChunk001Sub000Block119MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block119Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block119Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block119Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block119Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block119Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block119Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block119Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block119Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block119Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block119Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block119Mid : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block119Part010
    + surrogateDiagTailX0RatChunk001Sub000Block119Part011
    + surrogateDiagTailX0RatChunk001Sub000Block119Part012
    + surrogateDiagTailX0RatChunk001Sub000Block119Part013
    + surrogateDiagTailX0RatChunk001Sub000Block119Part014
    + surrogateDiagTailX0RatChunk001Sub000Block119Part015
    + surrogateDiagTailX0RatChunk001Sub000Block119Part016
    + surrogateDiagTailX0RatChunk001Sub000Block119Part017
    + surrogateDiagTailX0RatChunk001Sub000Block119Part018
    + surrogateDiagTailX0RatChunk001Sub000Block119Part019

def surrogateDiagonalTailChunk001Sub000Block119TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block119Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block119Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block119Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block119Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block119Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block119Tail : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block119Part020
    + surrogateDiagTailX0RatChunk001Sub000Block119Part021
    + surrogateDiagTailX0RatChunk001Sub000Block119Part022
    + surrogateDiagTailX0RatChunk001Sub000Block119Part023
    + surrogateDiagTailX0RatChunk001Sub000Block119Part024

def surrogateDiagonalTailChunk001Sub000Block119Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk001Sub000Block119HeadSum X0
    + surrogateDiagonalTailChunk001Sub000Block119MidSum X0
    + surrogateDiagonalTailChunk001Sub000Block119TailSum X0

def surrogateDiagTailX0RatChunk001Sub000Block119 : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block119Part000
    + surrogateDiagTailX0RatChunk001Sub000Block119Part001
    + surrogateDiagTailX0RatChunk001Sub000Block119Part002
    + surrogateDiagTailX0RatChunk001Sub000Block119Part003
    + surrogateDiagTailX0RatChunk001Sub000Block119Part004
    + surrogateDiagTailX0RatChunk001Sub000Block119Part005
    + surrogateDiagTailX0RatChunk001Sub000Block119Part006
    + surrogateDiagTailX0RatChunk001Sub000Block119Part007
    + surrogateDiagTailX0RatChunk001Sub000Block119Part008
    + surrogateDiagTailX0RatChunk001Sub000Block119Part009
    + surrogateDiagTailX0RatChunk001Sub000Block119Part010
    + surrogateDiagTailX0RatChunk001Sub000Block119Part011
    + surrogateDiagTailX0RatChunk001Sub000Block119Part012
    + surrogateDiagTailX0RatChunk001Sub000Block119Part013
    + surrogateDiagTailX0RatChunk001Sub000Block119Part014
    + surrogateDiagTailX0RatChunk001Sub000Block119Part015
    + surrogateDiagTailX0RatChunk001Sub000Block119Part016
    + surrogateDiagTailX0RatChunk001Sub000Block119Part017
    + surrogateDiagTailX0RatChunk001Sub000Block119Part018
    + surrogateDiagTailX0RatChunk001Sub000Block119Part019
    + surrogateDiagTailX0RatChunk001Sub000Block119Part020
    + surrogateDiagTailX0RatChunk001Sub000Block119Part021
    + surrogateDiagTailX0RatChunk001Sub000Block119Part022
    + surrogateDiagTailX0RatChunk001Sub000Block119Part023
    + surrogateDiagTailX0RatChunk001Sub000Block119Part024

theorem surrogateDiagTailX0RatChunk001Sub000Block119_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk001Sub000Block119Head + surrogateDiagTailX0RatChunk001Sub000Block119Mid + surrogateDiagTailX0RatChunk001Sub000Block119Tail =
      surrogateDiagTailX0RatChunk001Sub000Block119 := by
  unfold surrogateDiagTailX0RatChunk001Sub000Block119Head surrogateDiagTailX0RatChunk001Sub000Block119Mid surrogateDiagTailX0RatChunk001Sub000Block119Tail surrogateDiagTailX0RatChunk001Sub000Block119
  ring

def SurrogateDiagonalTailChunk001Sub000Block119HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block119HeadSum X0 = surrogateDiagTailX0RatChunk001Sub000Block119Head

def SurrogateDiagonalTailChunk001Sub000Block119MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block119MidSum X0 = surrogateDiagTailX0RatChunk001Sub000Block119Mid

def SurrogateDiagonalTailChunk001Sub000Block119TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block119TailSum X0 = surrogateDiagTailX0RatChunk001Sub000Block119Tail

theorem surrogateDiagonalTailChunk001Sub000Block119_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk001Sub000Block119HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk001Sub000Block119MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk001Sub000Block119TailCertificateAt X0) :
    surrogateDiagonalTailChunk001Sub000Block119Sum X0 = surrogateDiagTailX0RatChunk001Sub000Block119 := by
  unfold SurrogateDiagonalTailChunk001Sub000Block119HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk001Sub000Block119MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk001Sub000Block119TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk001Sub000Block119Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk001Sub000Block119_eq_head_add_mid_add_tail

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

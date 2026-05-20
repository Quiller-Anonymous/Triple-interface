import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0TailPilot25

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

open scoped BigOperators

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

/- Generated direct-term certificate blocks for tail chunk 000, subchunk 000, blocks [23,24). -/

/- Block 023 covers tail-support indices [575,600) and q from 997 to 1038. -/

def TailChunk000Sub000Block023Part000SupportExplicit : Finset ℕ :=
  ([997] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block023Part000 : ℚ :=
  (155189655125 : ℚ) / 1230365704256064

def SurrogateDiagonalTailChunk000Sub000Block023Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 997
    = surrogateDiagTailX0RatChunk000Sub000Block023Part000

theorem surrogateDiagonalTailChunk000Sub000Block023Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block023Part000CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block023Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block023Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block023Part000CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block023Part000SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block023Part000] using hcert

def TailChunk000Sub000Block023Part001SupportExplicit : Finset ℕ :=
  ([998] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block023Part001 : ℚ :=
  (155345498875 : ℚ) / 153795713032008

def SurrogateDiagonalTailChunk000Sub000Block023Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 998
    = surrogateDiagTailX0RatChunk000Sub000Block023Part001

theorem surrogateDiagonalTailChunk000Sub000Block023Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block023Part001CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block023Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block023Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block023Part001CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block023Part001SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block023Part001] using hcert

def TailChunk000Sub000Block023Part002SupportExplicit : Finset ℕ :=
  ([1001] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block023Part002 : ℚ :=
  (83432447 : ℚ) / 248881766400

def SurrogateDiagonalTailChunk000Sub000Block023Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1001
    = surrogateDiagTailX0RatChunk000Sub000Block023Part002

theorem surrogateDiagonalTailChunk000Sub000Block023Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block023Part002CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block023Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block023Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block023Part002CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block023Part002SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block023Part002] using hcert

def TailChunk000Sub000Block023Part003SupportExplicit : Finset ℕ :=
  ([1002] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block023Part003 : ℚ :=
  (97085644075 : ℚ) / 30379400105088

def SurrogateDiagonalTailChunk000Sub000Block023Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1002
    = surrogateDiagTailX0RatChunk000Sub000Block023Part003

theorem surrogateDiagonalTailChunk000Sub000Block023Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block023Part003CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block023Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block023Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block023Part003CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block023Part003SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block023Part003] using hcert

def TailChunk000Sub000Block023Part004SupportExplicit : Finset ℕ :=
  ([1003] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block023Part004 : ℚ :=
  (96970452675 : ℚ) / 618155174526976

def SurrogateDiagonalTailChunk000Sub000Block023Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1003
    = surrogateDiagTailX0RatChunk000Sub000Block023Part004

theorem surrogateDiagonalTailChunk000Sub000Block023Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block023Part004CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block023Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block023Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block023Part004CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block023Part004SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block023Part004] using hcert

def TailChunk000Sub000Block023Part005SupportExplicit : Finset ℕ :=
  ([1005] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block023Part005 : ℚ :=
  (165845786275 : ℚ) / 194340156899328

def SurrogateDiagonalTailChunk000Sub000Block023Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1005
    = surrogateDiagTailX0RatChunk000Sub000Block023Part005

theorem surrogateDiagonalTailChunk000Sub000Block023Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block023Part005CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block023Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block023Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block023Part005CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block023Part005SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block023Part005] using hcert

def TailChunk000Sub000Block023Part006SupportExplicit : Finset ℕ :=
  ([1006] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block023Part006 : ℚ :=
  (5920410600 : ℚ) / 6616533043667

def SurrogateDiagonalTailChunk000Sub000Block023Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1006
    = surrogateDiagTailX0RatChunk000Sub000Block023Part006

theorem surrogateDiagonalTailChunk000Sub000Block023Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block023Part006CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block023Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block023Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block023Part006CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block023Part006SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block023Part006] using hcert

def TailChunk000Sub000Block023Part007SupportExplicit : Finset ℕ :=
  ([1007] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block023Part007 : ℚ :=
  (177021575 : ℚ) / 1153391992272

def SurrogateDiagonalTailChunk000Sub000Block023Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1007
    = surrogateDiagTailX0RatChunk000Sub000Block023Part007

theorem surrogateDiagonalTailChunk000Sub000Block023Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block023Part007CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block023Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block023Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block023Part007CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block023Part007SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block023Part007] using hcert

def TailChunk000Sub000Block023Part008SupportExplicit : Finset ℕ :=
  ([1009] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block023Part008 : ℚ :=
  (158947896125 : ℚ) / 1290740661633024

def SurrogateDiagonalTailChunk000Sub000Block023Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1009
    = surrogateDiagTailX0RatChunk000Sub000Block023Part008

theorem surrogateDiagonalTailChunk000Sub000Block023Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block023Part008CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block023Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block023Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block023Part008CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block023Part008SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block023Part008] using hcert

def TailChunk000Sub000Block023Part009SupportExplicit : Finset ℕ :=
  ([1010] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block023Part009 : ℚ :=
  (50505499 : ℚ) / 25605120000

def SurrogateDiagonalTailChunk000Sub000Block023Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1010
    = surrogateDiagTailX0RatChunk000Sub000Block023Part009

theorem surrogateDiagonalTailChunk000Sub000Block023Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block023Part009CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block023Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block023Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block023Part009CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block023Part009SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block023Part009] using hcert

def TailChunk000Sub000Block023Part010SupportExplicit : Finset ℕ :=
  ([1011] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block023Part010 : ℚ :=
  (2358925 : ℚ) / 5664669696

def SurrogateDiagonalTailChunk000Sub000Block023Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1011
    = surrogateDiagTailX0RatChunk000Sub000Block023Part010

theorem surrogateDiagonalTailChunk000Sub000Block023Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block023Part010CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block023Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block023Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block023Part010CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block023Part010SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block023Part010] using hcert

def TailChunk000Sub000Block023Part011SupportExplicit : Finset ℕ :=
  ([1013] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block023Part011 : ℚ :=
  (160210635125 : ℚ) / 1311350883653184

def SurrogateDiagonalTailChunk000Sub000Block023Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1013
    = surrogateDiagTailX0RatChunk000Sub000Block023Part011

theorem surrogateDiagonalTailChunk000Sub000Block023Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block023Part011CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block023Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block023Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block023Part011CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block023Part011SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block023Part011] using hcert

def TailChunk000Sub000Block023Part012SupportExplicit : Finset ℕ :=
  ([1015] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block023Part012 : ℚ :=
  (23387792525 : ℚ) / 56658026299392

def SurrogateDiagonalTailChunk000Sub000Block023Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1015
    = surrogateDiagTailX0RatChunk000Sub000Block023Part012

theorem surrogateDiagonalTailChunk000Sub000Block023Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block023Part012CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block023Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block023Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block023Part012CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block023Part012SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block023Part012] using hcert

def TailChunk000Sub000Block023Part013SupportExplicit : Finset ℕ :=
  ([1018] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block023Part013 : ℚ :=
  (161634158875 : ℚ) / 166525868754048

def SurrogateDiagonalTailChunk000Sub000Block023Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1018
    = surrogateDiagTailX0RatChunk000Sub000Block023Part013

theorem surrogateDiagonalTailChunk000Sub000Block023Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block023Part013CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block023Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block023Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block023Part013CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block023Part013SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block023Part013] using hcert

def TailChunk000Sub000Block023Part014SupportExplicit : Finset ℕ :=
  ([1019] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block023Part014 : ℚ :=
  (162114111125 : ℚ) / 1342727783078244

def SurrogateDiagonalTailChunk000Sub000Block023Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1019
    = surrogateDiagTailX0RatChunk000Sub000Block023Part014

theorem surrogateDiagonalTailChunk000Sub000Block023Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block023Part014CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block023Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block023Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block023Part014CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block023Part014SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block023Part014] using hcert

def TailChunk000Sub000Block023Part015SupportExplicit : Finset ℕ :=
  ([1021] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block023Part015 : ℚ :=
  (1302008809 : ℚ) / 10826486464320

def SurrogateDiagonalTailChunk000Sub000Block023Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1021
    = surrogateDiagTailX0RatChunk000Sub000Block023Part015

theorem surrogateDiagonalTailChunk000Sub000Block023Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block023Part015CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block023Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block023Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block023Part015CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block023Part015SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block023Part015] using hcert

def TailChunk000Sub000Block023Part016SupportExplicit : Finset ℕ :=
  ([1022] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block023Part016 : ℚ :=
  (68653745525 : ℚ) / 43544353849344

def SurrogateDiagonalTailChunk000Sub000Block023Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1022
    = surrogateDiagTailX0RatChunk000Sub000Block023Part016

theorem surrogateDiagonalTailChunk000Sub000Block023Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block023Part016CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block023Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block023Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block023Part016CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block023Part016SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block023Part016] using hcert

def TailChunk000Sub000Block023Part017SupportExplicit : Finset ℕ :=
  ([1023] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block023Part017 : ℚ :=
  (3715216799 : ℚ) / 6481296000000

def SurrogateDiagonalTailChunk000Sub000Block023Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1023
    = surrogateDiagTailX0RatChunk000Sub000Block023Part017

theorem surrogateDiagonalTailChunk000Sub000Block023Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block023Part017CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block023Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block023Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block023Part017CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block023Part017SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block023Part017] using hcert

def TailChunk000Sub000Block023Part018SupportExplicit : Finset ℕ :=
  ([1027] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block023Part018 : ℚ :=
  (299598986425 : ℚ) / 1919244275140608

def SurrogateDiagonalTailChunk000Sub000Block023Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1027
    = surrogateDiagTailX0RatChunk000Sub000Block023Part018

theorem surrogateDiagonalTailChunk000Sub000Block023Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block023Part018CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block023Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block023Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block023Part018CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block023Part018SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block023Part018] using hcert

def TailChunk000Sub000Block023Part019SupportExplicit : Finset ℕ :=
  ([1030] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block023Part019 : ℚ :=
  (130013612575 : ℚ) / 69289513371648

def SurrogateDiagonalTailChunk000Sub000Block023Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1030
    = surrogateDiagTailX0RatChunk000Sub000Block023Part019

theorem surrogateDiagonalTailChunk000Sub000Block023Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block023Part019CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block023Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block023Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block023Part019CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block023Part019SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block023Part019] using hcert

def TailChunk000Sub000Block023Part020SupportExplicit : Finset ℕ :=
  ([1031] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block023Part020 : ℚ :=
  (1327638289 : ℚ) / 11257339117620

def SurrogateDiagonalTailChunk000Sub000Block023Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1031
    = surrogateDiagTailX0RatChunk000Sub000Block023Part020

theorem surrogateDiagonalTailChunk000Sub000Block023Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block023Part020CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block023Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block023Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block023Part020CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block023Part020SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block023Part020] using hcert

def TailChunk000Sub000Block023Part021SupportExplicit : Finset ℕ :=
  ([1033] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block023Part021 : ℚ :=
  (133306093325 : ℚ) / 1418128719750144

def SurrogateDiagonalTailChunk000Sub000Block023Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1033
    = surrogateDiagTailX0RatChunk000Sub000Block023Part021

theorem surrogateDiagonalTailChunk000Sub000Block023Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block023Part021CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block023Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block023Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block023Part021CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block023Part021SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block023Part021] using hcert

def TailChunk000Sub000Block023Part022SupportExplicit : Finset ℕ :=
  ([1034] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block023Part022 : ℚ :=
  (899629401 : ℚ) / 746391915200

def SurrogateDiagonalTailChunk000Sub000Block023Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1034
    = surrogateDiagTailX0RatChunk000Sub000Block023Part022

theorem surrogateDiagonalTailChunk000Sub000Block023Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block023Part022CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block023Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block023Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block023Part022CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block023Part022SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block023Part022] using hcert

def TailChunk000Sub000Block023Part023SupportExplicit : Finset ℕ :=
  ([1037] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block023Part023 : ℚ :=
  (5058416717 : ℚ) / 42475821465600

def SurrogateDiagonalTailChunk000Sub000Block023Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1037
    = surrogateDiagTailX0RatChunk000Sub000Block023Part023

theorem surrogateDiagonalTailChunk000Sub000Block023Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block023Part023CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block023Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block023Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block023Part023CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block023Part023SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block023Part023] using hcert

def TailChunk000Sub000Block023Part024SupportExplicit : Finset ℕ :=
  ([1038] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block023Part024 : ℚ :=
  (2551953625 : ℚ) / 814314510336

def SurrogateDiagonalTailChunk000Sub000Block023Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1038
    = surrogateDiagTailX0RatChunk000Sub000Block023Part024

theorem surrogateDiagonalTailChunk000Sub000Block023Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block023Part024CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block023Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block023Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block023Part024CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block023Part024SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block023Part024] using hcert

def surrogateDiagonalTailChunk000Sub000Block023HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block023Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block023Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block023Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block023Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block023Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block023Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block023Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block023Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block023Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block023Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block023Head : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block023Part000
    + surrogateDiagTailX0RatChunk000Sub000Block023Part001
    + surrogateDiagTailX0RatChunk000Sub000Block023Part002
    + surrogateDiagTailX0RatChunk000Sub000Block023Part003
    + surrogateDiagTailX0RatChunk000Sub000Block023Part004
    + surrogateDiagTailX0RatChunk000Sub000Block023Part005
    + surrogateDiagTailX0RatChunk000Sub000Block023Part006
    + surrogateDiagTailX0RatChunk000Sub000Block023Part007
    + surrogateDiagTailX0RatChunk000Sub000Block023Part008
    + surrogateDiagTailX0RatChunk000Sub000Block023Part009

def surrogateDiagonalTailChunk000Sub000Block023MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block023Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block023Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block023Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block023Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block023Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block023Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block023Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block023Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block023Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block023Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block023Mid : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block023Part010
    + surrogateDiagTailX0RatChunk000Sub000Block023Part011
    + surrogateDiagTailX0RatChunk000Sub000Block023Part012
    + surrogateDiagTailX0RatChunk000Sub000Block023Part013
    + surrogateDiagTailX0RatChunk000Sub000Block023Part014
    + surrogateDiagTailX0RatChunk000Sub000Block023Part015
    + surrogateDiagTailX0RatChunk000Sub000Block023Part016
    + surrogateDiagTailX0RatChunk000Sub000Block023Part017
    + surrogateDiagTailX0RatChunk000Sub000Block023Part018
    + surrogateDiagTailX0RatChunk000Sub000Block023Part019

def surrogateDiagonalTailChunk000Sub000Block023TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block023Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block023Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block023Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block023Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block023Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block023Tail : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block023Part020
    + surrogateDiagTailX0RatChunk000Sub000Block023Part021
    + surrogateDiagTailX0RatChunk000Sub000Block023Part022
    + surrogateDiagTailX0RatChunk000Sub000Block023Part023
    + surrogateDiagTailX0RatChunk000Sub000Block023Part024

def surrogateDiagonalTailChunk000Sub000Block023Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub000Block023HeadSum X0
    + surrogateDiagonalTailChunk000Sub000Block023MidSum X0
    + surrogateDiagonalTailChunk000Sub000Block023TailSum X0

def surrogateDiagTailX0RatChunk000Sub000Block023 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block023Part000
    + surrogateDiagTailX0RatChunk000Sub000Block023Part001
    + surrogateDiagTailX0RatChunk000Sub000Block023Part002
    + surrogateDiagTailX0RatChunk000Sub000Block023Part003
    + surrogateDiagTailX0RatChunk000Sub000Block023Part004
    + surrogateDiagTailX0RatChunk000Sub000Block023Part005
    + surrogateDiagTailX0RatChunk000Sub000Block023Part006
    + surrogateDiagTailX0RatChunk000Sub000Block023Part007
    + surrogateDiagTailX0RatChunk000Sub000Block023Part008
    + surrogateDiagTailX0RatChunk000Sub000Block023Part009
    + surrogateDiagTailX0RatChunk000Sub000Block023Part010
    + surrogateDiagTailX0RatChunk000Sub000Block023Part011
    + surrogateDiagTailX0RatChunk000Sub000Block023Part012
    + surrogateDiagTailX0RatChunk000Sub000Block023Part013
    + surrogateDiagTailX0RatChunk000Sub000Block023Part014
    + surrogateDiagTailX0RatChunk000Sub000Block023Part015
    + surrogateDiagTailX0RatChunk000Sub000Block023Part016
    + surrogateDiagTailX0RatChunk000Sub000Block023Part017
    + surrogateDiagTailX0RatChunk000Sub000Block023Part018
    + surrogateDiagTailX0RatChunk000Sub000Block023Part019
    + surrogateDiagTailX0RatChunk000Sub000Block023Part020
    + surrogateDiagTailX0RatChunk000Sub000Block023Part021
    + surrogateDiagTailX0RatChunk000Sub000Block023Part022
    + surrogateDiagTailX0RatChunk000Sub000Block023Part023
    + surrogateDiagTailX0RatChunk000Sub000Block023Part024

theorem surrogateDiagTailX0RatChunk000Sub000Block023_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk000Sub000Block023Head + surrogateDiagTailX0RatChunk000Sub000Block023Mid + surrogateDiagTailX0RatChunk000Sub000Block023Tail =
      surrogateDiagTailX0RatChunk000Sub000Block023 := by
  unfold surrogateDiagTailX0RatChunk000Sub000Block023Head surrogateDiagTailX0RatChunk000Sub000Block023Mid surrogateDiagTailX0RatChunk000Sub000Block023Tail surrogateDiagTailX0RatChunk000Sub000Block023
  ring

def SurrogateDiagonalTailChunk000Sub000Block023HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block023HeadSum X0 = surrogateDiagTailX0RatChunk000Sub000Block023Head

def SurrogateDiagonalTailChunk000Sub000Block023MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block023MidSum X0 = surrogateDiagTailX0RatChunk000Sub000Block023Mid

def SurrogateDiagonalTailChunk000Sub000Block023TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block023TailSum X0 = surrogateDiagTailX0RatChunk000Sub000Block023Tail

theorem surrogateDiagonalTailChunk000Sub000Block023_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk000Sub000Block023HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk000Sub000Block023MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk000Sub000Block023TailCertificateAt X0) :
    surrogateDiagonalTailChunk000Sub000Block023Sum X0 = surrogateDiagTailX0RatChunk000Sub000Block023 := by
  unfold SurrogateDiagonalTailChunk000Sub000Block023HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk000Sub000Block023MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk000Sub000Block023TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk000Sub000Block023Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk000Sub000Block023_eq_head_add_mid_add_tail

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

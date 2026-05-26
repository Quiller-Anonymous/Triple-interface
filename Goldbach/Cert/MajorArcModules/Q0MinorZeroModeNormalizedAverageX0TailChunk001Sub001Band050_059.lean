import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0TailPilot25

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

open scoped BigOperators

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

/- Generated direct-term certificate blocks for tail chunk 001, subchunk 001, blocks [50,60). -/

/-- Block 050 covers tail-support indices [16250,16275) and q from 26783 to 26821. -/

def TailChunk001Sub001Block050Part000SupportExplicit : Finset ℕ :=
  ([26783] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block050Part000 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block050Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26783
    = surrogateDiagTailX0RatChunk001Sub001Block050Part000

theorem surrogateDiagonalTailChunk001Sub001Block050Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block050Part000CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block050Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block050Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block050Part000CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block050Part000SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block050Part000] using hcert

def TailChunk001Sub001Block050Part001SupportExplicit : Finset ℕ :=
  ([26785] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block050Part001 : ℚ :=
  (41290220423 : ℚ) / 7142362640138649600

def SurrogateDiagonalTailChunk001Sub001Block050Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26785
    = surrogateDiagTailX0RatChunk001Sub001Block050Part001

theorem surrogateDiagonalTailChunk001Sub001Block050Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block050Part001CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block050Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block050Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block050Part001CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block050Part001SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block050Part001] using hcert

def TailChunk001Sub001Block050Part002SupportExplicit : Finset ℕ :=
  ([26786] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block050Part002 : ℚ :=
  (88110805525 : ℚ) / 73819753341150776448

def SurrogateDiagonalTailChunk001Sub001Block050Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26786
    = surrogateDiagTailX0RatChunk001Sub001Block050Part002

theorem surrogateDiagonalTailChunk001Sub001Block050Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block050Part002CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block050Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block050Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block050Part002CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block050Part002SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block050Part002] using hcert

def TailChunk001Sub001Block050Part003SupportExplicit : Finset ℕ :=
  ([26787] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block050Part003 : ℚ :=
  (1245612241075 : ℚ) / 63548247247486451712

def SurrogateDiagonalTailChunk001Sub001Block050Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26787
    = surrogateDiagTailX0RatChunk001Sub001Block050Part003

theorem surrogateDiagonalTailChunk001Sub001Block050Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block050Part003CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block050Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block050Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block050Part003CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block050Part003SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block050Part003] using hcert

def TailChunk001Sub001Block050Part004SupportExplicit : Finset ℕ :=
  ([26789] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block050Part004 : ℚ :=
  (99345751325 : ℚ) / 54975226260273758208

def SurrogateDiagonalTailChunk001Sub001Block050Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26789
    = surrogateDiagTailX0RatChunk001Sub001Block050Part004

theorem surrogateDiagonalTailChunk001Sub001Block050Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block050Part004CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block050Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block050Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block050Part004CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block050Part004SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block050Part004] using hcert

def TailChunk001Sub001Block050Part005SupportExplicit : Finset ℕ :=
  ([26790] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block050Part005 : ℚ :=
  (1948159561675 : ℚ) / 4814022923675762688

def SurrogateDiagonalTailChunk001Sub001Block050Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26790
    = surrogateDiagTailX0RatChunk001Sub001Block050Part005

theorem surrogateDiagonalTailChunk001Sub001Block050Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block050Part005CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block050Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block050Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block050Part005CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block050Part005SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block050Part005] using hcert

def TailChunk001Sub001Block050Part006SupportExplicit : Finset ℕ :=
  ([26791] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block050Part006 : ℚ :=
  (139253595175 : ℚ) / 1205816399691509956608

def SurrogateDiagonalTailChunk001Sub001Block050Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26791
    = surrogateDiagTailX0RatChunk001Sub001Block050Part006

theorem surrogateDiagonalTailChunk001Sub001Block050Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block050Part006CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block050Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block050Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block050Part006CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block050Part006SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block050Part006] using hcert

def TailChunk001Sub001Block050Part007SupportExplicit : Finset ℕ :=
  ([26794] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block050Part007 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block050Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26794
    = surrogateDiagTailX0RatChunk001Sub001Block050Part007

theorem surrogateDiagonalTailChunk001Sub001Block050Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block050Part007CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block050Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block050Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block050Part007CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block050Part007SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block050Part007] using hcert

def TailChunk001Sub001Block050Part008SupportExplicit : Finset ℕ :=
  ([26795] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block050Part008 : ℚ :=
  (66497535275 : ℚ) / 14979988816964616192

def SurrogateDiagonalTailChunk001Sub001Block050Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26795
    = surrogateDiagTailX0RatChunk001Sub001Block050Part008

theorem surrogateDiagonalTailChunk001Sub001Block050Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block050Part008CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block050Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block050Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block050Part008CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block050Part008SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block050Part008] using hcert

def TailChunk001Sub001Block050Part009SupportExplicit : Finset ℕ :=
  ([26797] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block050Part009 : ℚ :=
  (22193207 : ℚ) / 259408621253980800

def SurrogateDiagonalTailChunk001Sub001Block050Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26797
    = surrogateDiagTailX0RatChunk001Sub001Block050Part009

theorem surrogateDiagonalTailChunk001Sub001Block050Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block050Part009CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block050Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block050Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block050Part009CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block050Part009SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block050Part009] using hcert

def TailChunk001Sub001Block050Part010SupportExplicit : Finset ℕ :=
  ([26798] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block050Part010 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block050Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26798
    = surrogateDiagTailX0RatChunk001Sub001Block050Part010

theorem surrogateDiagonalTailChunk001Sub001Block050Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block050Part010CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block050Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block050Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block050Part010CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block050Part010SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block050Part010] using hcert

def TailChunk001Sub001Block050Part011SupportExplicit : Finset ℕ :=
  ([26799] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block050Part011 : ℚ :=
  (89052035075 : ℚ) / 4547300682444672768

def SurrogateDiagonalTailChunk001Sub001Block050Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26799
    = surrogateDiagTailX0RatChunk001Sub001Block050Part011

theorem surrogateDiagonalTailChunk001Sub001Block050Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block050Part011CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block050Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block050Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block050Part011CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block050Part011SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block050Part011] using hcert

def TailChunk001Sub001Block050Part012SupportExplicit : Finset ℕ :=
  ([26801] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block050Part012 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block050Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26801
    = surrogateDiagTailX0RatChunk001Sub001Block050Part012

theorem surrogateDiagonalTailChunk001Sub001Block050Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block050Part012CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block050Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block050Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block050Part012CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block050Part012SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block050Part012] using hcert

def TailChunk001Sub001Block050Part013SupportExplicit : Finset ℕ :=
  ([26805] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block050Part013 : ℚ :=
  (1856803275 : ℚ) / 46192719347836928

def SurrogateDiagonalTailChunk001Sub001Block050Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26805
    = surrogateDiagTailX0RatChunk001Sub001Block050Part013

theorem surrogateDiagonalTailChunk001Sub001Block050Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block050Part013CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block050Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block050Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block050Part013CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block050Part013SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block050Part013] using hcert

def TailChunk001Sub001Block050Part014SupportExplicit : Finset ℕ :=
  ([26806] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block050Part014 : ℚ :=
  (2680150427 : ℚ) / 466864367885936640

def SurrogateDiagonalTailChunk001Sub001Block050Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26806
    = surrogateDiagTailX0RatChunk001Sub001Block050Part014

theorem surrogateDiagonalTailChunk001Sub001Block050Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block050Part014CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block050Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block050Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block050Part014CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block050Part014SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block050Part014] using hcert

def TailChunk001Sub001Block050Part015SupportExplicit : Finset ℕ :=
  ([26807] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block050Part015 : ℚ :=
  (2482470973 : ℚ) / 2935044836356953600

def SurrogateDiagonalTailChunk001Sub001Block050Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26807
    = surrogateDiagTailX0RatChunk001Sub001Block050Part015

theorem surrogateDiagonalTailChunk001Sub001Block050Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block050Part015CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block050Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block050Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block050Part015CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block050Part015SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block050Part015] using hcert

def TailChunk001Sub001Block050Part016SupportExplicit : Finset ℕ :=
  ([26809] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block050Part016 : ℚ :=
  (282147353575 : ℚ) / 259257282639383494656

def SurrogateDiagonalTailChunk001Sub001Block050Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26809
    = surrogateDiagTailX0RatChunk001Sub001Block050Part016

theorem surrogateDiagonalTailChunk001Sub001Block050Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block050Part016CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block050Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block050Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block050Part016CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block050Part016SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block050Part016] using hcert

def TailChunk001Sub001Block050Part017SupportExplicit : Finset ℕ :=
  ([26810] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block050Part017 : ℚ :=
  (519035842025 : ℚ) / 8832736643272556544

def SurrogateDiagonalTailChunk001Sub001Block050Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26810
    = surrogateDiagTailX0RatChunk001Sub001Block050Part017

theorem surrogateDiagonalTailChunk001Sub001Block050Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block050Part017CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block050Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block050Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block050Part017CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block050Part017SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block050Part017] using hcert

def TailChunk001Sub001Block050Part018SupportExplicit : Finset ℕ :=
  ([26813] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block050Part018 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block050Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26813
    = surrogateDiagTailX0RatChunk001Sub001Block050Part018

theorem surrogateDiagonalTailChunk001Sub001Block050Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block050Part018CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block050Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block050Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block050Part018CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block050Part018SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block050Part018] using hcert

def TailChunk001Sub001Block050Part019SupportExplicit : Finset ℕ :=
  ([26814] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block050Part019 : ℚ :=
  (96872540779 : ℚ) / 557367729271603200

def SurrogateDiagonalTailChunk001Sub001Block050Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26814
    = surrogateDiagTailX0RatChunk001Sub001Block050Part019

theorem surrogateDiagonalTailChunk001Sub001Block050Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block050Part019CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block050Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block050Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block050Part019CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block050Part019SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block050Part019] using hcert

def TailChunk001Sub001Block050Part020SupportExplicit : Finset ℕ :=
  ([26815] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block050Part020 : ℚ :=
  (12617906069 : ℚ) / 3025341268800307200

def SurrogateDiagonalTailChunk001Sub001Block050Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26815
    = surrogateDiagTailX0RatChunk001Sub001Block050Part020

theorem surrogateDiagonalTailChunk001Sub001Block050Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block050Part020CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block050Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block050Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block050Part020CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block050Part020SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block050Part020] using hcert

def TailChunk001Sub001Block050Part021SupportExplicit : Finset ℕ :=
  ([26817] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block050Part021 : ℚ :=
  (3300794725 : ℚ) / 106059491135735808

def SurrogateDiagonalTailChunk001Sub001Block050Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26817
    = surrogateDiagTailX0RatChunk001Sub001Block050Part021

theorem surrogateDiagonalTailChunk001Sub001Block050Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block050Part021CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block050Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block050Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block050Part021CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block050Part021SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block050Part021] using hcert

def TailChunk001Sub001Block050Part022SupportExplicit : Finset ℕ :=
  ([26818] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block050Part022 : ℚ :=
  (22487600071 : ℚ) / 1713132475679539200

def SurrogateDiagonalTailChunk001Sub001Block050Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26818
    = surrogateDiagTailX0RatChunk001Sub001Block050Part022

theorem surrogateDiagonalTailChunk001Sub001Block050Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block050Part022CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block050Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block050Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block050Part022CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block050Part022SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block050Part022] using hcert

def TailChunk001Sub001Block050Part023SupportExplicit : Finset ℕ :=
  ([26819] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block050Part023 : ℚ :=
  (535127710525 : ℚ) / 937360150976704923648

def SurrogateDiagonalTailChunk001Sub001Block050Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26819
    = surrogateDiagTailX0RatChunk001Sub001Block050Part023

theorem surrogateDiagonalTailChunk001Sub001Block050Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block050Part023CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block050Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block050Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block050Part023CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block050Part023SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block050Part023] using hcert

def TailChunk001Sub001Block050Part024SupportExplicit : Finset ℕ :=
  ([26821] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block050Part024 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block050Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26821
    = surrogateDiagTailX0RatChunk001Sub001Block050Part024

theorem surrogateDiagonalTailChunk001Sub001Block050Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block050Part024CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block050Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block050Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block050Part024CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block050Part024SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block050Part024] using hcert

def surrogateDiagonalTailChunk001Sub001Block050HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub001Block050Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block050Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block050Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block050Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block050Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block050Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block050Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block050Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block050Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block050Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub001Block050Head : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block050Part000
    + surrogateDiagTailX0RatChunk001Sub001Block050Part001
    + surrogateDiagTailX0RatChunk001Sub001Block050Part002
    + surrogateDiagTailX0RatChunk001Sub001Block050Part003
    + surrogateDiagTailX0RatChunk001Sub001Block050Part004
    + surrogateDiagTailX0RatChunk001Sub001Block050Part005
    + surrogateDiagTailX0RatChunk001Sub001Block050Part006
    + surrogateDiagTailX0RatChunk001Sub001Block050Part007
    + surrogateDiagTailX0RatChunk001Sub001Block050Part008
    + surrogateDiagTailX0RatChunk001Sub001Block050Part009

def surrogateDiagonalTailChunk001Sub001Block050MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub001Block050Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block050Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block050Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block050Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block050Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block050Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block050Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block050Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block050Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block050Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub001Block050Mid : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block050Part010
    + surrogateDiagTailX0RatChunk001Sub001Block050Part011
    + surrogateDiagTailX0RatChunk001Sub001Block050Part012
    + surrogateDiagTailX0RatChunk001Sub001Block050Part013
    + surrogateDiagTailX0RatChunk001Sub001Block050Part014
    + surrogateDiagTailX0RatChunk001Sub001Block050Part015
    + surrogateDiagTailX0RatChunk001Sub001Block050Part016
    + surrogateDiagTailX0RatChunk001Sub001Block050Part017
    + surrogateDiagTailX0RatChunk001Sub001Block050Part018
    + surrogateDiagTailX0RatChunk001Sub001Block050Part019

def surrogateDiagonalTailChunk001Sub001Block050TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub001Block050Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block050Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block050Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block050Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block050Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub001Block050Tail : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block050Part020
    + surrogateDiagTailX0RatChunk001Sub001Block050Part021
    + surrogateDiagTailX0RatChunk001Sub001Block050Part022
    + surrogateDiagTailX0RatChunk001Sub001Block050Part023
    + surrogateDiagTailX0RatChunk001Sub001Block050Part024

def surrogateDiagonalTailChunk001Sub001Block050Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk001Sub001Block050HeadSum X0
    + surrogateDiagonalTailChunk001Sub001Block050MidSum X0
    + surrogateDiagonalTailChunk001Sub001Block050TailSum X0

def surrogateDiagTailX0RatChunk001Sub001Block050 : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block050Part000
    + surrogateDiagTailX0RatChunk001Sub001Block050Part001
    + surrogateDiagTailX0RatChunk001Sub001Block050Part002
    + surrogateDiagTailX0RatChunk001Sub001Block050Part003
    + surrogateDiagTailX0RatChunk001Sub001Block050Part004
    + surrogateDiagTailX0RatChunk001Sub001Block050Part005
    + surrogateDiagTailX0RatChunk001Sub001Block050Part006
    + surrogateDiagTailX0RatChunk001Sub001Block050Part007
    + surrogateDiagTailX0RatChunk001Sub001Block050Part008
    + surrogateDiagTailX0RatChunk001Sub001Block050Part009
    + surrogateDiagTailX0RatChunk001Sub001Block050Part010
    + surrogateDiagTailX0RatChunk001Sub001Block050Part011
    + surrogateDiagTailX0RatChunk001Sub001Block050Part012
    + surrogateDiagTailX0RatChunk001Sub001Block050Part013
    + surrogateDiagTailX0RatChunk001Sub001Block050Part014
    + surrogateDiagTailX0RatChunk001Sub001Block050Part015
    + surrogateDiagTailX0RatChunk001Sub001Block050Part016
    + surrogateDiagTailX0RatChunk001Sub001Block050Part017
    + surrogateDiagTailX0RatChunk001Sub001Block050Part018
    + surrogateDiagTailX0RatChunk001Sub001Block050Part019
    + surrogateDiagTailX0RatChunk001Sub001Block050Part020
    + surrogateDiagTailX0RatChunk001Sub001Block050Part021
    + surrogateDiagTailX0RatChunk001Sub001Block050Part022
    + surrogateDiagTailX0RatChunk001Sub001Block050Part023
    + surrogateDiagTailX0RatChunk001Sub001Block050Part024

theorem surrogateDiagTailX0RatChunk001Sub001Block050_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk001Sub001Block050Head + surrogateDiagTailX0RatChunk001Sub001Block050Mid + surrogateDiagTailX0RatChunk001Sub001Block050Tail =
      surrogateDiagTailX0RatChunk001Sub001Block050 := by
  unfold surrogateDiagTailX0RatChunk001Sub001Block050Head surrogateDiagTailX0RatChunk001Sub001Block050Mid surrogateDiagTailX0RatChunk001Sub001Block050Tail surrogateDiagTailX0RatChunk001Sub001Block050
  ring

def SurrogateDiagonalTailChunk001Sub001Block050HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub001Block050HeadSum X0 = surrogateDiagTailX0RatChunk001Sub001Block050Head

def SurrogateDiagonalTailChunk001Sub001Block050MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub001Block050MidSum X0 = surrogateDiagTailX0RatChunk001Sub001Block050Mid

def SurrogateDiagonalTailChunk001Sub001Block050TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub001Block050TailSum X0 = surrogateDiagTailX0RatChunk001Sub001Block050Tail

theorem surrogateDiagonalTailChunk001Sub001Block050_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk001Sub001Block050HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk001Sub001Block050MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk001Sub001Block050TailCertificateAt X0) :
    surrogateDiagonalTailChunk001Sub001Block050Sum X0 = surrogateDiagTailX0RatChunk001Sub001Block050 := by
  unfold SurrogateDiagonalTailChunk001Sub001Block050HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk001Sub001Block050MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk001Sub001Block050TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk001Sub001Block050Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk001Sub001Block050_eq_head_add_mid_add_tail

/-- Block 051 covers tail-support indices [16275,16300) and q from 26822 to 26861. -/

def TailChunk001Sub001Block051Part000SupportExplicit : Finset ℕ :=
  ([26822] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block051Part000 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block051Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26822
    = surrogateDiagTailX0RatChunk001Sub001Block051Part000

theorem surrogateDiagonalTailChunk001Sub001Block051Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block051Part000CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block051Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block051Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block051Part000CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block051Part000SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block051Part000] using hcert

def TailChunk001Sub001Block051Part001SupportExplicit : Finset ℕ :=
  ([26823] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block051Part001 : ℚ :=
  (1248962491 : ℚ) / 63890593933273920

def SurrogateDiagonalTailChunk001Sub001Block051Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26823
    = surrogateDiagTailX0RatChunk001Sub001Block051Part001

theorem surrogateDiagonalTailChunk001Sub001Block051Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block051Part001CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block051Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block051Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block051Part001CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block051Part001SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block051Part001] using hcert

def TailChunk001Sub001Block051Part002SupportExplicit : Finset ℕ :=
  ([26826] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block051Part002 : ℚ :=
  (1275544682725 : ℚ) / 12354692410893139968

def SurrogateDiagonalTailChunk001Sub001Block051Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26826
    = surrogateDiagTailX0RatChunk001Sub001Block051Part002

theorem surrogateDiagonalTailChunk001Sub001Block051Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block051Part002CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block051Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block051Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block051Part002CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block051Part002SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block051Part002] using hcert

def TailChunk001Sub001Block051Part003SupportExplicit : Finset ℕ :=
  ([26827] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block051Part003 : ℚ :=
  (102767169325 : ℚ) / 1232389868460995248128

def SurrogateDiagonalTailChunk001Sub001Block051Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26827
    = surrogateDiagTailX0RatChunk001Sub001Block051Part003

theorem surrogateDiagonalTailChunk001Sub001Block051Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block051Part003CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block051Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block051Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block051Part003CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block051Part003SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block051Part003] using hcert

def TailChunk001Sub001Block051Part004SupportExplicit : Finset ℕ :=
  ([26830] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block051Part004 : ℚ :=
  (300070330675 : ℚ) / 11040294631669733376

def SurrogateDiagonalTailChunk001Sub001Block051Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26830
    = surrogateDiagTailX0RatChunk001Sub001Block051Part004

theorem surrogateDiagonalTailChunk001Sub001Block051Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block051Part004CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block051Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block051Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block051Part004CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block051Part004SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block051Part004] using hcert

def TailChunk001Sub001Block051Part005SupportExplicit : Finset ℕ :=
  ([26831] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block051Part005 : ℚ :=
  (919638941425 : ℚ) / 698769373651794690048

def SurrogateDiagonalTailChunk001Sub001Block051Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26831
    = surrogateDiagTailX0RatChunk001Sub001Block051Part005

theorem surrogateDiagonalTailChunk001Sub001Block051Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block051Part005CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block051Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block051Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block051Part005CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block051Part005SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block051Part005] using hcert

def TailChunk001Sub001Block051Part006SupportExplicit : Finset ℕ :=
  ([26833] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block051Part006 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block051Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26833
    = surrogateDiagTailX0RatChunk001Sub001Block051Part006

theorem surrogateDiagonalTailChunk001Sub001Block051Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block051Part006CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block051Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block051Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block051Part006CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block051Part006SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block051Part006] using hcert

def TailChunk001Sub001Block051Part007SupportExplicit : Finset ℕ :=
  ([26834] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block051Part007 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block051Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26834
    = surrogateDiagTailX0RatChunk001Sub001Block051Part007

theorem surrogateDiagonalTailChunk001Sub001Block051Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block051Part007CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block051Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block051Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block051Part007CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block051Part007SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block051Part007] using hcert

def TailChunk001Sub001Block051Part008SupportExplicit : Finset ℕ :=
  ([26835] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block051Part008 : ℚ :=
  (2099164791125 : ℚ) / 52339174550137995264

def SurrogateDiagonalTailChunk001Sub001Block051Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26835
    = surrogateDiagTailX0RatChunk001Sub001Block051Part008

theorem surrogateDiagonalTailChunk001Sub001Block051Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block051Part008CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block051Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block051Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block051Part008CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block051Part008SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block051Part008] using hcert

def TailChunk001Sub001Block051Part009SupportExplicit : Finset ℕ :=
  ([26837] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block051Part009 : ℚ :=
  (7871674441 : ℚ) / 47273482819458691200

def SurrogateDiagonalTailChunk001Sub001Block051Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26837
    = surrogateDiagTailX0RatChunk001Sub001Block051Part009

theorem surrogateDiagonalTailChunk001Sub001Block051Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block051Part009CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block051Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block051Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block051Part009CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block051Part009SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block051Part009] using hcert

def TailChunk001Sub001Block051Part010SupportExplicit : Finset ℕ :=
  ([26839] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block051Part010 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block051Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26839
    = surrogateDiagTailX0RatChunk001Sub001Block051Part010

theorem surrogateDiagonalTailChunk001Sub001Block051Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block051Part010CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block051Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block051Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block051Part010CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block051Part010SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block051Part010] using hcert

def TailChunk001Sub001Block051Part011SupportExplicit : Finset ℕ :=
  ([26841] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block051Part011 : ℚ :=
  (1560379125 : ℚ) / 69142209843286624

def SurrogateDiagonalTailChunk001Sub001Block051Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26841
    = surrogateDiagTailX0RatChunk001Sub001Block051Part011

theorem surrogateDiagonalTailChunk001Sub001Block051Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block051Part011CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block051Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block051Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block051Part011CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block051Part011SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block051Part011] using hcert

def TailChunk001Sub001Block051Part012SupportExplicit : Finset ℕ :=
  ([26842] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block051Part012 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block051Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26842
    = surrogateDiagTailX0RatChunk001Sub001Block051Part012

theorem surrogateDiagonalTailChunk001Sub001Block051Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block051Part012CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block051Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block051Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block051Part012CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block051Part012SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block051Part012] using hcert

def TailChunk001Sub001Block051Part013SupportExplicit : Finset ℕ :=
  ([26843] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block051Part013 : ℚ :=
  (13102860925 : ℚ) / 28224891702483222528

def SurrogateDiagonalTailChunk001Sub001Block051Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26843
    = surrogateDiagTailX0RatChunk001Sub001Block051Part013

theorem surrogateDiagonalTailChunk001Sub001Block051Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block051Part013CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block051Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block051Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block051Part013CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block051Part013SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block051Part013] using hcert

def TailChunk001Sub001Block051Part014SupportExplicit : Finset ℕ :=
  ([26845] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block051Part014 : ℚ :=
  (30334570175 : ℚ) / 2703810733380993024

def SurrogateDiagonalTailChunk001Sub001Block051Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26845
    = surrogateDiagTailX0RatChunk001Sub001Block051Part014

theorem surrogateDiagonalTailChunk001Sub001Block051Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block051Part014CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block051Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block051Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block051Part014CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block051Part014SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block051Part014] using hcert

def TailChunk001Sub001Block051Part015SupportExplicit : Finset ℕ :=
  ([26846] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block051Part015 : ℚ :=
  (596078731 : ℚ) / 282167412943749120

def SurrogateDiagonalTailChunk001Sub001Block051Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26846
    = surrogateDiagTailX0RatChunk001Sub001Block051Part015

theorem surrogateDiagonalTailChunk001Sub001Block051Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block051Part015CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block051Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block051Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block051Part015CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block051Part015SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block051Part015] using hcert

def TailChunk001Sub001Block051Part016SupportExplicit : Finset ℕ :=
  ([26849] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block051Part016 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block051Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26849
    = surrogateDiagTailX0RatChunk001Sub001Block051Part016

theorem surrogateDiagonalTailChunk001Sub001Block051Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block051Part016CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block051Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block051Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block051Part016CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block051Part016SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block051Part016] using hcert

def TailChunk001Sub001Block051Part017SupportExplicit : Finset ℕ :=
  ([26851] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block051Part017 : ℚ :=
  (7471788031 : ℚ) / 8863110507648000000

def SurrogateDiagonalTailChunk001Sub001Block051Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26851
    = surrogateDiagTailX0RatChunk001Sub001Block051Part017

theorem surrogateDiagonalTailChunk001Sub001Block051Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block051Part017CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block051Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block051Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block051Part017CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block051Part017SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block051Part017] using hcert

def TailChunk001Sub001Block051Part018SupportExplicit : Finset ℕ :=
  ([26853] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block051Part018 : ℚ :=
  (4005624971 : ℚ) / 205366201227240000

def SurrogateDiagonalTailChunk001Sub001Block051Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26853
    = surrogateDiagTailX0RatChunk001Sub001Block051Part018

theorem surrogateDiagonalTailChunk001Sub001Block051Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block051Part018CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block051Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block051Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block051Part018CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block051Part018SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block051Part018] using hcert

def TailChunk001Sub001Block051Part019SupportExplicit : Finset ℕ :=
  ([26854] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block051Part019 : ℚ :=
  (14107308125 : ℚ) / 6365524607007971328

def SurrogateDiagonalTailChunk001Sub001Block051Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26854
    = surrogateDiagTailX0RatChunk001Sub001Block051Part019

theorem surrogateDiagonalTailChunk001Sub001Block051Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block051Part019CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block051Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block051Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block051Part019CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block051Part019SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block051Part019] using hcert

def TailChunk001Sub001Block051Part020SupportExplicit : Finset ℕ :=
  ([26855] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block051Part020 : ℚ :=
  (1453367857 : ℚ) / 360028471296000000

def SurrogateDiagonalTailChunk001Sub001Block051Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26855
    = surrogateDiagTailX0RatChunk001Sub001Block051Part020

theorem surrogateDiagonalTailChunk001Sub001Block051Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block051Part020CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block051Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block051Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block051Part020CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block051Part020SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block051Part020] using hcert

def TailChunk001Sub001Block051Part021SupportExplicit : Finset ℕ :=
  ([26857] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block051Part021 : ℚ :=
  (1430224053 : ℚ) / 16441789783750000000

def SurrogateDiagonalTailChunk001Sub001Block051Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26857
    = surrogateDiagTailX0RatChunk001Sub001Block051Part021

theorem surrogateDiagonalTailChunk001Sub001Block051Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block051Part021CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block051Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block051Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block051Part021CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block051Part021SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block051Part021] using hcert

def TailChunk001Sub001Block051Part022SupportExplicit : Finset ℕ :=
  ([26858] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block051Part022 : ℚ :=
  (134924710325 : ℚ) / 29406317132738985984

def SurrogateDiagonalTailChunk001Sub001Block051Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26858
    = surrogateDiagTailX0RatChunk001Sub001Block051Part022

theorem surrogateDiagonalTailChunk001Sub001Block051Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block051Part022CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block051Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block051Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block051Part022CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block051Part022SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block051Part022] using hcert

def TailChunk001Sub001Block051Part023SupportExplicit : Finset ℕ :=
  ([26859] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block051Part023 : ℚ :=
  (119201079025 : ℚ) / 3842136213092540928

def SurrogateDiagonalTailChunk001Sub001Block051Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26859
    = surrogateDiagTailX0RatChunk001Sub001Block051Part023

theorem surrogateDiagonalTailChunk001Sub001Block051Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block051Part023CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block051Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block051Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block051Part023CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block051Part023SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block051Part023] using hcert

def TailChunk001Sub001Block051Part024SupportExplicit : Finset ℕ :=
  ([26861] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block051Part024 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block051Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26861
    = surrogateDiagTailX0RatChunk001Sub001Block051Part024

theorem surrogateDiagonalTailChunk001Sub001Block051Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block051Part024CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block051Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block051Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block051Part024CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block051Part024SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block051Part024] using hcert

def surrogateDiagonalTailChunk001Sub001Block051HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub001Block051Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block051Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block051Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block051Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block051Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block051Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block051Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block051Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block051Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block051Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub001Block051Head : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block051Part000
    + surrogateDiagTailX0RatChunk001Sub001Block051Part001
    + surrogateDiagTailX0RatChunk001Sub001Block051Part002
    + surrogateDiagTailX0RatChunk001Sub001Block051Part003
    + surrogateDiagTailX0RatChunk001Sub001Block051Part004
    + surrogateDiagTailX0RatChunk001Sub001Block051Part005
    + surrogateDiagTailX0RatChunk001Sub001Block051Part006
    + surrogateDiagTailX0RatChunk001Sub001Block051Part007
    + surrogateDiagTailX0RatChunk001Sub001Block051Part008
    + surrogateDiagTailX0RatChunk001Sub001Block051Part009

def surrogateDiagonalTailChunk001Sub001Block051MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub001Block051Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block051Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block051Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block051Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block051Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block051Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block051Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block051Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block051Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block051Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub001Block051Mid : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block051Part010
    + surrogateDiagTailX0RatChunk001Sub001Block051Part011
    + surrogateDiagTailX0RatChunk001Sub001Block051Part012
    + surrogateDiagTailX0RatChunk001Sub001Block051Part013
    + surrogateDiagTailX0RatChunk001Sub001Block051Part014
    + surrogateDiagTailX0RatChunk001Sub001Block051Part015
    + surrogateDiagTailX0RatChunk001Sub001Block051Part016
    + surrogateDiagTailX0RatChunk001Sub001Block051Part017
    + surrogateDiagTailX0RatChunk001Sub001Block051Part018
    + surrogateDiagTailX0RatChunk001Sub001Block051Part019

def surrogateDiagonalTailChunk001Sub001Block051TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub001Block051Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block051Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block051Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block051Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block051Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub001Block051Tail : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block051Part020
    + surrogateDiagTailX0RatChunk001Sub001Block051Part021
    + surrogateDiagTailX0RatChunk001Sub001Block051Part022
    + surrogateDiagTailX0RatChunk001Sub001Block051Part023
    + surrogateDiagTailX0RatChunk001Sub001Block051Part024

def surrogateDiagonalTailChunk001Sub001Block051Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk001Sub001Block051HeadSum X0
    + surrogateDiagonalTailChunk001Sub001Block051MidSum X0
    + surrogateDiagonalTailChunk001Sub001Block051TailSum X0

def surrogateDiagTailX0RatChunk001Sub001Block051 : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block051Part000
    + surrogateDiagTailX0RatChunk001Sub001Block051Part001
    + surrogateDiagTailX0RatChunk001Sub001Block051Part002
    + surrogateDiagTailX0RatChunk001Sub001Block051Part003
    + surrogateDiagTailX0RatChunk001Sub001Block051Part004
    + surrogateDiagTailX0RatChunk001Sub001Block051Part005
    + surrogateDiagTailX0RatChunk001Sub001Block051Part006
    + surrogateDiagTailX0RatChunk001Sub001Block051Part007
    + surrogateDiagTailX0RatChunk001Sub001Block051Part008
    + surrogateDiagTailX0RatChunk001Sub001Block051Part009
    + surrogateDiagTailX0RatChunk001Sub001Block051Part010
    + surrogateDiagTailX0RatChunk001Sub001Block051Part011
    + surrogateDiagTailX0RatChunk001Sub001Block051Part012
    + surrogateDiagTailX0RatChunk001Sub001Block051Part013
    + surrogateDiagTailX0RatChunk001Sub001Block051Part014
    + surrogateDiagTailX0RatChunk001Sub001Block051Part015
    + surrogateDiagTailX0RatChunk001Sub001Block051Part016
    + surrogateDiagTailX0RatChunk001Sub001Block051Part017
    + surrogateDiagTailX0RatChunk001Sub001Block051Part018
    + surrogateDiagTailX0RatChunk001Sub001Block051Part019
    + surrogateDiagTailX0RatChunk001Sub001Block051Part020
    + surrogateDiagTailX0RatChunk001Sub001Block051Part021
    + surrogateDiagTailX0RatChunk001Sub001Block051Part022
    + surrogateDiagTailX0RatChunk001Sub001Block051Part023
    + surrogateDiagTailX0RatChunk001Sub001Block051Part024

theorem surrogateDiagTailX0RatChunk001Sub001Block051_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk001Sub001Block051Head + surrogateDiagTailX0RatChunk001Sub001Block051Mid + surrogateDiagTailX0RatChunk001Sub001Block051Tail =
      surrogateDiagTailX0RatChunk001Sub001Block051 := by
  unfold surrogateDiagTailX0RatChunk001Sub001Block051Head surrogateDiagTailX0RatChunk001Sub001Block051Mid surrogateDiagTailX0RatChunk001Sub001Block051Tail surrogateDiagTailX0RatChunk001Sub001Block051
  ring

def SurrogateDiagonalTailChunk001Sub001Block051HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub001Block051HeadSum X0 = surrogateDiagTailX0RatChunk001Sub001Block051Head

def SurrogateDiagonalTailChunk001Sub001Block051MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub001Block051MidSum X0 = surrogateDiagTailX0RatChunk001Sub001Block051Mid

def SurrogateDiagonalTailChunk001Sub001Block051TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub001Block051TailSum X0 = surrogateDiagTailX0RatChunk001Sub001Block051Tail

theorem surrogateDiagonalTailChunk001Sub001Block051_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk001Sub001Block051HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk001Sub001Block051MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk001Sub001Block051TailCertificateAt X0) :
    surrogateDiagonalTailChunk001Sub001Block051Sum X0 = surrogateDiagTailX0RatChunk001Sub001Block051 := by
  unfold SurrogateDiagonalTailChunk001Sub001Block051HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk001Sub001Block051MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk001Sub001Block051TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk001Sub001Block051Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk001Sub001Block051_eq_head_add_mid_add_tail

/-- Block 052 covers tail-support indices [16300,16325) and q from 26863 to 26905. -/

def TailChunk001Sub001Block052Part000SupportExplicit : Finset ℕ :=
  ([26863] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block052Part000 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block052Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26863
    = surrogateDiagTailX0RatChunk001Sub001Block052Part000

theorem surrogateDiagonalTailChunk001Sub001Block052Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block052Part000CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block052Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block052Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block052Part000CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block052Part000SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block052Part000] using hcert

def TailChunk001Sub001Block052Part001SupportExplicit : Finset ℕ :=
  ([26866] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block052Part001 : ℚ :=
  (685852157 : ℚ) / 28349188704000000

def SurrogateDiagonalTailChunk001Sub001Block052Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26866
    = surrogateDiagTailX0RatChunk001Sub001Block052Part001

theorem surrogateDiagonalTailChunk001Sub001Block052Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block052Part001CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block052Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block052Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block052Part001CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block052Part001SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block052Part001] using hcert

def TailChunk001Sub001Block052Part002SupportExplicit : Finset ℕ :=
  ([26867] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block052Part002 : ℚ :=
  (3008262611 : ℚ) / 24292519612416000000

def SurrogateDiagonalTailChunk001Sub001Block052Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26867
    = surrogateDiagTailX0RatChunk001Sub001Block052Part002

theorem surrogateDiagonalTailChunk001Sub001Block052Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block052Part002CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block052Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block052Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block052Part002CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block052Part002SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block052Part002] using hcert

def TailChunk001Sub001Block052Part003SupportExplicit : Finset ℕ :=
  ([26869] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block052Part003 : ℚ :=
  (115665243625 : ℚ) / 1232389868460995248128

def SurrogateDiagonalTailChunk001Sub001Block052Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26869
    = surrogateDiagTailX0RatChunk001Sub001Block052Part003

theorem surrogateDiagonalTailChunk001Sub001Block052Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block052Part003CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block052Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block052Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block052Part003CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block052Part003SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block052Part003] using hcert

def TailChunk001Sub001Block052Part004SupportExplicit : Finset ℕ :=
  ([26870] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block052Part004 : ℚ :=
  (150721033875 : ℚ) / 11106305178091657216

def SurrogateDiagonalTailChunk001Sub001Block052Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26870
    = surrogateDiagTailX0RatChunk001Sub001Block052Part004

theorem surrogateDiagonalTailChunk001Sub001Block052Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block052Part004CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block052Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block052Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block052Part004CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block052Part004SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block052Part004] using hcert

def TailChunk001Sub001Block052Part005SupportExplicit : Finset ℕ :=
  ([26873] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block052Part005 : ℚ :=
  (56159125573 : ℚ) / 19011169219085107200

def SurrogateDiagonalTailChunk001Sub001Block052Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26873
    = surrogateDiagTailX0RatChunk001Sub001Block052Part005

theorem surrogateDiagonalTailChunk001Sub001Block052Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block052Part005CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block052Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block052Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block052Part005CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block052Part005SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block052Part005] using hcert

def TailChunk001Sub001Block052Part006SupportExplicit : Finset ℕ :=
  ([26878] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block052Part006 : ℚ :=
  (328873933 : ℚ) / 337396105728000000

def SurrogateDiagonalTailChunk001Sub001Block052Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26878
    = surrogateDiagTailX0RatChunk001Sub001Block052Part006

theorem surrogateDiagonalTailChunk001Sub001Block052Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block052Part006CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block052Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block052Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block052Part006CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block052Part006SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block052Part006] using hcert

def TailChunk001Sub001Block052Part007SupportExplicit : Finset ℕ :=
  ([26879] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block052Part007 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block052Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26879
    = surrogateDiagTailX0RatChunk001Sub001Block052Part007

theorem surrogateDiagonalTailChunk001Sub001Block052Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block052Part007CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block052Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block052Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block052Part007CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block052Part007SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block052Part007] using hcert

def TailChunk001Sub001Block052Part008SupportExplicit : Finset ℕ :=
  ([26881] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block052Part008 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block052Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26881
    = surrogateDiagTailX0RatChunk001Sub001Block052Part008

theorem surrogateDiagonalTailChunk001Sub001Block052Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block052Part008CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block052Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block052Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block052Part008CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block052Part008SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block052Part008] using hcert

def TailChunk001Sub001Block052Part009SupportExplicit : Finset ℕ :=
  ([26882] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block052Part009 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block052Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26882
    = surrogateDiagTailX0RatChunk001Sub001Block052Part009

theorem surrogateDiagonalTailChunk001Sub001Block052Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block052Part009CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block052Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block052Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block052Part009CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block052Part009SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block052Part009] using hcert

def TailChunk001Sub001Block052Part010SupportExplicit : Finset ℕ :=
  ([26885] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block052Part010 : ℚ :=
  (646979223725 : ℚ) / 141655037423947186176

def SurrogateDiagonalTailChunk001Sub001Block052Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26885
    = surrogateDiagTailX0RatChunk001Sub001Block052Part010

theorem surrogateDiagonalTailChunk001Sub001Block052Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block052Part010CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block052Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block052Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block052Part010CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block052Part010SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block052Part010] using hcert

def TailChunk001Sub001Block052Part011SupportExplicit : Finset ℕ :=
  ([26886] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block052Part011 : ℚ :=
  (358578593 : ℚ) / 4604588804014080

def SurrogateDiagonalTailChunk001Sub001Block052Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26886
    = surrogateDiagTailX0RatChunk001Sub001Block052Part011

theorem surrogateDiagonalTailChunk001Sub001Block052Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block052Part011CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block052Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block052Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block052Part011CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block052Part011SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block052Part011] using hcert

def TailChunk001Sub001Block052Part012SupportExplicit : Finset ℕ :=
  ([26887] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block052Part012 : ℚ :=
  (582054308675 : ℚ) / 288220548416208528384

def SurrogateDiagonalTailChunk001Sub001Block052Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26887
    = surrogateDiagTailX0RatChunk001Sub001Block052Part012

theorem surrogateDiagonalTailChunk001Sub001Block052Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block052Part012CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block052Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block052Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block052Part012CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block052Part012SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block052Part012] using hcert

def TailChunk001Sub001Block052Part013SupportExplicit : Finset ℕ :=
  ([26889] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block052Part013 : ℚ :=
  (2510232606725 : ℚ) / 129043639781105492544

def SurrogateDiagonalTailChunk001Sub001Block052Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26889
    = surrogateDiagTailX0RatChunk001Sub001Block052Part013

theorem surrogateDiagonalTailChunk001Sub001Block052Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block052Part013CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block052Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block052Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block052Part013CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block052Part013SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block052Part013] using hcert

def TailChunk001Sub001Block052Part014SupportExplicit : Finset ℕ :=
  ([26890] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block052Part014 : ℚ :=
  (301412561575 : ℚ) / 11139421234670862336

def SurrogateDiagonalTailChunk001Sub001Block052Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26890
    = surrogateDiagTailX0RatChunk001Sub001Block052Part014

theorem surrogateDiagonalTailChunk001Sub001Block052Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block052Part014CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block052Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block052Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block052Part014CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block052Part014SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block052Part014] using hcert

def TailChunk001Sub001Block052Part015SupportExplicit : Finset ℕ :=
  ([26891] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block052Part015 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block052Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26891
    = surrogateDiagTailX0RatChunk001Sub001Block052Part015

theorem surrogateDiagonalTailChunk001Sub001Block052Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block052Part015CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block052Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block052Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block052Part015CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block052Part015SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block052Part015] using hcert

def TailChunk001Sub001Block052Part016SupportExplicit : Finset ℕ :=
  ([26893] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block052Part016 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block052Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26893
    = surrogateDiagTailX0RatChunk001Sub001Block052Part016

theorem surrogateDiagonalTailChunk001Sub001Block052Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block052Part016CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block052Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block052Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block052Part016CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block052Part016SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block052Part016] using hcert

def TailChunk001Sub001Block052Part017SupportExplicit : Finset ℕ :=
  ([26894] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block052Part017 : ℚ :=
  (629672664625 : ℚ) / 33418263704012587008

def SurrogateDiagonalTailChunk001Sub001Block052Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26894
    = surrogateDiagTailX0RatChunk001Sub001Block052Part017

theorem surrogateDiagonalTailChunk001Sub001Block052Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block052Part017CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block052Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block052Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block052Part017CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block052Part017SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block052Part017] using hcert

def TailChunk001Sub001Block052Part018SupportExplicit : Finset ℕ :=
  ([26895] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block052Part018 : ℚ :=
  (6383180449 : ℚ) / 117569755393228800

def SurrogateDiagonalTailChunk001Sub001Block052Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26895
    = surrogateDiagTailX0RatChunk001Sub001Block052Part018

theorem surrogateDiagonalTailChunk001Sub001Block052Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block052Part018CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block052Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block052Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block052Part018CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block052Part018SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block052Part018] using hcert

def TailChunk001Sub001Block052Part019SupportExplicit : Finset ℕ :=
  ([26897] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block052Part019 : ℚ :=
  (402649615025 : ℚ) / 474158985579334877184

def SurrogateDiagonalTailChunk001Sub001Block052Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26897
    = surrogateDiagTailX0RatChunk001Sub001Block052Part019

theorem surrogateDiagonalTailChunk001Sub001Block052Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block052Part019CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block052Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block052Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block052Part019CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block052Part019SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block052Part019] using hcert

def TailChunk001Sub001Block052Part020SupportExplicit : Finset ℕ :=
  ([26898] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block052Part020 : ℚ :=
  (628072662725 : ℚ) / 8072429385624035904

def SurrogateDiagonalTailChunk001Sub001Block052Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26898
    = surrogateDiagTailX0RatChunk001Sub001Block052Part020

theorem surrogateDiagonalTailChunk001Sub001Block052Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block052Part020CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block052Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block052Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block052Part020CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block052Part020SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block052Part020] using hcert

def TailChunk001Sub001Block052Part021SupportExplicit : Finset ℕ :=
  ([26899] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block052Part021 : ℚ :=
  (241559843275 : ℚ) / 1166764870626677803008

def SurrogateDiagonalTailChunk001Sub001Block052Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26899
    = surrogateDiagTailX0RatChunk001Sub001Block052Part021

theorem surrogateDiagonalTailChunk001Sub001Block052Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block052Part021CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block052Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block052Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block052Part021CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block052Part021SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block052Part021] using hcert

def TailChunk001Sub001Block052Part022SupportExplicit : Finset ℕ :=
  ([26902] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block052Part022 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block052Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26902
    = surrogateDiagTailX0RatChunk001Sub001Block052Part022

theorem surrogateDiagonalTailChunk001Sub001Block052Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block052Part022CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block052Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block052Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block052Part022CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block052Part022SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block052Part022] using hcert

def TailChunk001Sub001Block052Part023SupportExplicit : Finset ℕ :=
  ([26903] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block052Part023 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block052Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26903
    = surrogateDiagTailX0RatChunk001Sub001Block052Part023

theorem surrogateDiagonalTailChunk001Sub001Block052Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block052Part023CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block052Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block052Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block052Part023CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block052Part023SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block052Part023] using hcert

def TailChunk001Sub001Block052Part024SupportExplicit : Finset ℕ :=
  ([26905] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block052Part024 : ℚ :=
  (4827401373 : ℚ) / 1430094245577850880

def SurrogateDiagonalTailChunk001Sub001Block052Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26905
    = surrogateDiagTailX0RatChunk001Sub001Block052Part024

theorem surrogateDiagonalTailChunk001Sub001Block052Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block052Part024CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block052Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block052Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block052Part024CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block052Part024SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block052Part024] using hcert

def surrogateDiagonalTailChunk001Sub001Block052HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub001Block052Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block052Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block052Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block052Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block052Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block052Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block052Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block052Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block052Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block052Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub001Block052Head : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block052Part000
    + surrogateDiagTailX0RatChunk001Sub001Block052Part001
    + surrogateDiagTailX0RatChunk001Sub001Block052Part002
    + surrogateDiagTailX0RatChunk001Sub001Block052Part003
    + surrogateDiagTailX0RatChunk001Sub001Block052Part004
    + surrogateDiagTailX0RatChunk001Sub001Block052Part005
    + surrogateDiagTailX0RatChunk001Sub001Block052Part006
    + surrogateDiagTailX0RatChunk001Sub001Block052Part007
    + surrogateDiagTailX0RatChunk001Sub001Block052Part008
    + surrogateDiagTailX0RatChunk001Sub001Block052Part009

def surrogateDiagonalTailChunk001Sub001Block052MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub001Block052Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block052Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block052Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block052Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block052Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block052Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block052Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block052Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block052Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block052Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub001Block052Mid : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block052Part010
    + surrogateDiagTailX0RatChunk001Sub001Block052Part011
    + surrogateDiagTailX0RatChunk001Sub001Block052Part012
    + surrogateDiagTailX0RatChunk001Sub001Block052Part013
    + surrogateDiagTailX0RatChunk001Sub001Block052Part014
    + surrogateDiagTailX0RatChunk001Sub001Block052Part015
    + surrogateDiagTailX0RatChunk001Sub001Block052Part016
    + surrogateDiagTailX0RatChunk001Sub001Block052Part017
    + surrogateDiagTailX0RatChunk001Sub001Block052Part018
    + surrogateDiagTailX0RatChunk001Sub001Block052Part019

def surrogateDiagonalTailChunk001Sub001Block052TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub001Block052Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block052Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block052Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block052Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block052Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub001Block052Tail : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block052Part020
    + surrogateDiagTailX0RatChunk001Sub001Block052Part021
    + surrogateDiagTailX0RatChunk001Sub001Block052Part022
    + surrogateDiagTailX0RatChunk001Sub001Block052Part023
    + surrogateDiagTailX0RatChunk001Sub001Block052Part024

def surrogateDiagonalTailChunk001Sub001Block052Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk001Sub001Block052HeadSum X0
    + surrogateDiagonalTailChunk001Sub001Block052MidSum X0
    + surrogateDiagonalTailChunk001Sub001Block052TailSum X0

def surrogateDiagTailX0RatChunk001Sub001Block052 : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block052Part000
    + surrogateDiagTailX0RatChunk001Sub001Block052Part001
    + surrogateDiagTailX0RatChunk001Sub001Block052Part002
    + surrogateDiagTailX0RatChunk001Sub001Block052Part003
    + surrogateDiagTailX0RatChunk001Sub001Block052Part004
    + surrogateDiagTailX0RatChunk001Sub001Block052Part005
    + surrogateDiagTailX0RatChunk001Sub001Block052Part006
    + surrogateDiagTailX0RatChunk001Sub001Block052Part007
    + surrogateDiagTailX0RatChunk001Sub001Block052Part008
    + surrogateDiagTailX0RatChunk001Sub001Block052Part009
    + surrogateDiagTailX0RatChunk001Sub001Block052Part010
    + surrogateDiagTailX0RatChunk001Sub001Block052Part011
    + surrogateDiagTailX0RatChunk001Sub001Block052Part012
    + surrogateDiagTailX0RatChunk001Sub001Block052Part013
    + surrogateDiagTailX0RatChunk001Sub001Block052Part014
    + surrogateDiagTailX0RatChunk001Sub001Block052Part015
    + surrogateDiagTailX0RatChunk001Sub001Block052Part016
    + surrogateDiagTailX0RatChunk001Sub001Block052Part017
    + surrogateDiagTailX0RatChunk001Sub001Block052Part018
    + surrogateDiagTailX0RatChunk001Sub001Block052Part019
    + surrogateDiagTailX0RatChunk001Sub001Block052Part020
    + surrogateDiagTailX0RatChunk001Sub001Block052Part021
    + surrogateDiagTailX0RatChunk001Sub001Block052Part022
    + surrogateDiagTailX0RatChunk001Sub001Block052Part023
    + surrogateDiagTailX0RatChunk001Sub001Block052Part024

theorem surrogateDiagTailX0RatChunk001Sub001Block052_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk001Sub001Block052Head + surrogateDiagTailX0RatChunk001Sub001Block052Mid + surrogateDiagTailX0RatChunk001Sub001Block052Tail =
      surrogateDiagTailX0RatChunk001Sub001Block052 := by
  unfold surrogateDiagTailX0RatChunk001Sub001Block052Head surrogateDiagTailX0RatChunk001Sub001Block052Mid surrogateDiagTailX0RatChunk001Sub001Block052Tail surrogateDiagTailX0RatChunk001Sub001Block052
  ring

def SurrogateDiagonalTailChunk001Sub001Block052HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub001Block052HeadSum X0 = surrogateDiagTailX0RatChunk001Sub001Block052Head

def SurrogateDiagonalTailChunk001Sub001Block052MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub001Block052MidSum X0 = surrogateDiagTailX0RatChunk001Sub001Block052Mid

def SurrogateDiagonalTailChunk001Sub001Block052TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub001Block052TailSum X0 = surrogateDiagTailX0RatChunk001Sub001Block052Tail

theorem surrogateDiagonalTailChunk001Sub001Block052_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk001Sub001Block052HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk001Sub001Block052MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk001Sub001Block052TailCertificateAt X0) :
    surrogateDiagonalTailChunk001Sub001Block052Sum X0 = surrogateDiagTailX0RatChunk001Sub001Block052 := by
  unfold SurrogateDiagonalTailChunk001Sub001Block052HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk001Sub001Block052MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk001Sub001Block052TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk001Sub001Block052Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk001Sub001Block052_eq_head_add_mid_add_tail

/-- Block 053 covers tail-support indices [16325,16350) and q from 26906 to 26945. -/

def TailChunk001Sub001Block053Part000SupportExplicit : Finset ℕ :=
  ([26906] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block053Part000 : ℚ :=
  (5016323727 : ℚ) / 743447694692310400

def SurrogateDiagonalTailChunk001Sub001Block053Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26906
    = surrogateDiagTailX0RatChunk001Sub001Block053Part000

theorem surrogateDiagonalTailChunk001Sub001Block053Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block053Part000CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block053Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block053Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block053Part000CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block053Part000SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block053Part000] using hcert

def TailChunk001Sub001Block053Part001SupportExplicit : Finset ℕ :=
  ([26907] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block053Part001 : ℚ :=
  (1256797240825 : ℚ) / 64694781222976561152

def SurrogateDiagonalTailChunk001Sub001Block053Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26907
    = surrogateDiagTailX0RatChunk001Sub001Block053Part001

theorem surrogateDiagonalTailChunk001Sub001Block053Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block053Part001CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block053Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block053Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block053Part001CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block053Part001SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block053Part001] using hcert

def TailChunk001Sub001Block053Part002SupportExplicit : Finset ℕ :=
  ([26909] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block053Part002 : ℚ :=
  (1834214099 : ℚ) / 16342743139000790400

def SurrogateDiagonalTailChunk001Sub001Block053Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26909
    = surrogateDiagTailX0RatChunk001Sub001Block053Part002

theorem surrogateDiagonalTailChunk001Sub001Block053Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block053Part002CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block053Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block053Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block053Part002CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block053Part002SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block053Part002] using hcert

def TailChunk001Sub001Block053Part003SupportExplicit : Finset ℕ :=
  ([26911] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block053Part003 : ℚ :=
  (630304370275 : ℚ) / 1026437963064940167168

def SurrogateDiagonalTailChunk001Sub001Block053Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26911
    = surrogateDiagTailX0RatChunk001Sub001Block053Part003

theorem surrogateDiagonalTailChunk001Sub001Block053Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block053Part003CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block053Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block053Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block053Part003CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block053Part003SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block053Part003] using hcert

def TailChunk001Sub001Block053Part004SupportExplicit : Finset ℕ :=
  ([26913] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block053Part004 : ℚ :=
  (20117724853 : ℚ) / 1036040195215321920

def SurrogateDiagonalTailChunk001Sub001Block053Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26913
    = surrogateDiagTailX0RatChunk001Sub001Block053Part004

theorem surrogateDiagonalTailChunk001Sub001Block053Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block053Part004CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block053Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block053Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block053Part004CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block053Part004SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block053Part004] using hcert

def TailChunk001Sub001Block053Part005SupportExplicit : Finset ℕ :=
  ([26914] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block053Part005 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block053Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26914
    = surrogateDiagTailX0RatChunk001Sub001Block053Part005

theorem surrogateDiagonalTailChunk001Sub001Block053Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block053Part005CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block053Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block053Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block053Part005CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block053Part005SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block053Part005] using hcert

def TailChunk001Sub001Block053Part006SupportExplicit : Finset ℕ :=
  ([26915] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block053Part006 : ℚ :=
  (86334728375 : ℚ) / 12025564281660506112

def SurrogateDiagonalTailChunk001Sub001Block053Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26915
    = surrogateDiagTailX0RatChunk001Sub001Block053Part006

theorem surrogateDiagonalTailChunk001Sub001Block053Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block053Part006CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block053Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block053Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block053Part006CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block053Part006SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block053Part006] using hcert

def TailChunk001Sub001Block053Part007SupportExplicit : Finset ℕ :=
  ([26917] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block053Part007 : ℚ :=
  (1877106421 : ℚ) / 2237652682489288200

def SurrogateDiagonalTailChunk001Sub001Block053Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26917
    = surrogateDiagTailX0RatChunk001Sub001Block053Part007

theorem surrogateDiagonalTailChunk001Sub001Block053Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block053Part007CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block053Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block053Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block053Part007CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block053Part007SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block053Part007] using hcert

def TailChunk001Sub001Block053Part008SupportExplicit : Finset ℕ :=
  ([26918] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block053Part008 : ℚ :=
  (55126170725 : ℚ) / 36864844036900798464

def SurrogateDiagonalTailChunk001Sub001Block053Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26918
    = surrogateDiagTailX0RatChunk001Sub001Block053Part008

theorem surrogateDiagonalTailChunk001Sub001Block053Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block053Part008CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block053Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block053Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block053Part008CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block053Part008SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block053Part008] using hcert

def TailChunk001Sub001Block053Part009SupportExplicit : Finset ℕ :=
  ([26921] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block053Part009 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block053Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26921
    = surrogateDiagTailX0RatChunk001Sub001Block053Part009

theorem surrogateDiagonalTailChunk001Sub001Block053Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block053Part009CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block053Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block053Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block053Part009CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block053Part009SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block053Part009] using hcert

def TailChunk001Sub001Block053Part010SupportExplicit : Finset ℕ :=
  ([26922] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block053Part010 : ℚ :=
  (1826085167 : ℚ) / 12887478868377600

def SurrogateDiagonalTailChunk001Sub001Block053Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26922
    = surrogateDiagTailX0RatChunk001Sub001Block053Part010

theorem surrogateDiagonalTailChunk001Sub001Block053Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block053Part010CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block053Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block053Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block053Part010CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block053Part010SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block053Part010] using hcert

def TailChunk001Sub001Block053Part011SupportExplicit : Finset ℕ :=
  ([26923] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block053Part011 : ℚ :=
  (247023361225 : ℚ) / 185130039632393797632

def SurrogateDiagonalTailChunk001Sub001Block053Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26923
    = surrogateDiagTailX0RatChunk001Sub001Block053Part011

theorem surrogateDiagonalTailChunk001Sub001Block053Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block053Part011CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block053Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block053Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block053Part011CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block053Part011SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block053Part011] using hcert

def TailChunk001Sub001Block053Part012SupportExplicit : Finset ℕ :=
  ([26926] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block053Part012 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block053Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26926
    = surrogateDiagTailX0RatChunk001Sub001Block053Part012

theorem surrogateDiagonalTailChunk001Sub001Block053Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block053Part012CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block053Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block053Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block053Part012CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block053Part012SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block053Part012] using hcert

def TailChunk001Sub001Block053Part013SupportExplicit : Finset ℕ :=
  ([26927] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block053Part013 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block053Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26927
    = surrogateDiagTailX0RatChunk001Sub001Block053Part013

theorem surrogateDiagonalTailChunk001Sub001Block053Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block053Part013CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block053Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block053Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block053Part013CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block053Part013SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block053Part013] using hcert

def TailChunk001Sub001Block053Part014SupportExplicit : Finset ℕ :=
  ([26929] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block053Part014 : ℚ :=
  (925234793375 : ℚ) / 354518566339303508544

def SurrogateDiagonalTailChunk001Sub001Block053Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26929
    = surrogateDiagTailX0RatChunk001Sub001Block053Part014

theorem surrogateDiagonalTailChunk001Sub001Block053Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block053Part014CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block053Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block053Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block053Part014CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block053Part014SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block053Part014] using hcert

def TailChunk001Sub001Block053Part015SupportExplicit : Finset ℕ :=
  ([26930] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block053Part015 : ℚ :=
  (906927145525 : ℚ) / 33617626394920255488

def SurrogateDiagonalTailChunk001Sub001Block053Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26930
    = surrogateDiagTailX0RatChunk001Sub001Block053Part015

theorem surrogateDiagonalTailChunk001Sub001Block053Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block053Part015CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block053Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block053Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block053Part015CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block053Part015SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block053Part015] using hcert

def TailChunk001Sub001Block053Part016SupportExplicit : Finset ℕ :=
  ([26931] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block053Part016 : ℚ :=
  (196795010629 : ℚ) / 9337971914954803200

def SurrogateDiagonalTailChunk001Sub001Block053Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26931
    = surrogateDiagTailX0RatChunk001Sub001Block053Part016

theorem surrogateDiagonalTailChunk001Sub001Block053Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block053Part016CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block053Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block053Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block053Part016CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block053Part016SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block053Part016] using hcert

def TailChunk001Sub001Block053Part017SupportExplicit : Finset ℕ :=
  ([26933] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block053Part017 : ℚ :=
  (17372162641 : ℚ) / 43905711613021315200

def SurrogateDiagonalTailChunk001Sub001Block053Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26933
    = surrogateDiagTailX0RatChunk001Sub001Block053Part017

theorem surrogateDiagonalTailChunk001Sub001Block053Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block053Part017CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block053Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block053Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block053Part017CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block053Part017SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block053Part017] using hcert

def TailChunk001Sub001Block053Part018SupportExplicit : Finset ℕ :=
  ([26935] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block053Part018 : ℚ :=
  (604770921375 : ℚ) / 179560566036864342016

def SurrogateDiagonalTailChunk001Sub001Block053Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26935
    = surrogateDiagTailX0RatChunk001Sub001Block053Part018

theorem surrogateDiagonalTailChunk001Sub001Block053Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block053Part018CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block053Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block053Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block053Part018CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block053Part018SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block053Part018] using hcert

def TailChunk001Sub001Block053Part019SupportExplicit : Finset ℕ :=
  ([26938] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block053Part019 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block053Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26938
    = surrogateDiagTailX0RatChunk001Sub001Block053Part019

theorem surrogateDiagonalTailChunk001Sub001Block053Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block053Part019CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block053Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block053Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block053Part019CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block053Part019SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block053Part019] using hcert

def TailChunk001Sub001Block053Part020SupportExplicit : Finset ℕ :=
  ([26939] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block053Part020 : ℚ :=
  (23687803 : ℚ) / 17354277661500000

def SurrogateDiagonalTailChunk001Sub001Block053Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26939
    = surrogateDiagTailX0RatChunk001Sub001Block053Part020

theorem surrogateDiagonalTailChunk001Sub001Block053Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block053Part020CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block053Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block053Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block053Part020CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block053Part020SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block053Part020] using hcert

def TailChunk001Sub001Block053Part021SupportExplicit : Finset ℕ :=
  ([26941] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block053Part021 : ℚ :=
  (23136406425 : ℚ) / 94988196738513240064

def SurrogateDiagonalTailChunk001Sub001Block053Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26941
    = surrogateDiagTailX0RatChunk001Sub001Block053Part021

theorem surrogateDiagonalTailChunk001Sub001Block053Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block053Part021CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block053Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block053Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block053Part021CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block053Part021SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block053Part021] using hcert

def TailChunk001Sub001Block053Part022SupportExplicit : Finset ℕ :=
  ([26942] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block053Part022 : ℚ :=
  (24962447375 : ℚ) / 7328370209781123072

def SurrogateDiagonalTailChunk001Sub001Block053Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26942
    = surrogateDiagTailX0RatChunk001Sub001Block053Part022

theorem surrogateDiagonalTailChunk001Sub001Block053Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block053Part022CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block053Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block053Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block053Part022CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block053Part022SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block053Part022] using hcert

def TailChunk001Sub001Block053Part023SupportExplicit : Finset ℕ :=
  ([26943] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block053Part023 : ℚ :=
  (256967548825 : ℚ) / 7780928753674699776

def SurrogateDiagonalTailChunk001Sub001Block053Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26943
    = surrogateDiagTailX0RatChunk001Sub001Block053Part023

theorem surrogateDiagonalTailChunk001Sub001Block053Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block053Part023CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block053Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block053Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block053Part023CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block053Part023SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block053Part023] using hcert

def TailChunk001Sub001Block053Part024SupportExplicit : Finset ℕ :=
  ([26945] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block053Part024 : ℚ :=
  (166021065225 : ℚ) / 34858912903409434624

def SurrogateDiagonalTailChunk001Sub001Block053Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26945
    = surrogateDiagTailX0RatChunk001Sub001Block053Part024

theorem surrogateDiagonalTailChunk001Sub001Block053Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block053Part024CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block053Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block053Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block053Part024CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block053Part024SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block053Part024] using hcert

def surrogateDiagonalTailChunk001Sub001Block053HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub001Block053Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block053Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block053Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block053Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block053Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block053Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block053Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block053Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block053Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block053Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub001Block053Head : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block053Part000
    + surrogateDiagTailX0RatChunk001Sub001Block053Part001
    + surrogateDiagTailX0RatChunk001Sub001Block053Part002
    + surrogateDiagTailX0RatChunk001Sub001Block053Part003
    + surrogateDiagTailX0RatChunk001Sub001Block053Part004
    + surrogateDiagTailX0RatChunk001Sub001Block053Part005
    + surrogateDiagTailX0RatChunk001Sub001Block053Part006
    + surrogateDiagTailX0RatChunk001Sub001Block053Part007
    + surrogateDiagTailX0RatChunk001Sub001Block053Part008
    + surrogateDiagTailX0RatChunk001Sub001Block053Part009

def surrogateDiagonalTailChunk001Sub001Block053MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub001Block053Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block053Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block053Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block053Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block053Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block053Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block053Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block053Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block053Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block053Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub001Block053Mid : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block053Part010
    + surrogateDiagTailX0RatChunk001Sub001Block053Part011
    + surrogateDiagTailX0RatChunk001Sub001Block053Part012
    + surrogateDiagTailX0RatChunk001Sub001Block053Part013
    + surrogateDiagTailX0RatChunk001Sub001Block053Part014
    + surrogateDiagTailX0RatChunk001Sub001Block053Part015
    + surrogateDiagTailX0RatChunk001Sub001Block053Part016
    + surrogateDiagTailX0RatChunk001Sub001Block053Part017
    + surrogateDiagTailX0RatChunk001Sub001Block053Part018
    + surrogateDiagTailX0RatChunk001Sub001Block053Part019

def surrogateDiagonalTailChunk001Sub001Block053TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub001Block053Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block053Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block053Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block053Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block053Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub001Block053Tail : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block053Part020
    + surrogateDiagTailX0RatChunk001Sub001Block053Part021
    + surrogateDiagTailX0RatChunk001Sub001Block053Part022
    + surrogateDiagTailX0RatChunk001Sub001Block053Part023
    + surrogateDiagTailX0RatChunk001Sub001Block053Part024

def surrogateDiagonalTailChunk001Sub001Block053Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk001Sub001Block053HeadSum X0
    + surrogateDiagonalTailChunk001Sub001Block053MidSum X0
    + surrogateDiagonalTailChunk001Sub001Block053TailSum X0

def surrogateDiagTailX0RatChunk001Sub001Block053 : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block053Part000
    + surrogateDiagTailX0RatChunk001Sub001Block053Part001
    + surrogateDiagTailX0RatChunk001Sub001Block053Part002
    + surrogateDiagTailX0RatChunk001Sub001Block053Part003
    + surrogateDiagTailX0RatChunk001Sub001Block053Part004
    + surrogateDiagTailX0RatChunk001Sub001Block053Part005
    + surrogateDiagTailX0RatChunk001Sub001Block053Part006
    + surrogateDiagTailX0RatChunk001Sub001Block053Part007
    + surrogateDiagTailX0RatChunk001Sub001Block053Part008
    + surrogateDiagTailX0RatChunk001Sub001Block053Part009
    + surrogateDiagTailX0RatChunk001Sub001Block053Part010
    + surrogateDiagTailX0RatChunk001Sub001Block053Part011
    + surrogateDiagTailX0RatChunk001Sub001Block053Part012
    + surrogateDiagTailX0RatChunk001Sub001Block053Part013
    + surrogateDiagTailX0RatChunk001Sub001Block053Part014
    + surrogateDiagTailX0RatChunk001Sub001Block053Part015
    + surrogateDiagTailX0RatChunk001Sub001Block053Part016
    + surrogateDiagTailX0RatChunk001Sub001Block053Part017
    + surrogateDiagTailX0RatChunk001Sub001Block053Part018
    + surrogateDiagTailX0RatChunk001Sub001Block053Part019
    + surrogateDiagTailX0RatChunk001Sub001Block053Part020
    + surrogateDiagTailX0RatChunk001Sub001Block053Part021
    + surrogateDiagTailX0RatChunk001Sub001Block053Part022
    + surrogateDiagTailX0RatChunk001Sub001Block053Part023
    + surrogateDiagTailX0RatChunk001Sub001Block053Part024

theorem surrogateDiagTailX0RatChunk001Sub001Block053_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk001Sub001Block053Head + surrogateDiagTailX0RatChunk001Sub001Block053Mid + surrogateDiagTailX0RatChunk001Sub001Block053Tail =
      surrogateDiagTailX0RatChunk001Sub001Block053 := by
  unfold surrogateDiagTailX0RatChunk001Sub001Block053Head surrogateDiagTailX0RatChunk001Sub001Block053Mid surrogateDiagTailX0RatChunk001Sub001Block053Tail surrogateDiagTailX0RatChunk001Sub001Block053
  ring

def SurrogateDiagonalTailChunk001Sub001Block053HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub001Block053HeadSum X0 = surrogateDiagTailX0RatChunk001Sub001Block053Head

def SurrogateDiagonalTailChunk001Sub001Block053MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub001Block053MidSum X0 = surrogateDiagTailX0RatChunk001Sub001Block053Mid

def SurrogateDiagonalTailChunk001Sub001Block053TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub001Block053TailSum X0 = surrogateDiagTailX0RatChunk001Sub001Block053Tail

theorem surrogateDiagonalTailChunk001Sub001Block053_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk001Sub001Block053HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk001Sub001Block053MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk001Sub001Block053TailCertificateAt X0) :
    surrogateDiagonalTailChunk001Sub001Block053Sum X0 = surrogateDiagTailX0RatChunk001Sub001Block053 := by
  unfold SurrogateDiagonalTailChunk001Sub001Block053HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk001Sub001Block053MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk001Sub001Block053TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk001Sub001Block053Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk001Sub001Block053_eq_head_add_mid_add_tail

/-- Block 054 covers tail-support indices [16350,16375) and q from 26947 to 26989. -/

def TailChunk001Sub001Block054Part000SupportExplicit : Finset ℕ :=
  ([26947] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block054Part000 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block054Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26947
    = surrogateDiagTailX0RatChunk001Sub001Block054Part000

theorem surrogateDiagonalTailChunk001Sub001Block054Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block054Part000CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block054Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block054Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block054Part000CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block054Part000SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block054Part000] using hcert

def TailChunk001Sub001Block054Part001SupportExplicit : Finset ℕ :=
  ([26949] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block054Part001 : ℚ :=
  (92990728643 : ℚ) / 3760955409121689600

def SurrogateDiagonalTailChunk001Sub001Block054Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26949
    = surrogateDiagTailX0RatChunk001Sub001Block054Part001

theorem surrogateDiagonalTailChunk001Sub001Block054Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block054Part001CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block054Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block054Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block054Part001CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block054Part001SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block054Part001] using hcert

def TailChunk001Sub001Block054Part002SupportExplicit : Finset ℕ :=
  ([26951] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block054Part002 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block054Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26951
    = surrogateDiagTailX0RatChunk001Sub001Block054Part002

theorem surrogateDiagonalTailChunk001Sub001Block054Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block054Part002CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block054Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block054Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block054Part002CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block054Part002SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block054Part002] using hcert

def TailChunk001Sub001Block054Part003SupportExplicit : Finset ℕ :=
  ([26953] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block054Part003 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block054Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26953
    = surrogateDiagTailX0RatChunk001Sub001Block054Part003

theorem surrogateDiagonalTailChunk001Sub001Block054Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block054Part003CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block054Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block054Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block054Part003CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block054Part003SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block054Part003] using hcert

def TailChunk001Sub001Block054Part004SupportExplicit : Finset ℕ :=
  ([26954] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block054Part004 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block054Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26954
    = surrogateDiagTailX0RatChunk001Sub001Block054Part004

theorem surrogateDiagonalTailChunk001Sub001Block054Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block054Part004CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block054Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block054Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block054Part004CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block054Part004SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block054Part004] using hcert

def TailChunk001Sub001Block054Part005SupportExplicit : Finset ℕ :=
  ([26957] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block054Part005 : ℚ :=
  (37086336347 : ℚ) / 14239829001321000000

def SurrogateDiagonalTailChunk001Sub001Block054Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26957
    = surrogateDiagTailX0RatChunk001Sub001Block054Part005

theorem surrogateDiagonalTailChunk001Sub001Block054Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block054Part005CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block054Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block054Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block054Part005CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block054Part005SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block054Part005] using hcert

def TailChunk001Sub001Block054Part006SupportExplicit : Finset ℕ :=
  ([26958] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block054Part006 : ℚ :=
  (19714907425 : ℚ) / 254522311025908512

def SurrogateDiagonalTailChunk001Sub001Block054Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26958
    = surrogateDiagTailX0RatChunk001Sub001Block054Part006

theorem surrogateDiagonalTailChunk001Sub001Block054Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block054Part006CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block054Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block054Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block054Part006CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block054Part006SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block054Part006] using hcert

def TailChunk001Sub001Block054Part007SupportExplicit : Finset ℕ :=
  ([26959] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block054Part007 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block054Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26959
    = surrogateDiagTailX0RatChunk001Sub001Block054Part007

theorem surrogateDiagonalTailChunk001Sub001Block054Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block054Part007CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block054Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block054Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block054Part007CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block054Part007SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block054Part007] using hcert

def TailChunk001Sub001Block054Part008SupportExplicit : Finset ℕ :=
  ([26961] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block054Part008 : ℚ :=
  (88768021691 : ℚ) / 2613749839806873600

def SurrogateDiagonalTailChunk001Sub001Block054Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26961
    = surrogateDiagTailX0RatChunk001Sub001Block054Part008

theorem surrogateDiagonalTailChunk001Sub001Block054Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block054Part008CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block054Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block054Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block054Part008CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block054Part008SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block054Part008] using hcert

def TailChunk001Sub001Block054Part009SupportExplicit : Finset ℕ :=
  ([26962] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block054Part009 : ℚ :=
  (5016369067 : ℚ) / 440389316955340800

def SurrogateDiagonalTailChunk001Sub001Block054Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26962
    = surrogateDiagTailX0RatChunk001Sub001Block054Part009

theorem surrogateDiagonalTailChunk001Sub001Block054Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block054Part009CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block054Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block054Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block054Part009CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block054Part009SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block054Part009] using hcert

def TailChunk001Sub001Block054Part010SupportExplicit : Finset ℕ :=
  ([26963] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block054Part010 : ℚ :=
  (80424196625 : ℚ) / 611741872543306235904

def SurrogateDiagonalTailChunk001Sub001Block054Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26963
    = surrogateDiagTailX0RatChunk001Sub001Block054Part010

theorem surrogateDiagonalTailChunk001Sub001Block054Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block054Part010CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block054Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block054Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block054Part010CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block054Part010SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block054Part010] using hcert

def TailChunk001Sub001Block054Part011SupportExplicit : Finset ℕ :=
  ([26965] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block054Part011 : ℚ :=
  (606118171125 : ℚ) / 180362025380815568896

def SurrogateDiagonalTailChunk001Sub001Block054Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26965
    = surrogateDiagTailX0RatChunk001Sub001Block054Part011

theorem surrogateDiagonalTailChunk001Sub001Block054Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block054Part011CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block054Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block054Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block054Part011CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block054Part011SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block054Part011] using hcert

def TailChunk001Sub001Block054Part012SupportExplicit : Finset ℕ :=
  ([26966] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block054Part012 : ℚ :=
  (18201070375 : ℚ) / 19256091694703050752

def SurrogateDiagonalTailChunk001Sub001Block054Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26966
    = surrogateDiagTailX0RatChunk001Sub001Block054Part012

theorem surrogateDiagonalTailChunk001Sub001Block054Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block054Part012CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block054Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block054Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block054Part012CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block054Part012SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block054Part012] using hcert

def TailChunk001Sub001Block054Part013SupportExplicit : Finset ℕ :=
  ([26967] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block054Part013 : ℚ :=
  (6007218159 : ℚ) / 290819538944000000

def SurrogateDiagonalTailChunk001Sub001Block054Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26967
    = surrogateDiagTailX0RatChunk001Sub001Block054Part013

theorem surrogateDiagonalTailChunk001Sub001Block054Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block054Part013CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block054Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block054Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block054Part013CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block054Part013SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block054Part013] using hcert

def TailChunk001Sub001Block054Part014SupportExplicit : Finset ℕ :=
  ([26969] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block054Part014 : ℚ :=
  (1376614031 : ℚ) / 16792002007127654400

def SurrogateDiagonalTailChunk001Sub001Block054Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26969
    = surrogateDiagTailX0RatChunk001Sub001Block054Part014

theorem surrogateDiagonalTailChunk001Sub001Block054Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block054Part014CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block054Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block054Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block054Part014CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block054Part014SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block054Part014] using hcert

def TailChunk001Sub001Block054Part015SupportExplicit : Finset ℕ :=
  ([26970] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block054Part015 : ℚ :=
  (51440758333 : ℚ) / 203968894677811200

def SurrogateDiagonalTailChunk001Sub001Block054Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26970
    = surrogateDiagTailX0RatChunk001Sub001Block054Part015

theorem surrogateDiagonalTailChunk001Sub001Block054Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block054Part015CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block054Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block054Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block054Part015CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block054Part015SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block054Part015] using hcert

def TailChunk001Sub001Block054Part016SupportExplicit : Finset ℕ :=
  ([26971] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block054Part016 : ℚ :=
  (928120966175 : ℚ) / 356736033023426601984

def SurrogateDiagonalTailChunk001Sub001Block054Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26971
    = surrogateDiagTailX0RatChunk001Sub001Block054Part016

theorem surrogateDiagonalTailChunk001Sub001Block054Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block054Part016CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block054Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block054Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block054Part016CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block054Part016SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block054Part016] using hcert

def TailChunk001Sub001Block054Part017SupportExplicit : Finset ℕ :=
  ([26974] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block054Part017 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block054Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26974
    = surrogateDiagTailX0RatChunk001Sub001Block054Part017

theorem surrogateDiagonalTailChunk001Sub001Block054Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block054Part017CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block054Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block054Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block054Part017CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block054Part017SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block054Part017] using hcert

def TailChunk001Sub001Block054Part018SupportExplicit : Finset ℕ :=
  ([26977] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block054Part018 : ℚ :=
  (3694965375 : ℚ) / 25366108466583279616

def SurrogateDiagonalTailChunk001Sub001Block054Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26977
    = surrogateDiagTailX0RatChunk001Sub001Block054Part018

theorem surrogateDiagonalTailChunk001Sub001Block054Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block054Part018CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block054Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block054Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block054Part018CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block054Part018SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block054Part018] using hcert

def TailChunk001Sub001Block054Part019SupportExplicit : Finset ℕ :=
  ([26978] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block054Part019 : ℚ :=
  (31632304849 : ℚ) / 1485809544344371200

def SurrogateDiagonalTailChunk001Sub001Block054Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26978
    = surrogateDiagTailX0RatChunk001Sub001Block054Part019

theorem surrogateDiagonalTailChunk001Sub001Block054Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block054Part019CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block054Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block054Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block054Part019CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block054Part019SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block054Part019] using hcert

def TailChunk001Sub001Block054Part020SupportExplicit : Finset ℕ :=
  ([26981] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block054Part020 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block054Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26981
    = surrogateDiagTailX0RatChunk001Sub001Block054Part020

theorem surrogateDiagonalTailChunk001Sub001Block054Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block054Part020CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block054Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block054Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block054Part020CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block054Part020SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block054Part020] using hcert

def TailChunk001Sub001Block054Part021SupportExplicit : Finset ℕ :=
  ([26985] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block054Part021 : ℚ :=
  (393929767525 : ℚ) / 6334453613384957952

def SurrogateDiagonalTailChunk001Sub001Block054Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26985
    = surrogateDiagTailX0RatChunk001Sub001Block054Part021

theorem surrogateDiagonalTailChunk001Sub001Block054Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block054Part021CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block054Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block054Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block054Part021CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block054Part021SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block054Part021] using hcert

def TailChunk001Sub001Block054Part022SupportExplicit : Finset ℕ :=
  ([26986] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block054Part022 : ℚ :=
  (167925449 : ℚ) / 181891341122025600

def SurrogateDiagonalTailChunk001Sub001Block054Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26986
    = surrogateDiagTailX0RatChunk001Sub001Block054Part022

theorem surrogateDiagonalTailChunk001Sub001Block054Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block054Part022CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block054Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block054Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block054Part022CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block054Part022SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block054Part022] using hcert

def TailChunk001Sub001Block054Part023SupportExplicit : Finset ℕ :=
  ([26987] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block054Part023 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block054Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26987
    = surrogateDiagTailX0RatChunk001Sub001Block054Part023

theorem surrogateDiagonalTailChunk001Sub001Block054Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block054Part023CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block054Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block054Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block054Part023CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block054Part023SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block054Part023] using hcert

def TailChunk001Sub001Block054Part024SupportExplicit : Finset ℕ :=
  ([26989] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block054Part024 : ℚ :=
  (102814683025 : ℚ) / 1262428463326466408448

def SurrogateDiagonalTailChunk001Sub001Block054Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26989
    = surrogateDiagTailX0RatChunk001Sub001Block054Part024

theorem surrogateDiagonalTailChunk001Sub001Block054Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block054Part024CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block054Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block054Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block054Part024CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block054Part024SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block054Part024] using hcert

def surrogateDiagonalTailChunk001Sub001Block054HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub001Block054Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block054Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block054Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block054Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block054Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block054Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block054Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block054Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block054Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block054Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub001Block054Head : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block054Part000
    + surrogateDiagTailX0RatChunk001Sub001Block054Part001
    + surrogateDiagTailX0RatChunk001Sub001Block054Part002
    + surrogateDiagTailX0RatChunk001Sub001Block054Part003
    + surrogateDiagTailX0RatChunk001Sub001Block054Part004
    + surrogateDiagTailX0RatChunk001Sub001Block054Part005
    + surrogateDiagTailX0RatChunk001Sub001Block054Part006
    + surrogateDiagTailX0RatChunk001Sub001Block054Part007
    + surrogateDiagTailX0RatChunk001Sub001Block054Part008
    + surrogateDiagTailX0RatChunk001Sub001Block054Part009

def surrogateDiagonalTailChunk001Sub001Block054MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub001Block054Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block054Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block054Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block054Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block054Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block054Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block054Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block054Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block054Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block054Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub001Block054Mid : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block054Part010
    + surrogateDiagTailX0RatChunk001Sub001Block054Part011
    + surrogateDiagTailX0RatChunk001Sub001Block054Part012
    + surrogateDiagTailX0RatChunk001Sub001Block054Part013
    + surrogateDiagTailX0RatChunk001Sub001Block054Part014
    + surrogateDiagTailX0RatChunk001Sub001Block054Part015
    + surrogateDiagTailX0RatChunk001Sub001Block054Part016
    + surrogateDiagTailX0RatChunk001Sub001Block054Part017
    + surrogateDiagTailX0RatChunk001Sub001Block054Part018
    + surrogateDiagTailX0RatChunk001Sub001Block054Part019

def surrogateDiagonalTailChunk001Sub001Block054TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub001Block054Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block054Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block054Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block054Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block054Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub001Block054Tail : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block054Part020
    + surrogateDiagTailX0RatChunk001Sub001Block054Part021
    + surrogateDiagTailX0RatChunk001Sub001Block054Part022
    + surrogateDiagTailX0RatChunk001Sub001Block054Part023
    + surrogateDiagTailX0RatChunk001Sub001Block054Part024

def surrogateDiagonalTailChunk001Sub001Block054Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk001Sub001Block054HeadSum X0
    + surrogateDiagonalTailChunk001Sub001Block054MidSum X0
    + surrogateDiagonalTailChunk001Sub001Block054TailSum X0

def surrogateDiagTailX0RatChunk001Sub001Block054 : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block054Part000
    + surrogateDiagTailX0RatChunk001Sub001Block054Part001
    + surrogateDiagTailX0RatChunk001Sub001Block054Part002
    + surrogateDiagTailX0RatChunk001Sub001Block054Part003
    + surrogateDiagTailX0RatChunk001Sub001Block054Part004
    + surrogateDiagTailX0RatChunk001Sub001Block054Part005
    + surrogateDiagTailX0RatChunk001Sub001Block054Part006
    + surrogateDiagTailX0RatChunk001Sub001Block054Part007
    + surrogateDiagTailX0RatChunk001Sub001Block054Part008
    + surrogateDiagTailX0RatChunk001Sub001Block054Part009
    + surrogateDiagTailX0RatChunk001Sub001Block054Part010
    + surrogateDiagTailX0RatChunk001Sub001Block054Part011
    + surrogateDiagTailX0RatChunk001Sub001Block054Part012
    + surrogateDiagTailX0RatChunk001Sub001Block054Part013
    + surrogateDiagTailX0RatChunk001Sub001Block054Part014
    + surrogateDiagTailX0RatChunk001Sub001Block054Part015
    + surrogateDiagTailX0RatChunk001Sub001Block054Part016
    + surrogateDiagTailX0RatChunk001Sub001Block054Part017
    + surrogateDiagTailX0RatChunk001Sub001Block054Part018
    + surrogateDiagTailX0RatChunk001Sub001Block054Part019
    + surrogateDiagTailX0RatChunk001Sub001Block054Part020
    + surrogateDiagTailX0RatChunk001Sub001Block054Part021
    + surrogateDiagTailX0RatChunk001Sub001Block054Part022
    + surrogateDiagTailX0RatChunk001Sub001Block054Part023
    + surrogateDiagTailX0RatChunk001Sub001Block054Part024

theorem surrogateDiagTailX0RatChunk001Sub001Block054_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk001Sub001Block054Head + surrogateDiagTailX0RatChunk001Sub001Block054Mid + surrogateDiagTailX0RatChunk001Sub001Block054Tail =
      surrogateDiagTailX0RatChunk001Sub001Block054 := by
  unfold surrogateDiagTailX0RatChunk001Sub001Block054Head surrogateDiagTailX0RatChunk001Sub001Block054Mid surrogateDiagTailX0RatChunk001Sub001Block054Tail surrogateDiagTailX0RatChunk001Sub001Block054
  ring

def SurrogateDiagonalTailChunk001Sub001Block054HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub001Block054HeadSum X0 = surrogateDiagTailX0RatChunk001Sub001Block054Head

def SurrogateDiagonalTailChunk001Sub001Block054MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub001Block054MidSum X0 = surrogateDiagTailX0RatChunk001Sub001Block054Mid

def SurrogateDiagonalTailChunk001Sub001Block054TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub001Block054TailSum X0 = surrogateDiagTailX0RatChunk001Sub001Block054Tail

theorem surrogateDiagonalTailChunk001Sub001Block054_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk001Sub001Block054HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk001Sub001Block054MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk001Sub001Block054TailCertificateAt X0) :
    surrogateDiagonalTailChunk001Sub001Block054Sum X0 = surrogateDiagTailX0RatChunk001Sub001Block054 := by
  unfold SurrogateDiagonalTailChunk001Sub001Block054HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk001Sub001Block054MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk001Sub001Block054TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk001Sub001Block054Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk001Sub001Block054_eq_head_add_mid_add_tail

/-- Block 055 covers tail-support indices [16375,16400) and q from 26990 to 27030. -/

def TailChunk001Sub001Block055Part000SupportExplicit : Finset ℕ :=
  ([26990] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block055Part000 : ℚ :=
  (12830546975 : ℚ) / 477723116491634688

def SurrogateDiagonalTailChunk001Sub001Block055Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26990
    = surrogateDiagTailX0RatChunk001Sub001Block055Part000

theorem surrogateDiagonalTailChunk001Sub001Block055Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block055Part000CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block055Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block055Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block055Part000CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block055Part000SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block055Part000] using hcert

def TailChunk001Sub001Block055Part001SupportExplicit : Finset ℕ :=
  ([26993] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block055Part001 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block055Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26993
    = surrogateDiagTailX0RatChunk001Sub001Block055Part001

theorem surrogateDiagonalTailChunk001Sub001Block055Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block055Part001CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block055Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block055Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block055Part001CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block055Part001SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block055Part001] using hcert

def TailChunk001Sub001Block055Part002SupportExplicit : Finset ℕ :=
  ([26994] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block055Part002 : ℚ :=
  (321487297 : ℚ) / 2771580534865920

def SurrogateDiagonalTailChunk001Sub001Block055Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26994
    = surrogateDiagTailX0RatChunk001Sub001Block055Part002

theorem surrogateDiagonalTailChunk001Sub001Block055Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block055Part002CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block055Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block055Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block055Part002CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block055Part002SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block055Part002] using hcert

def TailChunk001Sub001Block055Part003SupportExplicit : Finset ℕ :=
  ([26995] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block055Part003 : ℚ :=
  (607466920875 : ℚ) / 181166164690079881216

def SurrogateDiagonalTailChunk001Sub001Block055Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26995
    = surrogateDiagTailX0RatChunk001Sub001Block055Part003

theorem surrogateDiagonalTailChunk001Sub001Block055Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block055Part003CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block055Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block055Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block055Part003CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block055Part003SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block055Part003] using hcert

def TailChunk001Sub001Block055Part004SupportExplicit : Finset ℕ :=
  ([26997] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block055Part004 : ℚ :=
  (2530437606275 : ℚ) / 131129619554015168064

def SurrogateDiagonalTailChunk001Sub001Block055Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26997
    = surrogateDiagTailX0RatChunk001Sub001Block055Part004

theorem surrogateDiagonalTailChunk001Sub001Block055Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block055Part004CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block055Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block055Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block055Part004CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block055Part004SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block055Part004] using hcert

def TailChunk001Sub001Block055Part005SupportExplicit : Finset ℕ :=
  ([26998] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block055Part005 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block055Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26998
    = surrogateDiagTailX0RatChunk001Sub001Block055Part005

theorem surrogateDiagonalTailChunk001Sub001Block055Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block055Part005CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block055Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block055Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block055Part005CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block055Part005SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block055Part005] using hcert

def TailChunk001Sub001Block055Part006SupportExplicit : Finset ℕ :=
  ([27001] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block055Part006 : ℚ :=
  (5484373 : ℚ) / 4099362684595200

def SurrogateDiagonalTailChunk001Sub001Block055Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27001
    = surrogateDiagTailX0RatChunk001Sub001Block055Part006

theorem surrogateDiagonalTailChunk001Sub001Block055Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block055Part006CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block055Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block055Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block055Part006CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block055Part006SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block055Part006] using hcert

def TailChunk001Sub001Block055Part007SupportExplicit : Finset ℕ :=
  ([27002] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block055Part007 : ℚ :=
  (199715385475 : ℚ) / 69072956646525752448

def SurrogateDiagonalTailChunk001Sub001Block055Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27002
    = surrogateDiagTailX0RatChunk001Sub001Block055Part007

theorem surrogateDiagonalTailChunk001Sub001Block055Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block055Part007CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block055Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block055Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block055Part007CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block055Part007SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block055Part007] using hcert

def TailChunk001Sub001Block055Part008SupportExplicit : Finset ℕ :=
  ([27003] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block055Part008 : ℚ :=
  (405049997 : ℚ) / 20999399040000000

def SurrogateDiagonalTailChunk001Sub001Block055Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27003
    = surrogateDiagTailX0RatChunk001Sub001Block055Part008

theorem surrogateDiagonalTailChunk001Sub001Block055Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block055Part008CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block055Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block055Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block055Part008CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block055Part008SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block055Part008] using hcert

def TailChunk001Sub001Block055Part009SupportExplicit : Finset ℕ :=
  ([27005] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block055Part009 : ℚ :=
  (13989519279 : ℚ) / 2460140356352000000

def SurrogateDiagonalTailChunk001Sub001Block055Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27005
    = surrogateDiagTailX0RatChunk001Sub001Block055Part009

theorem surrogateDiagonalTailChunk001Sub001Block055Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block055Part009CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block055Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block055Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block055Part009CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block055Part009SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block055Part009] using hcert

def TailChunk001Sub001Block055Part010SupportExplicit : Finset ℕ :=
  ([27006] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block055Part010 : ℚ :=
  (316530514825 : ℚ) / 2202074277922386432

def SurrogateDiagonalTailChunk001Sub001Block055Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27006
    = surrogateDiagTailX0RatChunk001Sub001Block055Part010

theorem surrogateDiagonalTailChunk001Sub001Block055Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block055Part010CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block055Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block055Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block055Part010CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block055Part010SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block055Part010] using hcert

def TailChunk001Sub001Block055Part011SupportExplicit : Finset ℕ :=
  ([27007] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block055Part011 : ℚ :=
  (26529761875 : ℚ) / 315607115831616602112

def SurrogateDiagonalTailChunk001Sub001Block055Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27007
    = surrogateDiagTailX0RatChunk001Sub001Block055Part011

theorem surrogateDiagonalTailChunk001Sub001Block055Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block055Part011CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block055Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block055Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block055Part011CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block055Part011SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block055Part011] using hcert

def TailChunk001Sub001Block055Part012SupportExplicit : Finset ℕ :=
  ([27010] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block055Part012 : ℚ :=
  (554520806575 : ℚ) / 28893943085439909888

def SurrogateDiagonalTailChunk001Sub001Block055Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27010
    = surrogateDiagTailX0RatChunk001Sub001Block055Part012

theorem surrogateDiagonalTailChunk001Sub001Block055Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block055Part012CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block055Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block055Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block055Part012CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block055Part012SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block055Part012] using hcert

def TailChunk001Sub001Block055Part013SupportExplicit : Finset ℕ :=
  ([27011] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block055Part013 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block055Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27011
    = surrogateDiagTailX0RatChunk001Sub001Block055Part013

theorem surrogateDiagonalTailChunk001Sub001Block055Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block055Part013CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block055Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block055Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block055Part013CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block055Part013SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block055Part013] using hcert

def TailChunk001Sub001Block055Part014SupportExplicit : Finset ℕ :=
  ([27013] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block055Part014 : ℚ :=
  (624744263975 : ℚ) / 277022823850929291264

def SurrogateDiagonalTailChunk001Sub001Block055Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27013
    = surrogateDiagTailX0RatChunk001Sub001Block055Part014

theorem surrogateDiagonalTailChunk001Sub001Block055Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block055Part014CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block055Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block055Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block055Part014CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block055Part014SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block055Part014] using hcert

def TailChunk001Sub001Block055Part015SupportExplicit : Finset ℕ :=
  ([27014] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block055Part015 : ℚ :=
  (37798295375 : ℚ) / 6688038241443612672

def SurrogateDiagonalTailChunk001Sub001Block055Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27014
    = surrogateDiagTailX0RatChunk001Sub001Block055Part015

theorem surrogateDiagonalTailChunk001Sub001Block055Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block055Part015CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block055Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block055Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block055Part015CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block055Part015SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block055Part015] using hcert

def TailChunk001Sub001Block055Part016SupportExplicit : Finset ℕ :=
  ([27015] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block055Part016 : ℚ :=
  (85096768739 : ℚ) / 2150338461696000000

def SurrogateDiagonalTailChunk001Sub001Block055Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27015
    = surrogateDiagTailX0RatChunk001Sub001Block055Part016

theorem surrogateDiagonalTailChunk001Sub001Block055Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block055Part016CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block055Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block055Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block055Part016CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block055Part016SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block055Part016] using hcert

def TailChunk001Sub001Block055Part017SupportExplicit : Finset ℕ :=
  ([27017] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block055Part017 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block055Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27017
    = surrogateDiagTailX0RatChunk001Sub001Block055Part017

theorem surrogateDiagonalTailChunk001Sub001Block055Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block055Part017CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block055Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block055Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block055Part017CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block055Part017SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block055Part017] using hcert

def TailChunk001Sub001Block055Part018SupportExplicit : Finset ℕ :=
  ([27019] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block055Part018 : ℚ :=
  (9147387127 : ℚ) / 47998801116431155200

def SurrogateDiagonalTailChunk001Sub001Block055Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27019
    = surrogateDiagTailX0RatChunk001Sub001Block055Part018

theorem surrogateDiagonalTailChunk001Sub001Block055Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block055Part018CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block055Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block055Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block055Part018CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block055Part018SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block055Part018] using hcert

def TailChunk001Sub001Block055Part019SupportExplicit : Finset ℕ :=
  ([27021] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block055Part019 : ℚ :=
  (2534938606175 : ℚ) / 131596584129561029184

def SurrogateDiagonalTailChunk001Sub001Block055Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27021
    = surrogateDiagTailX0RatChunk001Sub001Block055Part019

theorem surrogateDiagonalTailChunk001Sub001Block055Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block055Part019CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block055Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block055Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block055Part019CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block055Part019SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block055Part019] using hcert

def TailChunk001Sub001Block055Part020SupportExplicit : Finset ℕ :=
  ([27022] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block055Part020 : ℚ :=
  (1567614425 : ℚ) / 1341539194173917184

def SurrogateDiagonalTailChunk001Sub001Block055Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27022
    = surrogateDiagTailX0RatChunk001Sub001Block055Part020

theorem surrogateDiagonalTailChunk001Sub001Block055Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block055Part020CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block055Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block055Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block055Part020CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block055Part020SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block055Part020] using hcert

def TailChunk001Sub001Block055Part021SupportExplicit : Finset ℕ :=
  ([27023] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block055Part021 : ℚ :=
  (235081793 : ℚ) / 1902863260968883200

def SurrogateDiagonalTailChunk001Sub001Block055Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27023
    = surrogateDiagTailX0RatChunk001Sub001Block055Part021

theorem surrogateDiagonalTailChunk001Sub001Block055Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block055Part021CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block055Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block055Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block055Part021CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block055Part021SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block055Part021] using hcert

def TailChunk001Sub001Block055Part022SupportExplicit : Finset ℕ :=
  ([27026] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block055Part022 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block055Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27026
    = surrogateDiagTailX0RatChunk001Sub001Block055Part022

theorem surrogateDiagonalTailChunk001Sub001Block055Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block055Part022CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block055Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block055Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block055Part022CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block055Part022SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block055Part022] using hcert

def TailChunk001Sub001Block055Part023SupportExplicit : Finset ℕ :=
  ([27029] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block055Part023 : ℚ :=
  (2037413639 : ℚ) / 25415689726521000000

def SurrogateDiagonalTailChunk001Sub001Block055Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27029
    = surrogateDiagTailX0RatChunk001Sub001Block055Part023

theorem surrogateDiagonalTailChunk001Sub001Block055Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block055Part023CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block055Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block055Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block055Part023CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block055Part023SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block055Part023] using hcert

def TailChunk001Sub001Block055Part024SupportExplicit : Finset ℕ :=
  ([27030] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block055Part024 : ℚ :=
  (653736470325 : ℚ) / 817953964354961408

def SurrogateDiagonalTailChunk001Sub001Block055Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27030
    = surrogateDiagTailX0RatChunk001Sub001Block055Part024

theorem surrogateDiagonalTailChunk001Sub001Block055Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block055Part024CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block055Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block055Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block055Part024CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block055Part024SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block055Part024] using hcert

def surrogateDiagonalTailChunk001Sub001Block055HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub001Block055Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block055Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block055Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block055Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block055Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block055Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block055Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block055Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block055Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block055Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub001Block055Head : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block055Part000
    + surrogateDiagTailX0RatChunk001Sub001Block055Part001
    + surrogateDiagTailX0RatChunk001Sub001Block055Part002
    + surrogateDiagTailX0RatChunk001Sub001Block055Part003
    + surrogateDiagTailX0RatChunk001Sub001Block055Part004
    + surrogateDiagTailX0RatChunk001Sub001Block055Part005
    + surrogateDiagTailX0RatChunk001Sub001Block055Part006
    + surrogateDiagTailX0RatChunk001Sub001Block055Part007
    + surrogateDiagTailX0RatChunk001Sub001Block055Part008
    + surrogateDiagTailX0RatChunk001Sub001Block055Part009

def surrogateDiagonalTailChunk001Sub001Block055MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub001Block055Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block055Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block055Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block055Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block055Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block055Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block055Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block055Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block055Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block055Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub001Block055Mid : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block055Part010
    + surrogateDiagTailX0RatChunk001Sub001Block055Part011
    + surrogateDiagTailX0RatChunk001Sub001Block055Part012
    + surrogateDiagTailX0RatChunk001Sub001Block055Part013
    + surrogateDiagTailX0RatChunk001Sub001Block055Part014
    + surrogateDiagTailX0RatChunk001Sub001Block055Part015
    + surrogateDiagTailX0RatChunk001Sub001Block055Part016
    + surrogateDiagTailX0RatChunk001Sub001Block055Part017
    + surrogateDiagTailX0RatChunk001Sub001Block055Part018
    + surrogateDiagTailX0RatChunk001Sub001Block055Part019

def surrogateDiagonalTailChunk001Sub001Block055TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub001Block055Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block055Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block055Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block055Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block055Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub001Block055Tail : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block055Part020
    + surrogateDiagTailX0RatChunk001Sub001Block055Part021
    + surrogateDiagTailX0RatChunk001Sub001Block055Part022
    + surrogateDiagTailX0RatChunk001Sub001Block055Part023
    + surrogateDiagTailX0RatChunk001Sub001Block055Part024

def surrogateDiagonalTailChunk001Sub001Block055Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk001Sub001Block055HeadSum X0
    + surrogateDiagonalTailChunk001Sub001Block055MidSum X0
    + surrogateDiagonalTailChunk001Sub001Block055TailSum X0

def surrogateDiagTailX0RatChunk001Sub001Block055 : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block055Part000
    + surrogateDiagTailX0RatChunk001Sub001Block055Part001
    + surrogateDiagTailX0RatChunk001Sub001Block055Part002
    + surrogateDiagTailX0RatChunk001Sub001Block055Part003
    + surrogateDiagTailX0RatChunk001Sub001Block055Part004
    + surrogateDiagTailX0RatChunk001Sub001Block055Part005
    + surrogateDiagTailX0RatChunk001Sub001Block055Part006
    + surrogateDiagTailX0RatChunk001Sub001Block055Part007
    + surrogateDiagTailX0RatChunk001Sub001Block055Part008
    + surrogateDiagTailX0RatChunk001Sub001Block055Part009
    + surrogateDiagTailX0RatChunk001Sub001Block055Part010
    + surrogateDiagTailX0RatChunk001Sub001Block055Part011
    + surrogateDiagTailX0RatChunk001Sub001Block055Part012
    + surrogateDiagTailX0RatChunk001Sub001Block055Part013
    + surrogateDiagTailX0RatChunk001Sub001Block055Part014
    + surrogateDiagTailX0RatChunk001Sub001Block055Part015
    + surrogateDiagTailX0RatChunk001Sub001Block055Part016
    + surrogateDiagTailX0RatChunk001Sub001Block055Part017
    + surrogateDiagTailX0RatChunk001Sub001Block055Part018
    + surrogateDiagTailX0RatChunk001Sub001Block055Part019
    + surrogateDiagTailX0RatChunk001Sub001Block055Part020
    + surrogateDiagTailX0RatChunk001Sub001Block055Part021
    + surrogateDiagTailX0RatChunk001Sub001Block055Part022
    + surrogateDiagTailX0RatChunk001Sub001Block055Part023
    + surrogateDiagTailX0RatChunk001Sub001Block055Part024

theorem surrogateDiagTailX0RatChunk001Sub001Block055_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk001Sub001Block055Head + surrogateDiagTailX0RatChunk001Sub001Block055Mid + surrogateDiagTailX0RatChunk001Sub001Block055Tail =
      surrogateDiagTailX0RatChunk001Sub001Block055 := by
  unfold surrogateDiagTailX0RatChunk001Sub001Block055Head surrogateDiagTailX0RatChunk001Sub001Block055Mid surrogateDiagTailX0RatChunk001Sub001Block055Tail surrogateDiagTailX0RatChunk001Sub001Block055
  ring

def SurrogateDiagonalTailChunk001Sub001Block055HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub001Block055HeadSum X0 = surrogateDiagTailX0RatChunk001Sub001Block055Head

def SurrogateDiagonalTailChunk001Sub001Block055MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub001Block055MidSum X0 = surrogateDiagTailX0RatChunk001Sub001Block055Mid

def SurrogateDiagonalTailChunk001Sub001Block055TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub001Block055TailSum X0 = surrogateDiagTailX0RatChunk001Sub001Block055Tail

theorem surrogateDiagonalTailChunk001Sub001Block055_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk001Sub001Block055HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk001Sub001Block055MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk001Sub001Block055TailCertificateAt X0) :
    surrogateDiagonalTailChunk001Sub001Block055Sum X0 = surrogateDiagTailX0RatChunk001Sub001Block055 := by
  unfold SurrogateDiagonalTailChunk001Sub001Block055HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk001Sub001Block055MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk001Sub001Block055TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk001Sub001Block055Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk001Sub001Block055_eq_head_add_mid_add_tail

/-- Block 056 covers tail-support indices [16400,16425) and q from 27031 to 27069. -/

def TailChunk001Sub001Block056Part000SupportExplicit : Finset ℕ :=
  ([27031] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block056Part000 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block056Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27031
    = surrogateDiagTailX0RatChunk001Sub001Block056Part000

theorem surrogateDiagonalTailChunk001Sub001Block056Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block056Part000CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block056Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block056Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block056Part000CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block056Part000SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block056Part000] using hcert

def TailChunk001Sub001Block056Part001SupportExplicit : Finset ℕ :=
  ([27033] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block056Part001 : ℚ :=
  (20297524849 : ℚ) / 1054644268437952320

def SurrogateDiagonalTailChunk001Sub001Block056Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27033
    = surrogateDiagTailX0RatChunk001Sub001Block056Part001

theorem surrogateDiagonalTailChunk001Sub001Block056Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block056Part001CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block056Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block056Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block056Part001CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block056Part001SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block056Part001] using hcert

def TailChunk001Sub001Block056Part002SupportExplicit : Finset ℕ :=
  ([27034] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block056Part002 : ℚ :=
  (5530958083 : ℚ) / 28102251346654050

def SurrogateDiagonalTailChunk001Sub001Block056Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27034
    = surrogateDiagTailX0RatChunk001Sub001Block056Part002

theorem surrogateDiagonalTailChunk001Sub001Block056Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block056Part002CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block056Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block056Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block056Part002CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block056Part002SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block056Part002] using hcert

def TailChunk001Sub001Block056Part003SupportExplicit : Finset ℕ :=
  ([27035] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block056Part003 : ℚ :=
  (1827802761625 : ℚ) / 546727588758234482688

def SurrogateDiagonalTailChunk001Sub001Block056Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27035
    = surrogateDiagTailX0RatChunk001Sub001Block056Part003

theorem surrogateDiagonalTailChunk001Sub001Block056Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block056Part003CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block056Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block056Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block056Part003CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block056Part003SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block056Part003] using hcert

def TailChunk001Sub001Block056Part004SupportExplicit : Finset ℕ :=
  ([27037] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block056Part004 : ℚ :=
  (384612012175 : ℚ) / 1073285506808542643328

def SurrogateDiagonalTailChunk001Sub001Block056Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27037
    = surrogateDiagTailX0RatChunk001Sub001Block056Part004

theorem surrogateDiagonalTailChunk001Sub001Block056Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block056Part004CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block056Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block056Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block056Part004CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block056Part004SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block056Part004] using hcert

def TailChunk001Sub001Block056Part005SupportExplicit : Finset ℕ :=
  ([27038] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block056Part005 : ℚ :=
  (388471452247 : ℚ) / 2274470547404851200

def SurrogateDiagonalTailChunk001Sub001Block056Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27038
    = surrogateDiagTailX0RatChunk001Sub001Block056Part005

theorem surrogateDiagonalTailChunk001Sub001Block056Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block056Part005CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block056Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block056Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block056Part005CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block056Part005SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block056Part005] using hcert

def TailChunk001Sub001Block056Part006SupportExplicit : Finset ℕ :=
  ([27039] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block056Part006 : ℚ :=
  (634579245275 : ℚ) / 32986906293189908736

def SurrogateDiagonalTailChunk001Sub001Block056Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27039
    = surrogateDiagTailX0RatChunk001Sub001Block056Part006

theorem surrogateDiagonalTailChunk001Sub001Block056Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block056Part006CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block056Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block056Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block056Part006CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block056Part006SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block056Part006] using hcert

def TailChunk001Sub001Block056Part007SupportExplicit : Finset ℕ :=
  ([27041] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block056Part007 : ℚ :=
  (934065192925 : ℚ) / 720909814703386854528

def SurrogateDiagonalTailChunk001Sub001Block056Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27041
    = surrogateDiagTailX0RatChunk001Sub001Block056Part007

theorem surrogateDiagonalTailChunk001Sub001Block056Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block056Part007CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block056Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block056Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block056Part007CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block056Part007SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block056Part007] using hcert

def TailChunk001Sub001Block056Part008SupportExplicit : Finset ℕ :=
  ([27042] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block056Part008 : ℚ :=
  (793331409575 : ℚ) / 2061681643324369296

def SurrogateDiagonalTailChunk001Sub001Block056Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27042
    = surrogateDiagTailX0RatChunk001Sub001Block056Part008

theorem surrogateDiagonalTailChunk001Sub001Block056Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block056Part008CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block056Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block056Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block056Part008CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block056Part008SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block056Part008] using hcert

def TailChunk001Sub001Block056Part009SupportExplicit : Finset ℕ :=
  ([27043] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block056Part009 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block056Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27043
    = surrogateDiagTailX0RatChunk001Sub001Block056Part009

theorem surrogateDiagonalTailChunk001Sub001Block056Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block056Part009CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block056Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block056Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block056Part009CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block056Part009SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block056Part009] using hcert

def TailChunk001Sub001Block056Part010SupportExplicit : Finset ℕ :=
  ([27046] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block056Part010 : ℚ :=
  (2857367640625 : ℚ) / 20899244843932563282

def SurrogateDiagonalTailChunk001Sub001Block056Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27046
    = surrogateDiagTailX0RatChunk001Sub001Block056Part010

theorem surrogateDiagonalTailChunk001Sub001Block056Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block056Part010CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block056Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block056Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block056Part010CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block056Part010SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block056Part010] using hcert

def TailChunk001Sub001Block056Part011SupportExplicit : Finset ℕ :=
  ([27047] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block056Part011 : ℚ :=
  (6496476575 : ℚ) / 6797409107205685248

def SurrogateDiagonalTailChunk001Sub001Block056Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27047
    = surrogateDiagTailX0RatChunk001Sub001Block056Part011

theorem surrogateDiagonalTailChunk001Sub001Block056Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block056Part011CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block056Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block056Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block056Part011CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block056Part011SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block056Part011] using hcert

def TailChunk001Sub001Block056Part012SupportExplicit : Finset ℕ :=
  ([27049] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block056Part012 : ℚ :=
  (947746367 : ℚ) / 1140944150441948100

def SurrogateDiagonalTailChunk001Sub001Block056Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27049
    = surrogateDiagTailX0RatChunk001Sub001Block056Part012

theorem surrogateDiagonalTailChunk001Sub001Block056Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block056Part012CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block056Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block056Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block056Part012CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block056Part012SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block056Part012] using hcert

def TailChunk001Sub001Block056Part013SupportExplicit : Finset ℕ :=
  ([27051] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block056Part013 : ℚ :=
  (3162729047 : ℚ) / 153723627409766400

def SurrogateDiagonalTailChunk001Sub001Block056Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27051
    = surrogateDiagTailX0RatChunk001Sub001Block056Part013

theorem surrogateDiagonalTailChunk001Sub001Block056Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block056Part013CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block056Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block056Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block056Part013CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block056Part013SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block056Part013] using hcert

def TailChunk001Sub001Block056Part014SupportExplicit : Finset ℕ :=
  ([27053] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block056Part014 : ℚ :=
  (21777813649 : ℚ) / 38820861980128051200

def SurrogateDiagonalTailChunk001Sub001Block056Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27053
    = surrogateDiagTailX0RatChunk001Sub001Block056Part014

theorem surrogateDiagonalTailChunk001Sub001Block056Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block056Part014CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block056Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block056Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block056Part014CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block056Part014SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block056Part014] using hcert

def TailChunk001Sub001Block056Part015SupportExplicit : Finset ℕ :=
  ([27055] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block056Part015 : ℚ :=
  (532733405275 : ℚ) / 73668365770172792832

def SurrogateDiagonalTailChunk001Sub001Block056Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27055
    = surrogateDiagTailX0RatChunk001Sub001Block056Part015

theorem surrogateDiagonalTailChunk001Sub001Block056Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block056Part015CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block056Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block056Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block056Part015CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block056Part015SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block056Part015] using hcert

def TailChunk001Sub001Block056Part016SupportExplicit : Finset ℕ :=
  ([27057] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block056Part016 : ℚ :=
  (2216609911 : ℚ) / 2271045013283020800

def SurrogateDiagonalTailChunk001Sub001Block056Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27057
    = surrogateDiagTailX0RatChunk001Sub001Block056Part016

theorem surrogateDiagonalTailChunk001Sub001Block056Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block056Part016CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block056Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block056Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block056Part016CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block056Part016SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block056Part016] using hcert

def TailChunk001Sub001Block056Part017SupportExplicit : Finset ℕ :=
  ([27058] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block056Part017 : ℚ :=
  (11104668369925 : ℚ) / 77865006930404439168

def SurrogateDiagonalTailChunk001Sub001Block056Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27058
    = surrogateDiagTailX0RatChunk001Sub001Block056Part017

theorem surrogateDiagonalTailChunk001Sub001Block056Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block056Part017CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block056Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block056Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block056Part017CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block056Part017SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block056Part017] using hcert

def TailChunk001Sub001Block056Part018SupportExplicit : Finset ℕ :=
  ([27059] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block056Part018 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block056Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27059
    = surrogateDiagTailX0RatChunk001Sub001Block056Part018

theorem surrogateDiagonalTailChunk001Sub001Block056Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block056Part018CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block056Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block056Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block056Part018CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block056Part018SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block056Part018] using hcert

def TailChunk001Sub001Block056Part019SupportExplicit : Finset ℕ :=
  ([27061] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block056Part019 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block056Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27061
    = surrogateDiagTailX0RatChunk001Sub001Block056Part019

theorem surrogateDiagonalTailChunk001Sub001Block056Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block056Part019CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block056Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block056Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block056Part019CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block056Part019SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block056Part019] using hcert

def TailChunk001Sub001Block056Part020SupportExplicit : Finset ℕ :=
  ([27062] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block056Part020 : ℚ :=
  (316709984125 : ℚ) / 1612509631660924416

def SurrogateDiagonalTailChunk001Sub001Block056Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27062
    = surrogateDiagTailX0RatChunk001Sub001Block056Part020

theorem surrogateDiagonalTailChunk001Sub001Block056Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block056Part020CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block056Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block056Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block056Part020CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block056Part020SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block056Part020] using hcert

def TailChunk001Sub001Block056Part021SupportExplicit : Finset ℕ :=
  ([27065] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block056Part021 : ℚ :=
  (1831859510875 : ℚ) / 549158836100001988608

def SurrogateDiagonalTailChunk001Sub001Block056Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27065
    = surrogateDiagTailX0RatChunk001Sub001Block056Part021

theorem surrogateDiagonalTailChunk001Sub001Block056Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block056Part021CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block056Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block056Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block056Part021CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block056Part021SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block056Part021] using hcert

def TailChunk001Sub001Block056Part022SupportExplicit : Finset ℕ :=
  ([27066] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block056Part022 : ℚ :=
  (4511656902175 : ℚ) / 11889845762566422528

def SurrogateDiagonalTailChunk001Sub001Block056Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27066
    = surrogateDiagTailX0RatChunk001Sub001Block056Part022

theorem surrogateDiagonalTailChunk001Sub001Block056Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block056Part022CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block056Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block056Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block056Part022CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block056Part022SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block056Part022] using hcert

def TailChunk001Sub001Block056Part023SupportExplicit : Finset ℕ :=
  ([27067] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block056Part023 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block056Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27067
    = surrogateDiagTailX0RatChunk001Sub001Block056Part023

theorem surrogateDiagonalTailChunk001Sub001Block056Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block056Part023CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block056Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block056Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block056Part023CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block056Part023SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block056Part023] using hcert

def TailChunk001Sub001Block056Part024SupportExplicit : Finset ℕ :=
  ([27069] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block056Part024 : ℚ :=
  (729661575775 : ℚ) / 142697148638833410048

def SurrogateDiagonalTailChunk001Sub001Block056Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27069
    = surrogateDiagTailX0RatChunk001Sub001Block056Part024

theorem surrogateDiagonalTailChunk001Sub001Block056Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block056Part024CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block056Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block056Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block056Part024CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block056Part024SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block056Part024] using hcert

def surrogateDiagonalTailChunk001Sub001Block056HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub001Block056Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block056Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block056Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block056Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block056Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block056Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block056Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block056Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block056Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block056Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub001Block056Head : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block056Part000
    + surrogateDiagTailX0RatChunk001Sub001Block056Part001
    + surrogateDiagTailX0RatChunk001Sub001Block056Part002
    + surrogateDiagTailX0RatChunk001Sub001Block056Part003
    + surrogateDiagTailX0RatChunk001Sub001Block056Part004
    + surrogateDiagTailX0RatChunk001Sub001Block056Part005
    + surrogateDiagTailX0RatChunk001Sub001Block056Part006
    + surrogateDiagTailX0RatChunk001Sub001Block056Part007
    + surrogateDiagTailX0RatChunk001Sub001Block056Part008
    + surrogateDiagTailX0RatChunk001Sub001Block056Part009

def surrogateDiagonalTailChunk001Sub001Block056MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub001Block056Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block056Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block056Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block056Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block056Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block056Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block056Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block056Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block056Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block056Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub001Block056Mid : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block056Part010
    + surrogateDiagTailX0RatChunk001Sub001Block056Part011
    + surrogateDiagTailX0RatChunk001Sub001Block056Part012
    + surrogateDiagTailX0RatChunk001Sub001Block056Part013
    + surrogateDiagTailX0RatChunk001Sub001Block056Part014
    + surrogateDiagTailX0RatChunk001Sub001Block056Part015
    + surrogateDiagTailX0RatChunk001Sub001Block056Part016
    + surrogateDiagTailX0RatChunk001Sub001Block056Part017
    + surrogateDiagTailX0RatChunk001Sub001Block056Part018
    + surrogateDiagTailX0RatChunk001Sub001Block056Part019

def surrogateDiagonalTailChunk001Sub001Block056TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub001Block056Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block056Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block056Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block056Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block056Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub001Block056Tail : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block056Part020
    + surrogateDiagTailX0RatChunk001Sub001Block056Part021
    + surrogateDiagTailX0RatChunk001Sub001Block056Part022
    + surrogateDiagTailX0RatChunk001Sub001Block056Part023
    + surrogateDiagTailX0RatChunk001Sub001Block056Part024

def surrogateDiagonalTailChunk001Sub001Block056Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk001Sub001Block056HeadSum X0
    + surrogateDiagonalTailChunk001Sub001Block056MidSum X0
    + surrogateDiagonalTailChunk001Sub001Block056TailSum X0

def surrogateDiagTailX0RatChunk001Sub001Block056 : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block056Part000
    + surrogateDiagTailX0RatChunk001Sub001Block056Part001
    + surrogateDiagTailX0RatChunk001Sub001Block056Part002
    + surrogateDiagTailX0RatChunk001Sub001Block056Part003
    + surrogateDiagTailX0RatChunk001Sub001Block056Part004
    + surrogateDiagTailX0RatChunk001Sub001Block056Part005
    + surrogateDiagTailX0RatChunk001Sub001Block056Part006
    + surrogateDiagTailX0RatChunk001Sub001Block056Part007
    + surrogateDiagTailX0RatChunk001Sub001Block056Part008
    + surrogateDiagTailX0RatChunk001Sub001Block056Part009
    + surrogateDiagTailX0RatChunk001Sub001Block056Part010
    + surrogateDiagTailX0RatChunk001Sub001Block056Part011
    + surrogateDiagTailX0RatChunk001Sub001Block056Part012
    + surrogateDiagTailX0RatChunk001Sub001Block056Part013
    + surrogateDiagTailX0RatChunk001Sub001Block056Part014
    + surrogateDiagTailX0RatChunk001Sub001Block056Part015
    + surrogateDiagTailX0RatChunk001Sub001Block056Part016
    + surrogateDiagTailX0RatChunk001Sub001Block056Part017
    + surrogateDiagTailX0RatChunk001Sub001Block056Part018
    + surrogateDiagTailX0RatChunk001Sub001Block056Part019
    + surrogateDiagTailX0RatChunk001Sub001Block056Part020
    + surrogateDiagTailX0RatChunk001Sub001Block056Part021
    + surrogateDiagTailX0RatChunk001Sub001Block056Part022
    + surrogateDiagTailX0RatChunk001Sub001Block056Part023
    + surrogateDiagTailX0RatChunk001Sub001Block056Part024

theorem surrogateDiagTailX0RatChunk001Sub001Block056_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk001Sub001Block056Head + surrogateDiagTailX0RatChunk001Sub001Block056Mid + surrogateDiagTailX0RatChunk001Sub001Block056Tail =
      surrogateDiagTailX0RatChunk001Sub001Block056 := by
  unfold surrogateDiagTailX0RatChunk001Sub001Block056Head surrogateDiagTailX0RatChunk001Sub001Block056Mid surrogateDiagTailX0RatChunk001Sub001Block056Tail surrogateDiagTailX0RatChunk001Sub001Block056
  ring

def SurrogateDiagonalTailChunk001Sub001Block056HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub001Block056HeadSum X0 = surrogateDiagTailX0RatChunk001Sub001Block056Head

def SurrogateDiagonalTailChunk001Sub001Block056MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub001Block056MidSum X0 = surrogateDiagTailX0RatChunk001Sub001Block056Mid

def SurrogateDiagonalTailChunk001Sub001Block056TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub001Block056TailSum X0 = surrogateDiagTailX0RatChunk001Sub001Block056Tail

theorem surrogateDiagonalTailChunk001Sub001Block056_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk001Sub001Block056HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk001Sub001Block056MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk001Sub001Block056TailCertificateAt X0) :
    surrogateDiagonalTailChunk001Sub001Block056Sum X0 = surrogateDiagTailX0RatChunk001Sub001Block056 := by
  unfold SurrogateDiagonalTailChunk001Sub001Block056HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk001Sub001Block056MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk001Sub001Block056TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk001Sub001Block056Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk001Sub001Block056_eq_head_add_mid_add_tail

/-- Block 057 covers tail-support indices [16425,16450) and q from 27070 to 27109. -/

def TailChunk001Sub001Block057Part000SupportExplicit : Finset ℕ :=
  ([27070] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block057Part000 : ℚ :=
  (7782070884025 : ℚ) / 34322427256250124288

def SurrogateDiagonalTailChunk001Sub001Block057Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27070
    = surrogateDiagTailX0RatChunk001Sub001Block057Part000

theorem surrogateDiagonalTailChunk001Sub001Block057Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block057Part000CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block057Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block057Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block057Part000CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block057Part000SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block057Part000] using hcert

def TailChunk001Sub001Block057Part001SupportExplicit : Finset ℕ :=
  ([27071] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block057Part001 : ℚ :=
  (11281474741 : ℚ) / 7395048782557708800

def SurrogateDiagonalTailChunk001Sub001Block057Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27071
    = surrogateDiagTailX0RatChunk001Sub001Block057Part001

theorem surrogateDiagonalTailChunk001Sub001Block057Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block057Part001CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block057Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block057Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block057Part001CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block057Part001SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block057Part001] using hcert

def TailChunk001Sub001Block057Part002SupportExplicit : Finset ℕ :=
  ([27073] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block057Part002 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block057Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27073
    = surrogateDiagTailX0RatChunk001Sub001Block057Part002

theorem surrogateDiagonalTailChunk001Sub001Block057Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block057Part002CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block057Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block057Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block057Part002CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block057Part002SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block057Part002] using hcert

def TailChunk001Sub001Block057Part003SupportExplicit : Finset ℕ :=
  ([27074] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block057Part003 : ℚ :=
  (2863287015625 : ℚ) / 20985931470214397952

def SurrogateDiagonalTailChunk001Sub001Block057Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27074
    = surrogateDiagTailX0RatChunk001Sub001Block057Part003

theorem surrogateDiagonalTailChunk001Sub001Block057Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block057Part003CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block057Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block057Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block057Part003CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block057Part003SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block057Part003] using hcert

def TailChunk001Sub001Block057Part004SupportExplicit : Finset ℕ :=
  ([27077] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block057Part004 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block057Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27077
    = surrogateDiagTailX0RatChunk001Sub001Block057Part004

theorem surrogateDiagonalTailChunk001Sub001Block057Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block057Part004CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block057Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block057Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block057Part004CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block057Part004SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block057Part004] using hcert

def TailChunk001Sub001Block057Part005SupportExplicit : Finset ℕ :=
  ([27078] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block057Part005 : ℚ :=
  (5090160548725 : ℚ) / 16581476717206437888

def SurrogateDiagonalTailChunk001Sub001Block057Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27078
    = surrogateDiagTailX0RatChunk001Sub001Block057Part005

theorem surrogateDiagonalTailChunk001Sub001Block057Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block057Part005CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block057Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block057Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block057Part005CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block057Part005SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block057Part005] using hcert

def TailChunk001Sub001Block057Part006SupportExplicit : Finset ℕ :=
  ([27079] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block057Part006 : ℚ :=
  (6734390525 : ℚ) / 12027897678468630528

def SurrogateDiagonalTailChunk001Sub001Block057Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27079
    = surrogateDiagTailX0RatChunk001Sub001Block057Part006

theorem surrogateDiagonalTailChunk001Sub001Block057Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block057Part006CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block057Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block057Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block057Part006CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block057Part006SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block057Part006] using hcert

def TailChunk001Sub001Block057Part007SupportExplicit : Finset ℕ :=
  ([27082] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block057Part007 : ℚ :=
  (129912484979 : ℚ) / 763108061094000000

def SurrogateDiagonalTailChunk001Sub001Block057Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27082
    = surrogateDiagTailX0RatChunk001Sub001Block057Part007

theorem surrogateDiagonalTailChunk001Sub001Block057Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block057Part007CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block057Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block057Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block057Part007CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block057Part007SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block057Part007] using hcert

def TailChunk001Sub001Block057Part008SupportExplicit : Finset ℕ :=
  ([27083] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block057Part008 : ℚ :=
  (42758310125 : ℚ) / 24490738024194244608

def SurrogateDiagonalTailChunk001Sub001Block057Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27083
    = surrogateDiagTailX0RatChunk001Sub001Block057Part008

theorem surrogateDiagonalTailChunk001Sub001Block057Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block057Part008CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block057Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block057Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block057Part008CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block057Part008SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block057Part008] using hcert

def TailChunk001Sub001Block057Part009SupportExplicit : Finset ℕ :=
  ([27085] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block057Part009 : ℚ :=
  (611522170125 : ℚ) / 183594722119252443136

def SurrogateDiagonalTailChunk001Sub001Block057Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27085
    = surrogateDiagTailX0RatChunk001Sub001Block057Part009

theorem surrogateDiagonalTailChunk001Sub001Block057Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block057Part009CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block057Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block057Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block057Part009CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block057Part009SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block057Part009] using hcert

def TailChunk001Sub001Block057Part010SupportExplicit : Finset ℕ :=
  ([27086] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block057Part010 : ℚ :=
  (10786317702325 : ℚ) / 72477407613237086208

def SurrogateDiagonalTailChunk001Sub001Block057Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27086
    = surrogateDiagTailX0RatChunk001Sub001Block057Part010

theorem surrogateDiagonalTailChunk001Sub001Block057Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block057Part010CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block057Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block057Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block057Part010CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block057Part010SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block057Part010] using hcert

def TailChunk001Sub001Block057Part011SupportExplicit : Finset ℕ :=
  ([27087] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block057Part011 : ℚ :=
  (125025 : ℚ) / 53144238519093248

def SurrogateDiagonalTailChunk001Sub001Block057Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27087
    = surrogateDiagTailX0RatChunk001Sub001Block057Part011

theorem surrogateDiagonalTailChunk001Sub001Block057Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block057Part011CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block057Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block057Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block057Part011CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block057Part011SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block057Part011] using hcert

def TailChunk001Sub001Block057Part012SupportExplicit : Finset ℕ :=
  ([27089] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block057Part012 : ℚ :=
  (112752687025 : ℚ) / 1275359763379923727488

def SurrogateDiagonalTailChunk001Sub001Block057Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27089
    = surrogateDiagTailX0RatChunk001Sub001Block057Part012

theorem surrogateDiagonalTailChunk001Sub001Block057Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block057Part012CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block057Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block057Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block057Part012CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block057Part012SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block057Part012] using hcert

def TailChunk001Sub001Block057Part013SupportExplicit : Finset ℕ :=
  ([27091] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block057Part013 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block057Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27091
    = surrogateDiagTailX0RatChunk001Sub001Block057Part013

theorem surrogateDiagonalTailChunk001Sub001Block057Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block057Part013CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block057Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block057Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block057Part013CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block057Part013SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block057Part013] using hcert

def TailChunk001Sub001Block057Part014SupportExplicit : Finset ℕ :=
  ([27093] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block057Part014 : ℚ :=
  (20426531929 : ℚ) / 7235394949632000000

def SurrogateDiagonalTailChunk001Sub001Block057Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27093
    = surrogateDiagTailX0RatChunk001Sub001Block057Part014

theorem surrogateDiagonalTailChunk001Sub001Block057Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block057Part014CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block057Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block057Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block057Part014CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block057Part014SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block057Part014] using hcert

def TailChunk001Sub001Block057Part015SupportExplicit : Finset ℕ :=
  ([27094] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block057Part015 : ℚ :=
  (369939986563 : ℚ) / 1992290264713267200

def SurrogateDiagonalTailChunk001Sub001Block057Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27094
    = surrogateDiagTailX0RatChunk001Sub001Block057Part015

theorem surrogateDiagonalTailChunk001Sub001Block057Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block057Part015CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block057Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block057Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block057Part015CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block057Part015SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block057Part015] using hcert

def TailChunk001Sub001Block057Part016SupportExplicit : Finset ℕ :=
  ([27095] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block057Part016 : ℚ :=
  (1835920760125 : ℚ) / 551598183091455510528

def SurrogateDiagonalTailChunk001Sub001Block057Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27095
    = surrogateDiagTailX0RatChunk001Sub001Block057Part016

theorem surrogateDiagonalTailChunk001Sub001Block057Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block057Part016CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block057Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block057Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block057Part016CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block057Part016SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block057Part016] using hcert

def TailChunk001Sub001Block057Part017SupportExplicit : Finset ℕ :=
  ([27098] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block057Part017 : ℚ :=
  (10341949632325 : ℚ) / 65789874881018462208

def SurrogateDiagonalTailChunk001Sub001Block057Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27098
    = surrogateDiagTailX0RatChunk001Sub001Block057Part017

theorem surrogateDiagonalTailChunk001Sub001Block057Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block057Part017CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block057Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block057Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block057Part017CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block057Part017SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block057Part017] using hcert

def TailChunk001Sub001Block057Part018SupportExplicit : Finset ℕ :=
  ([27101] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block057Part018 : ℚ :=
  (2028523861 : ℚ) / 12146259806208000000

def SurrogateDiagonalTailChunk001Sub001Block057Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27101
    = surrogateDiagTailX0RatChunk001Sub001Block057Part018

theorem surrogateDiagonalTailChunk001Sub001Block057Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block057Part018CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block057Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block057Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block057Part018CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block057Part018SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block057Part018] using hcert

def TailChunk001Sub001Block057Part019SupportExplicit : Finset ℕ :=
  ([27102] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block057Part019 : ℚ :=
  (5099188548325 : ℚ) / 16640354517163788288

def SurrogateDiagonalTailChunk001Sub001Block057Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27102
    = surrogateDiagTailX0RatChunk001Sub001Block057Part019

theorem surrogateDiagonalTailChunk001Sub001Block057Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block057Part019CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block057Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block057Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block057Part019CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block057Part019SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block057Part019] using hcert

def TailChunk001Sub001Block057Part020SupportExplicit : Finset ℕ :=
  ([27103] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block057Part020 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block057Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27103
    = surrogateDiagTailX0RatChunk001Sub001Block057Part020

theorem surrogateDiagonalTailChunk001Sub001Block057Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block057Part020CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block057Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block057Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block057Part020CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block057Part020SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block057Part020] using hcert

def TailChunk001Sub001Block057Part021SupportExplicit : Finset ℕ :=
  ([27105] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block057Part021 : ℚ :=
  (1422533815375 : ℚ) / 77024366778812203008

def SurrogateDiagonalTailChunk001Sub001Block057Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27105
    = surrogateDiagTailX0RatChunk001Sub001Block057Part021

theorem surrogateDiagonalTailChunk001Sub001Block057Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block057Part021CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block057Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block057Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block057Part021CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block057Part021SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block057Part021] using hcert

def TailChunk001Sub001Block057Part022SupportExplicit : Finset ℕ :=
  ([27106] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block057Part022 : ℚ :=
  (2870059515625 : ℚ) / 21085331800705277952

def SurrogateDiagonalTailChunk001Sub001Block057Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27106
    = surrogateDiagTailX0RatChunk001Sub001Block057Part022

theorem surrogateDiagonalTailChunk001Sub001Block057Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block057Part022CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block057Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block057Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block057Part022CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block057Part022SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block057Part022] using hcert

def TailChunk001Sub001Block057Part023SupportExplicit : Finset ℕ :=
  ([27107] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block057Part023 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block057Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27107
    = surrogateDiagTailX0RatChunk001Sub001Block057Part023

theorem surrogateDiagonalTailChunk001Sub001Block057Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block057Part023CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block057Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block057Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block057Part023CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block057Part023SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block057Part023] using hcert

def TailChunk001Sub001Block057Part024SupportExplicit : Finset ℕ :=
  ([27109] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block057Part024 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block057Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27109
    = surrogateDiagTailX0RatChunk001Sub001Block057Part024

theorem surrogateDiagonalTailChunk001Sub001Block057Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block057Part024CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block057Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block057Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block057Part024CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block057Part024SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block057Part024] using hcert

def surrogateDiagonalTailChunk001Sub001Block057HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub001Block057Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block057Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block057Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block057Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block057Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block057Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block057Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block057Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block057Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block057Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub001Block057Head : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block057Part000
    + surrogateDiagTailX0RatChunk001Sub001Block057Part001
    + surrogateDiagTailX0RatChunk001Sub001Block057Part002
    + surrogateDiagTailX0RatChunk001Sub001Block057Part003
    + surrogateDiagTailX0RatChunk001Sub001Block057Part004
    + surrogateDiagTailX0RatChunk001Sub001Block057Part005
    + surrogateDiagTailX0RatChunk001Sub001Block057Part006
    + surrogateDiagTailX0RatChunk001Sub001Block057Part007
    + surrogateDiagTailX0RatChunk001Sub001Block057Part008
    + surrogateDiagTailX0RatChunk001Sub001Block057Part009

def surrogateDiagonalTailChunk001Sub001Block057MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub001Block057Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block057Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block057Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block057Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block057Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block057Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block057Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block057Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block057Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block057Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub001Block057Mid : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block057Part010
    + surrogateDiagTailX0RatChunk001Sub001Block057Part011
    + surrogateDiagTailX0RatChunk001Sub001Block057Part012
    + surrogateDiagTailX0RatChunk001Sub001Block057Part013
    + surrogateDiagTailX0RatChunk001Sub001Block057Part014
    + surrogateDiagTailX0RatChunk001Sub001Block057Part015
    + surrogateDiagTailX0RatChunk001Sub001Block057Part016
    + surrogateDiagTailX0RatChunk001Sub001Block057Part017
    + surrogateDiagTailX0RatChunk001Sub001Block057Part018
    + surrogateDiagTailX0RatChunk001Sub001Block057Part019

def surrogateDiagonalTailChunk001Sub001Block057TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub001Block057Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block057Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block057Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block057Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block057Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub001Block057Tail : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block057Part020
    + surrogateDiagTailX0RatChunk001Sub001Block057Part021
    + surrogateDiagTailX0RatChunk001Sub001Block057Part022
    + surrogateDiagTailX0RatChunk001Sub001Block057Part023
    + surrogateDiagTailX0RatChunk001Sub001Block057Part024

def surrogateDiagonalTailChunk001Sub001Block057Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk001Sub001Block057HeadSum X0
    + surrogateDiagonalTailChunk001Sub001Block057MidSum X0
    + surrogateDiagonalTailChunk001Sub001Block057TailSum X0

def surrogateDiagTailX0RatChunk001Sub001Block057 : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block057Part000
    + surrogateDiagTailX0RatChunk001Sub001Block057Part001
    + surrogateDiagTailX0RatChunk001Sub001Block057Part002
    + surrogateDiagTailX0RatChunk001Sub001Block057Part003
    + surrogateDiagTailX0RatChunk001Sub001Block057Part004
    + surrogateDiagTailX0RatChunk001Sub001Block057Part005
    + surrogateDiagTailX0RatChunk001Sub001Block057Part006
    + surrogateDiagTailX0RatChunk001Sub001Block057Part007
    + surrogateDiagTailX0RatChunk001Sub001Block057Part008
    + surrogateDiagTailX0RatChunk001Sub001Block057Part009
    + surrogateDiagTailX0RatChunk001Sub001Block057Part010
    + surrogateDiagTailX0RatChunk001Sub001Block057Part011
    + surrogateDiagTailX0RatChunk001Sub001Block057Part012
    + surrogateDiagTailX0RatChunk001Sub001Block057Part013
    + surrogateDiagTailX0RatChunk001Sub001Block057Part014
    + surrogateDiagTailX0RatChunk001Sub001Block057Part015
    + surrogateDiagTailX0RatChunk001Sub001Block057Part016
    + surrogateDiagTailX0RatChunk001Sub001Block057Part017
    + surrogateDiagTailX0RatChunk001Sub001Block057Part018
    + surrogateDiagTailX0RatChunk001Sub001Block057Part019
    + surrogateDiagTailX0RatChunk001Sub001Block057Part020
    + surrogateDiagTailX0RatChunk001Sub001Block057Part021
    + surrogateDiagTailX0RatChunk001Sub001Block057Part022
    + surrogateDiagTailX0RatChunk001Sub001Block057Part023
    + surrogateDiagTailX0RatChunk001Sub001Block057Part024

theorem surrogateDiagTailX0RatChunk001Sub001Block057_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk001Sub001Block057Head + surrogateDiagTailX0RatChunk001Sub001Block057Mid + surrogateDiagTailX0RatChunk001Sub001Block057Tail =
      surrogateDiagTailX0RatChunk001Sub001Block057 := by
  unfold surrogateDiagTailX0RatChunk001Sub001Block057Head surrogateDiagTailX0RatChunk001Sub001Block057Mid surrogateDiagTailX0RatChunk001Sub001Block057Tail surrogateDiagTailX0RatChunk001Sub001Block057
  ring

def SurrogateDiagonalTailChunk001Sub001Block057HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub001Block057HeadSum X0 = surrogateDiagTailX0RatChunk001Sub001Block057Head

def SurrogateDiagonalTailChunk001Sub001Block057MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub001Block057MidSum X0 = surrogateDiagTailX0RatChunk001Sub001Block057Mid

def SurrogateDiagonalTailChunk001Sub001Block057TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub001Block057TailSum X0 = surrogateDiagTailX0RatChunk001Sub001Block057Tail

theorem surrogateDiagonalTailChunk001Sub001Block057_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk001Sub001Block057HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk001Sub001Block057MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk001Sub001Block057TailCertificateAt X0) :
    surrogateDiagonalTailChunk001Sub001Block057Sum X0 = surrogateDiagTailX0RatChunk001Sub001Block057 := by
  unfold SurrogateDiagonalTailChunk001Sub001Block057HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk001Sub001Block057MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk001Sub001Block057TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk001Sub001Block057Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk001Sub001Block057_eq_head_add_mid_add_tail

/-- Block 058 covers tail-support indices [16450,16475) and q from 27110 to 27149. -/

def TailChunk001Sub001Block058Part000SupportExplicit : Finset ℕ :=
  ([27110] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block058Part000 : ℚ :=
  (312203642029 : ℚ) / 1381032754456627200

def SurrogateDiagonalTailChunk001Sub001Block058Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27110
    = surrogateDiagTailX0RatChunk001Sub001Block058Part000

theorem surrogateDiagonalTailChunk001Sub001Block058Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block058Part000CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block058Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block058Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block058Part000CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block058Part000SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block058Part000] using hcert

def TailChunk001Sub001Block058Part001SupportExplicit : Finset ℕ :=
  ([27111] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block058Part001 : ℚ :=
  (29276708497 : ℚ) / 5743421314988083200

def SurrogateDiagonalTailChunk001Sub001Block058Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27111
    = surrogateDiagTailX0RatChunk001Sub001Block058Part001

theorem surrogateDiagonalTailChunk001Sub001Block058Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block058Part001CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block058Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block058Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block058Part001CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block058Part001SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block058Part001] using hcert

def TailChunk001Sub001Block058Part002SupportExplicit : Finset ℕ :=
  ([27113] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block058Part002 : ℚ :=
  (386747158075 : ℚ) / 1085412906371084969088

def SurrogateDiagonalTailChunk001Sub001Block058Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27113
    = surrogateDiagTailX0RatChunk001Sub001Block058Part002

theorem surrogateDiagonalTailChunk001Sub001Block058Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block058Part002CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block058Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block058Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block058Part002CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block058Part002SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block058Part002] using hcert

def TailChunk001Sub001Block058Part003SupportExplicit : Finset ℕ :=
  ([27114] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block058Part003 : ℚ :=
  (5103705548125 : ℚ) / 16669852147007687808

def SurrogateDiagonalTailChunk001Sub001Block058Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27114
    = surrogateDiagTailX0RatChunk001Sub001Block058Part003

theorem surrogateDiagonalTailChunk001Sub001Block058Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block058Part003CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block058Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block058Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block058Part003CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block058Part003SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block058Part003] using hcert

def TailChunk001Sub001Block058Part004SupportExplicit : Finset ℕ :=
  ([27115] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block058Part004 : ℚ :=
  (11397267899 : ℚ) / 1289284865123942400

def SurrogateDiagonalTailChunk001Sub001Block058Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27115
    = surrogateDiagTailX0RatChunk001Sub001Block058Part004

theorem surrogateDiagonalTailChunk001Sub001Block058Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block058Part004CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block058Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block058Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block058Part004CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block058Part004SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block058Part004] using hcert

def TailChunk001Sub001Block058Part005SupportExplicit : Finset ℕ :=
  ([27118] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block058Part005 : ℚ :=
  (3776025335825 : ℚ) / 16120321926842548224

def SurrogateDiagonalTailChunk001Sub001Block058Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27118
    = surrogateDiagTailX0RatChunk001Sub001Block058Part005

theorem surrogateDiagonalTailChunk001Sub001Block058Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block058Part005CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block058Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block058Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block058Part005CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block058Part005SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block058Part005] using hcert

def TailChunk001Sub001Block058Part006SupportExplicit : Finset ℕ :=
  ([27119] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block058Part006 : ℚ :=
  (200653436125 : ℚ) / 1232389868460995248128

def SurrogateDiagonalTailChunk001Sub001Block058Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27119
    = surrogateDiagTailX0RatChunk001Sub001Block058Part006

theorem surrogateDiagonalTailChunk001Sub001Block058Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block058Part006CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block058Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block058Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block058Part006CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block058Part006SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block058Part006] using hcert

def TailChunk001Sub001Block058Part007SupportExplicit : Finset ℕ :=
  ([27121] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block058Part007 : ℚ :=
  (145386875 : ℚ) / 827034567689650176

def SurrogateDiagonalTailChunk001Sub001Block058Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27121
    = surrogateDiagTailX0RatChunk001Sub001Block058Part007

theorem surrogateDiagonalTailChunk001Sub001Block058Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block058Part007CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block058Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block058Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block058Part007CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block058Part007SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block058Part007] using hcert

def TailChunk001Sub001Block058Part008SupportExplicit : Finset ℕ :=
  ([27122] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block058Part008 : ℚ :=
  (89078125763 : ℚ) / 625926602288400000

def SurrogateDiagonalTailChunk001Sub001Block058Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27122
    = surrogateDiagTailX0RatChunk001Sub001Block058Part008

theorem surrogateDiagonalTailChunk001Sub001Block058Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block058Part008CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block058Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block058Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block058Part008CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block058Part008SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block058Part008] using hcert

def TailChunk001Sub001Block058Part009SupportExplicit : Finset ℕ :=
  ([27123] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block058Part009 : ℚ :=
  (5001 : ℚ) / 2137094370099200

def SurrogateDiagonalTailChunk001Sub001Block058Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27123
    = surrogateDiagTailX0RatChunk001Sub001Block058Part009

theorem surrogateDiagonalTailChunk001Sub001Block058Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block058Part009CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block058Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block058Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block058Part009CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block058Part009SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block058Part009] using hcert

def TailChunk001Sub001Block058Part010SupportExplicit : Finset ℕ :=
  ([27127] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block058Part010 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block058Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27127
    = surrogateDiagTailX0RatChunk001Sub001Block058Part010

theorem surrogateDiagonalTailChunk001Sub001Block058Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block058Part010CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block058Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block058Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block058Part010CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block058Part010SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block058Part010] using hcert

def TailChunk001Sub001Block058Part011SupportExplicit : Finset ℕ :=
  ([27129] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block058Part011 : ℚ :=
  (41675 : ℚ) / 17824885264745856

def SurrogateDiagonalTailChunk001Sub001Block058Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27129
    = surrogateDiagTailX0RatChunk001Sub001Block058Part011

theorem surrogateDiagonalTailChunk001Sub001Block058Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block058Part011CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block058Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block058Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block058Part011CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block058Part011SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block058Part011] using hcert

def TailChunk001Sub001Block058Part012SupportExplicit : Finset ℕ :=
  ([27130] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block058Part012 : ℚ :=
  (7816613885275 : ℚ) / 34627852981366161408

def SurrogateDiagonalTailChunk001Sub001Block058Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27130
    = surrogateDiagTailX0RatChunk001Sub001Block058Part012

theorem surrogateDiagonalTailChunk001Sub001Block058Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block058Part012CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block058Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block058Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block058Part012CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block058Part012SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block058Part012] using hcert

def TailChunk001Sub001Block058Part013SupportExplicit : Finset ℕ :=
  ([27131] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block058Part013 : ℚ :=
  (547569214525 : ℚ) / 981768422616260364288

def SurrogateDiagonalTailChunk001Sub001Block058Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27131
    = surrogateDiagTailX0RatChunk001Sub001Block058Part013

theorem surrogateDiagonalTailChunk001Sub001Block058Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block058Part013CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block058Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block058Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block058Part013CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block058Part013SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block058Part013] using hcert

def TailChunk001Sub001Block058Part014SupportExplicit : Finset ℕ :=
  ([27133] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block058Part014 : ℚ :=
  (845496019 : ℚ) / 4902822941700237120

def SurrogateDiagonalTailChunk001Sub001Block058Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27133
    = surrogateDiagTailX0RatChunk001Sub001Block058Part014

theorem surrogateDiagonalTailChunk001Sub001Block058Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block058Part014CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block058Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block058Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block058Part014CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block058Part014SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block058Part014] using hcert

def TailChunk001Sub001Block058Part015SupportExplicit : Finset ℕ :=
  ([27134] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block058Part015 : ℚ :=
  (2875992015625 : ℚ) / 21172596378640429842

def SurrogateDiagonalTailChunk001Sub001Block058Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27134
    = surrogateDiagTailX0RatChunk001Sub001Block058Part015

theorem surrogateDiagonalTailChunk001Sub001Block058Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block058Part015CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block058Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block058Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block058Part015CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block058Part015SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block058Part015] using hcert

def TailChunk001Sub001Block058Part016SupportExplicit : Finset ℕ :=
  ([27137] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block058Part016 : ℚ :=
  (317966711 : ℚ) / 385290149874950700

def SurrogateDiagonalTailChunk001Sub001Block058Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27137
    = surrogateDiagTailX0RatChunk001Sub001Block058Part016

theorem surrogateDiagonalTailChunk001Sub001Block058Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block058Part016CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block058Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block058Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block058Part016CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block058Part016SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block058Part016] using hcert

def TailChunk001Sub001Block058Part017SupportExplicit : Finset ℕ :=
  ([27138] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block058Part017 : ℚ :=
  (5112745547725 : ℚ) / 16728965039913426048

def SurrogateDiagonalTailChunk001Sub001Block058Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27138
    = surrogateDiagTailX0RatChunk001Sub001Block058Part017

theorem surrogateDiagonalTailChunk001Sub001Block058Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block058Part017CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block058Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block058Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block058Part017CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block058Part017SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block058Part017] using hcert

def TailChunk001Sub001Block058Part018SupportExplicit : Finset ℕ :=
  ([27139] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block058Part018 : ℚ :=
  (939710648375 : ℚ) / 365710086220314829824

def SurrogateDiagonalTailChunk001Sub001Block058Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27139
    = surrogateDiagTailX0RatChunk001Sub001Block058Part018

theorem surrogateDiagonalTailChunk001Sub001Block058Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block058Part018CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block058Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block058Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block058Part018CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block058Part018SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block058Part018] using hcert

def TailChunk001Sub001Block058Part019SupportExplicit : Finset ℕ :=
  ([27141] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block058Part019 : ℚ :=
  (117404265175 : ℚ) / 246091873755352301568

def SurrogateDiagonalTailChunk001Sub001Block058Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27141
    = surrogateDiagTailX0RatChunk001Sub001Block058Part019

theorem surrogateDiagonalTailChunk001Sub001Block058Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block058Part019CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block058Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block058Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block058Part019CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block058Part019SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block058Part019] using hcert

def TailChunk001Sub001Block058Part020SupportExplicit : Finset ℕ :=
  ([27142] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block058Part020 : ℚ :=
  (21997931051 : ℚ) / 151828247577600000

def SurrogateDiagonalTailChunk001Sub001Block058Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27142
    = surrogateDiagTailX0RatChunk001Sub001Block058Part020

theorem surrogateDiagonalTailChunk001Sub001Block058Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block058Part020CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block058Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block058Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block058Part020CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block058Part020SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block058Part020] using hcert

def TailChunk001Sub001Block058Part021SupportExplicit : Finset ℕ :=
  ([27143] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block058Part021 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block058Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27143
    = surrogateDiagTailX0RatChunk001Sub001Block058Part021

theorem surrogateDiagonalTailChunk001Sub001Block058Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block058Part021CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block058Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block058Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block058Part021CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block058Part021SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block058Part021] using hcert

def TailChunk001Sub001Block058Part022SupportExplicit : Finset ℕ :=
  ([27145] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block058Part022 : ℚ :=
  (9614311517 : ℚ) / 2487554008311398400

def SurrogateDiagonalTailChunk001Sub001Block058Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27145
    = surrogateDiagTailX0RatChunk001Sub001Block058Part022

theorem surrogateDiagonalTailChunk001Sub001Block058Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block058Part022CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block058Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block058Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block058Part022CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block058Part022SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block058Part022] using hcert

def TailChunk001Sub001Block058Part023SupportExplicit : Finset ℕ :=
  ([27147] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block058Part023 : ℚ :=
  (41675 : ℚ) / 17872244614987776

def SurrogateDiagonalTailChunk001Sub001Block058Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27147
    = surrogateDiagTailX0RatChunk001Sub001Block058Part023

theorem surrogateDiagonalTailChunk001Sub001Block058Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block058Part023CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block058Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block058Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block058Part023CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block058Part023SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block058Part023] using hcert

def TailChunk001Sub001Block058Part024SupportExplicit : Finset ℕ :=
  ([27149] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block058Part024 : ℚ :=
  (17092225 : ℚ) / 37672095129403392

def SurrogateDiagonalTailChunk001Sub001Block058Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27149
    = surrogateDiagTailX0RatChunk001Sub001Block058Part024

theorem surrogateDiagonalTailChunk001Sub001Block058Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block058Part024CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block058Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block058Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block058Part024CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block058Part024SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block058Part024] using hcert

def surrogateDiagonalTailChunk001Sub001Block058HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub001Block058Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block058Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block058Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block058Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block058Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block058Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block058Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block058Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block058Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block058Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub001Block058Head : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block058Part000
    + surrogateDiagTailX0RatChunk001Sub001Block058Part001
    + surrogateDiagTailX0RatChunk001Sub001Block058Part002
    + surrogateDiagTailX0RatChunk001Sub001Block058Part003
    + surrogateDiagTailX0RatChunk001Sub001Block058Part004
    + surrogateDiagTailX0RatChunk001Sub001Block058Part005
    + surrogateDiagTailX0RatChunk001Sub001Block058Part006
    + surrogateDiagTailX0RatChunk001Sub001Block058Part007
    + surrogateDiagTailX0RatChunk001Sub001Block058Part008
    + surrogateDiagTailX0RatChunk001Sub001Block058Part009

def surrogateDiagonalTailChunk001Sub001Block058MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub001Block058Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block058Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block058Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block058Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block058Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block058Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block058Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block058Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block058Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block058Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub001Block058Mid : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block058Part010
    + surrogateDiagTailX0RatChunk001Sub001Block058Part011
    + surrogateDiagTailX0RatChunk001Sub001Block058Part012
    + surrogateDiagTailX0RatChunk001Sub001Block058Part013
    + surrogateDiagTailX0RatChunk001Sub001Block058Part014
    + surrogateDiagTailX0RatChunk001Sub001Block058Part015
    + surrogateDiagTailX0RatChunk001Sub001Block058Part016
    + surrogateDiagTailX0RatChunk001Sub001Block058Part017
    + surrogateDiagTailX0RatChunk001Sub001Block058Part018
    + surrogateDiagTailX0RatChunk001Sub001Block058Part019

def surrogateDiagonalTailChunk001Sub001Block058TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub001Block058Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block058Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block058Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block058Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block058Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub001Block058Tail : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block058Part020
    + surrogateDiagTailX0RatChunk001Sub001Block058Part021
    + surrogateDiagTailX0RatChunk001Sub001Block058Part022
    + surrogateDiagTailX0RatChunk001Sub001Block058Part023
    + surrogateDiagTailX0RatChunk001Sub001Block058Part024

def surrogateDiagonalTailChunk001Sub001Block058Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk001Sub001Block058HeadSum X0
    + surrogateDiagonalTailChunk001Sub001Block058MidSum X0
    + surrogateDiagonalTailChunk001Sub001Block058TailSum X0

def surrogateDiagTailX0RatChunk001Sub001Block058 : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block058Part000
    + surrogateDiagTailX0RatChunk001Sub001Block058Part001
    + surrogateDiagTailX0RatChunk001Sub001Block058Part002
    + surrogateDiagTailX0RatChunk001Sub001Block058Part003
    + surrogateDiagTailX0RatChunk001Sub001Block058Part004
    + surrogateDiagTailX0RatChunk001Sub001Block058Part005
    + surrogateDiagTailX0RatChunk001Sub001Block058Part006
    + surrogateDiagTailX0RatChunk001Sub001Block058Part007
    + surrogateDiagTailX0RatChunk001Sub001Block058Part008
    + surrogateDiagTailX0RatChunk001Sub001Block058Part009
    + surrogateDiagTailX0RatChunk001Sub001Block058Part010
    + surrogateDiagTailX0RatChunk001Sub001Block058Part011
    + surrogateDiagTailX0RatChunk001Sub001Block058Part012
    + surrogateDiagTailX0RatChunk001Sub001Block058Part013
    + surrogateDiagTailX0RatChunk001Sub001Block058Part014
    + surrogateDiagTailX0RatChunk001Sub001Block058Part015
    + surrogateDiagTailX0RatChunk001Sub001Block058Part016
    + surrogateDiagTailX0RatChunk001Sub001Block058Part017
    + surrogateDiagTailX0RatChunk001Sub001Block058Part018
    + surrogateDiagTailX0RatChunk001Sub001Block058Part019
    + surrogateDiagTailX0RatChunk001Sub001Block058Part020
    + surrogateDiagTailX0RatChunk001Sub001Block058Part021
    + surrogateDiagTailX0RatChunk001Sub001Block058Part022
    + surrogateDiagTailX0RatChunk001Sub001Block058Part023
    + surrogateDiagTailX0RatChunk001Sub001Block058Part024

theorem surrogateDiagTailX0RatChunk001Sub001Block058_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk001Sub001Block058Head + surrogateDiagTailX0RatChunk001Sub001Block058Mid + surrogateDiagTailX0RatChunk001Sub001Block058Tail =
      surrogateDiagTailX0RatChunk001Sub001Block058 := by
  unfold surrogateDiagTailX0RatChunk001Sub001Block058Head surrogateDiagTailX0RatChunk001Sub001Block058Mid surrogateDiagTailX0RatChunk001Sub001Block058Tail surrogateDiagTailX0RatChunk001Sub001Block058
  ring

def SurrogateDiagonalTailChunk001Sub001Block058HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub001Block058HeadSum X0 = surrogateDiagTailX0RatChunk001Sub001Block058Head

def SurrogateDiagonalTailChunk001Sub001Block058MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub001Block058MidSum X0 = surrogateDiagTailX0RatChunk001Sub001Block058Mid

def SurrogateDiagonalTailChunk001Sub001Block058TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub001Block058TailSum X0 = surrogateDiagTailX0RatChunk001Sub001Block058Tail

theorem surrogateDiagonalTailChunk001Sub001Block058_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk001Sub001Block058HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk001Sub001Block058MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk001Sub001Block058TailCertificateAt X0) :
    surrogateDiagonalTailChunk001Sub001Block058Sum X0 = surrogateDiagTailX0RatChunk001Sub001Block058 := by
  unfold SurrogateDiagonalTailChunk001Sub001Block058HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk001Sub001Block058MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk001Sub001Block058TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk001Sub001Block058Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk001Sub001Block058_eq_head_add_mid_add_tail

/-- Block 059 covers tail-support indices [16475,16500) and q from 27151 to 27191. -/

def TailChunk001Sub001Block059Part000SupportExplicit : Finset ℕ :=
  ([27151] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block059Part000 : ℚ :=
  (57234763525 : ℚ) / 121279444650283272192

def SurrogateDiagonalTailChunk001Sub001Block059Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27151
    = surrogateDiagTailX0RatChunk001Sub001Block059Part000

theorem surrogateDiagonalTailChunk001Sub001Block059Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block059Part000CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block059Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block059Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block059Part000CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block059Part000SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block059Part000] using hcert

def TailChunk001Sub001Block059Part001SupportExplicit : Finset ℕ :=
  ([27154] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block059Part001 : ℚ :=
  (2880233265625 : ℚ) / 21235093853328118272

def SurrogateDiagonalTailChunk001Sub001Block059Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27154
    = surrogateDiagTailX0RatChunk001Sub001Block059Part001

theorem surrogateDiagonalTailChunk001Sub001Block059Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block059Part001CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block059Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block059Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block059Part001CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block059Part001SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block059Part001] using hcert

def TailChunk001Sub001Block059Part002SupportExplicit : Finset ℕ :=
  ([27155] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block059Part002 : ℚ :=
  (125125 : ℚ) / 55650124792038528

def SurrogateDiagonalTailChunk001Sub001Block059Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27155
    = surrogateDiagTailX0RatChunk001Sub001Block059Part002

theorem surrogateDiagonalTailChunk001Sub001Block059Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block059Part002CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block059Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block059Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block059Part002CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block059Part002SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block059Part002] using hcert

def TailChunk001Sub001Block059Part003SupportExplicit : Finset ℕ :=
  ([27157] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block059Part003 : ℚ :=
  (20318981675 : ℚ) / 36501444900643405824

def SurrogateDiagonalTailChunk001Sub001Block059Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27157
    = surrogateDiagTailX0RatChunk001Sub001Block059Part003

theorem surrogateDiagonalTailChunk001Sub001Block059Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block059Part003CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block059Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block059Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block059Part003CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block059Part003SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block059Part003] using hcert

def TailChunk001Sub001Block059Part004SupportExplicit : Finset ℕ :=
  ([27158] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block059Part004 : ℚ :=
  (1371466843925 : ℚ) / 9420440622589921536

def SurrogateDiagonalTailChunk001Sub001Block059Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27158
    = surrogateDiagTailX0RatChunk001Sub001Block059Part004

theorem surrogateDiagonalTailChunk001Sub001Block059Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block059Part004CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block059Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block059Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block059Part004CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block059Part004SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block059Part004] using hcert

def TailChunk001Sub001Block059Part005SupportExplicit : Finset ℕ :=
  ([27159] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block059Part005 : ℚ :=
  (20525071633 : ℚ) / 7306242842073139200

def SurrogateDiagonalTailChunk001Sub001Block059Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27159
    = surrogateDiagTailX0RatChunk001Sub001Block059Part005

theorem surrogateDiagonalTailChunk001Sub001Block059Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block059Part005CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block059Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block059Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block059Part005CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block059Part005SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block059Part005] using hcert

def TailChunk001Sub001Block059Part006SupportExplicit : Finset ℕ :=
  ([27161] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block059Part006 : ℚ :=
  (17050791725 : ℚ) / 216016929945513934848

def SurrogateDiagonalTailChunk001Sub001Block059Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27161
    = surrogateDiagTailX0RatChunk001Sub001Block059Part006

theorem surrogateDiagonalTailChunk001Sub001Block059Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block059Part006CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block059Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block059Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block059Part006CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block059Part006SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block059Part006] using hcert

def TailChunk001Sub001Block059Part007SupportExplicit : Finset ℕ :=
  ([27163] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block059Part007 : ℚ :=
  (7095124403 : ℚ) / 22713057850557465600

def SurrogateDiagonalTailChunk001Sub001Block059Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27163
    = surrogateDiagTailX0RatChunk001Sub001Block059Part007

theorem surrogateDiagonalTailChunk001Sub001Block059Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block059Part007CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block059Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block059Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block059Part007CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block059Part007SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block059Part007] using hcert

def TailChunk001Sub001Block059Part008SupportExplicit : Finset ℕ :=
  ([27165] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block059Part008 : ℚ :=
  (4119300097 : ℚ) / 1099261724287180800

def SurrogateDiagonalTailChunk001Sub001Block059Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27165
    = surrogateDiagTailX0RatChunk001Sub001Block059Part008

theorem surrogateDiagonalTailChunk001Sub001Block059Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block059Part008CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block059Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block059Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block059Part008CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block059Part008SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block059Part008] using hcert

def TailChunk001Sub001Block059Part009SupportExplicit : Finset ℕ :=
  ([27167] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block059Part009 : ℚ :=
  (37665970427 : ℚ) / 14688882555601305600

def SurrogateDiagonalTailChunk001Sub001Block059Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27167
    = surrogateDiagTailX0RatChunk001Sub001Block059Part009

theorem surrogateDiagonalTailChunk001Sub001Block059Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block059Part009CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block059Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block059Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block059Part009CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block059Part009SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block059Part009] using hcert

def TailChunk001Sub001Block059Part010SupportExplicit : Finset ℕ :=
  ([27169] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block059Part010 : ℚ :=
  (776931999 : ℚ) / 8599531188992000000

def SurrogateDiagonalTailChunk001Sub001Block059Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27169
    = surrogateDiagTailX0RatChunk001Sub001Block059Part010

theorem surrogateDiagonalTailChunk001Sub001Block059Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block059Part010CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block059Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block059Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block059Part010CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block059Part010SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block059Part010] using hcert

def TailChunk001Sub001Block059Part011SupportExplicit : Finset ℕ :=
  ([27170] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block059Part011 : ℚ :=
  (4137879659 : ℚ) / 11147354585432064

def SurrogateDiagonalTailChunk001Sub001Block059Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27170
    = surrogateDiagTailX0RatChunk001Sub001Block059Part011

theorem surrogateDiagonalTailChunk001Sub001Block059Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block059Part011CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block059Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block059Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block059Part011CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block059Part011SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block059Part011] using hcert

def TailChunk001Sub001Block059Part012SupportExplicit : Finset ℕ :=
  ([27173] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block059Part012 : ℚ :=
  (70573289275 : ℚ) / 294918752295206387712

def SurrogateDiagonalTailChunk001Sub001Block059Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27173
    = surrogateDiagTailX0RatChunk001Sub001Block059Part012

theorem surrogateDiagonalTailChunk001Sub001Block059Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block059Part012CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block059Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block059Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block059Part012CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block059Part012SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block059Part012] using hcert

def TailChunk001Sub001Block059Part013SupportExplicit : Finset ℕ :=
  ([27174] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block059Part013 : ℚ :=
  (2049293865725 : ℚ) / 4514939336053269504

def SurrogateDiagonalTailChunk001Sub001Block059Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27174
    = surrogateDiagTailX0RatChunk001Sub001Block059Part013

theorem surrogateDiagonalTailChunk001Sub001Block059Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block059Part013CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block059Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block059Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block059Part013CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block059Part013SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block059Part013] using hcert

def TailChunk001Sub001Block059Part014SupportExplicit : Finset ℕ :=
  ([27177] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block059Part014 : ℚ :=
  (125025 : ℚ) / 53854159514787968

def SurrogateDiagonalTailChunk001Sub001Block059Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27177
    = surrogateDiagTailX0RatChunk001Sub001Block059Part014

theorem surrogateDiagonalTailChunk001Sub001Block059Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block059Part014CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block059Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block059Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block059Part014CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block059Part014SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block059Part014] using hcert

def TailChunk001Sub001Block059Part015SupportExplicit : Finset ℕ :=
  ([27178] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block059Part015 : ℚ :=
  (114495457925 : ℚ) / 811907259769037376

def SurrogateDiagonalTailChunk001Sub001Block059Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27178
    = surrogateDiagTailX0RatChunk001Sub001Block059Part015

theorem surrogateDiagonalTailChunk001Sub001Block059Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block059Part015CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block059Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block059Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block059Part015CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block059Part015SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block059Part015] using hcert

def TailChunk001Sub001Block059Part016SupportExplicit : Finset ℕ :=
  ([27179] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block059Part016 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block059Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27179
    = surrogateDiagTailX0RatChunk001Sub001Block059Part016

theorem surrogateDiagonalTailChunk001Sub001Block059Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block059Part016CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block059Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block059Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block059Part016CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block059Part016SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block059Part016] using hcert

def TailChunk001Sub001Block059Part017SupportExplicit : Finset ℕ :=
  ([27181] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block059Part017 : ℚ :=
  (88089709273 : ℚ) / 19900432066491187200

def SurrogateDiagonalTailChunk001Sub001Block059Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27181
    = surrogateDiagTailX0RatChunk001Sub001Block059Part017

theorem surrogateDiagonalTailChunk001Sub001Block059Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block059Part017CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block059Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block059Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block059Part017CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block059Part017SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block059Part017] using hcert

def TailChunk001Sub001Block059Part018SupportExplicit : Finset ℕ :=
  ([27182] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block059Part018 : ℚ :=
  (4617882025 : ℚ) / 34116516220466322

def SurrogateDiagonalTailChunk001Sub001Block059Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27182
    = surrogateDiagTailX0RatChunk001Sub001Block059Part018

theorem surrogateDiagonalTailChunk001Sub001Block059Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block059Part018CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block059Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block059Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block059Part018CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block059Part018SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block059Part018] using hcert

def TailChunk001Sub001Block059Part019SupportExplicit : Finset ℕ :=
  ([27183] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block059Part019 : ℚ :=
  (9733296317 : ℚ) / 1855796957046374400

def SurrogateDiagonalTailChunk001Sub001Block059Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27183
    = surrogateDiagTailX0RatChunk001Sub001Block059Part019

theorem surrogateDiagonalTailChunk001Sub001Block059Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block059Part019CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block059Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block059Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block059Part019CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block059Part019SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block059Part019] using hcert

def TailChunk001Sub001Block059Part020SupportExplicit : Finset ℕ :=
  ([27185] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block059Part020 : ℚ :=
  (1848131507875 : ℚ) / 558965001756120219648

def SurrogateDiagonalTailChunk001Sub001Block059Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27185
    = surrogateDiagTailX0RatChunk001Sub001Block059Part020

theorem surrogateDiagonalTailChunk001Sub001Block059Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block059Part020CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block059Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block059Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block059Part020CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block059Part020SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block059Part020] using hcert

def TailChunk001Sub001Block059Part021SupportExplicit : Finset ℕ :=
  ([27186] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block059Part021 : ℚ :=
  (794971757775 : ℚ) / 2305210557270376448

def SurrogateDiagonalTailChunk001Sub001Block059Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27186
    = surrogateDiagTailX0RatChunk001Sub001Block059Part021

theorem surrogateDiagonalTailChunk001Sub001Block059Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block059Part021CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block059Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block059Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block059Part021CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block059Part021SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block059Part021] using hcert

def TailChunk001Sub001Block059Part022SupportExplicit : Finset ℕ :=
  ([27187] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block059Part022 : ℚ :=
  (1991792099 : ℚ) / 9541535916689418240

def SurrogateDiagonalTailChunk001Sub001Block059Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27187
    = surrogateDiagTailX0RatChunk001Sub001Block059Part022

theorem surrogateDiagonalTailChunk001Sub001Block059Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block059Part022CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block059Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block059Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block059Part022CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block059Part022SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block059Part022] using hcert

def TailChunk001Sub001Block059Part023SupportExplicit : Finset ℕ :=
  ([27190] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block059Part023 : ℚ :=
  (7851233393725 : ℚ) / 34935312609757513728

def SurrogateDiagonalTailChunk001Sub001Block059Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27190
    = surrogateDiagTailX0RatChunk001Sub001Block059Part023

theorem surrogateDiagonalTailChunk001Sub001Block059Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block059Part023CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block059Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block059Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block059Part023CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block059Part023SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block059Part023] using hcert

def TailChunk001Sub001Block059Part024SupportExplicit : Finset ℕ :=
  ([27191] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block059Part024 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block059Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27191
    = surrogateDiagTailX0RatChunk001Sub001Block059Part024

theorem surrogateDiagonalTailChunk001Sub001Block059Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block059Part024CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block059Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block059Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block059Part024CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block059Part024SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block059Part024] using hcert

def surrogateDiagonalTailChunk001Sub001Block059HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub001Block059Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block059Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block059Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block059Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block059Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block059Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block059Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block059Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block059Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block059Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub001Block059Head : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block059Part000
    + surrogateDiagTailX0RatChunk001Sub001Block059Part001
    + surrogateDiagTailX0RatChunk001Sub001Block059Part002
    + surrogateDiagTailX0RatChunk001Sub001Block059Part003
    + surrogateDiagTailX0RatChunk001Sub001Block059Part004
    + surrogateDiagTailX0RatChunk001Sub001Block059Part005
    + surrogateDiagTailX0RatChunk001Sub001Block059Part006
    + surrogateDiagTailX0RatChunk001Sub001Block059Part007
    + surrogateDiagTailX0RatChunk001Sub001Block059Part008
    + surrogateDiagTailX0RatChunk001Sub001Block059Part009

def surrogateDiagonalTailChunk001Sub001Block059MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub001Block059Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block059Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block059Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block059Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block059Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block059Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block059Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block059Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block059Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block059Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub001Block059Mid : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block059Part010
    + surrogateDiagTailX0RatChunk001Sub001Block059Part011
    + surrogateDiagTailX0RatChunk001Sub001Block059Part012
    + surrogateDiagTailX0RatChunk001Sub001Block059Part013
    + surrogateDiagTailX0RatChunk001Sub001Block059Part014
    + surrogateDiagTailX0RatChunk001Sub001Block059Part015
    + surrogateDiagTailX0RatChunk001Sub001Block059Part016
    + surrogateDiagTailX0RatChunk001Sub001Block059Part017
    + surrogateDiagTailX0RatChunk001Sub001Block059Part018
    + surrogateDiagTailX0RatChunk001Sub001Block059Part019

def surrogateDiagonalTailChunk001Sub001Block059TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub001Block059Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block059Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block059Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block059Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block059Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub001Block059Tail : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block059Part020
    + surrogateDiagTailX0RatChunk001Sub001Block059Part021
    + surrogateDiagTailX0RatChunk001Sub001Block059Part022
    + surrogateDiagTailX0RatChunk001Sub001Block059Part023
    + surrogateDiagTailX0RatChunk001Sub001Block059Part024

def surrogateDiagonalTailChunk001Sub001Block059Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk001Sub001Block059HeadSum X0
    + surrogateDiagonalTailChunk001Sub001Block059MidSum X0
    + surrogateDiagonalTailChunk001Sub001Block059TailSum X0

def surrogateDiagTailX0RatChunk001Sub001Block059 : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block059Part000
    + surrogateDiagTailX0RatChunk001Sub001Block059Part001
    + surrogateDiagTailX0RatChunk001Sub001Block059Part002
    + surrogateDiagTailX0RatChunk001Sub001Block059Part003
    + surrogateDiagTailX0RatChunk001Sub001Block059Part004
    + surrogateDiagTailX0RatChunk001Sub001Block059Part005
    + surrogateDiagTailX0RatChunk001Sub001Block059Part006
    + surrogateDiagTailX0RatChunk001Sub001Block059Part007
    + surrogateDiagTailX0RatChunk001Sub001Block059Part008
    + surrogateDiagTailX0RatChunk001Sub001Block059Part009
    + surrogateDiagTailX0RatChunk001Sub001Block059Part010
    + surrogateDiagTailX0RatChunk001Sub001Block059Part011
    + surrogateDiagTailX0RatChunk001Sub001Block059Part012
    + surrogateDiagTailX0RatChunk001Sub001Block059Part013
    + surrogateDiagTailX0RatChunk001Sub001Block059Part014
    + surrogateDiagTailX0RatChunk001Sub001Block059Part015
    + surrogateDiagTailX0RatChunk001Sub001Block059Part016
    + surrogateDiagTailX0RatChunk001Sub001Block059Part017
    + surrogateDiagTailX0RatChunk001Sub001Block059Part018
    + surrogateDiagTailX0RatChunk001Sub001Block059Part019
    + surrogateDiagTailX0RatChunk001Sub001Block059Part020
    + surrogateDiagTailX0RatChunk001Sub001Block059Part021
    + surrogateDiagTailX0RatChunk001Sub001Block059Part022
    + surrogateDiagTailX0RatChunk001Sub001Block059Part023
    + surrogateDiagTailX0RatChunk001Sub001Block059Part024

theorem surrogateDiagTailX0RatChunk001Sub001Block059_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk001Sub001Block059Head + surrogateDiagTailX0RatChunk001Sub001Block059Mid + surrogateDiagTailX0RatChunk001Sub001Block059Tail =
      surrogateDiagTailX0RatChunk001Sub001Block059 := by
  unfold surrogateDiagTailX0RatChunk001Sub001Block059Head surrogateDiagTailX0RatChunk001Sub001Block059Mid surrogateDiagTailX0RatChunk001Sub001Block059Tail surrogateDiagTailX0RatChunk001Sub001Block059
  ring

def SurrogateDiagonalTailChunk001Sub001Block059HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub001Block059HeadSum X0 = surrogateDiagTailX0RatChunk001Sub001Block059Head

def SurrogateDiagonalTailChunk001Sub001Block059MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub001Block059MidSum X0 = surrogateDiagTailX0RatChunk001Sub001Block059Mid

def SurrogateDiagonalTailChunk001Sub001Block059TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub001Block059TailSum X0 = surrogateDiagTailX0RatChunk001Sub001Block059Tail

theorem surrogateDiagonalTailChunk001Sub001Block059_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk001Sub001Block059HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk001Sub001Block059MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk001Sub001Block059TailCertificateAt X0) :
    surrogateDiagonalTailChunk001Sub001Block059Sum X0 = surrogateDiagTailX0RatChunk001Sub001Block059 := by
  unfold SurrogateDiagonalTailChunk001Sub001Block059HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk001Sub001Block059MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk001Sub001Block059TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk001Sub001Block059Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk001Sub001Block059_eq_head_add_mid_add_tail

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0TailPilot25

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

open scoped BigOperators

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

/- Generated direct-term certificate blocks for tail chunk 001, subchunk 000, blocks [130,140). -/

/-- Block 130 covers tail-support indices [13250,13275) and q from 21838 to 21882. -/

def TailChunk001Sub000Block130Part000SupportExplicit : Finset ℕ :=
  ([21838] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block130Part000 : ℚ :=
  (144038033381 : ℚ) / 650641656998937600

def SurrogateDiagonalTailChunk001Sub000Block130Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21838
    = surrogateDiagTailX0RatChunk001Sub000Block130Part000

theorem surrogateDiagonalTailChunk001Sub000Block130Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block130Part000CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block130Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block130Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block130Part000CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block130Part000SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block130Part000] using hcert

def TailChunk001Sub000Block130Part001SupportExplicit : Finset ℕ :=
  ([21839] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block130Part001 : ℚ :=
  (7452217515625 : ℚ) / 142173388448318495442

def SurrogateDiagonalTailChunk001Sub000Block130Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21839
    = surrogateDiagTailX0RatChunk001Sub000Block130Part001

theorem surrogateDiagonalTailChunk001Sub000Block130Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block130Part001CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block130Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block130Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block130Part001CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block130Part001SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block130Part001] using hcert

def TailChunk001Sub000Block130Part002SupportExplicit : Finset ℕ :=
  ([21841] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block130Part002 : ℚ :=
  (11925732025 : ℚ) / 227560765659881472

def SurrogateDiagonalTailChunk001Sub000Block130Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21841
    = surrogateDiagTailX0RatChunk001Sub000Block130Part002

theorem surrogateDiagonalTailChunk001Sub000Block130Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block130Part002CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block130Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block130Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block130Part002CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block130Part002SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block130Part002] using hcert

def TailChunk001Sub000Block130Part003SupportExplicit : Finset ℕ :=
  ([21842] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block130Part003 : ℚ :=
  (25054184075 : ℚ) / 113467156482497796

def SurrogateDiagonalTailChunk001Sub000Block130Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21842
    = surrogateDiagTailX0RatChunk001Sub000Block130Part003

theorem surrogateDiagonalTailChunk001Sub000Block130Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block130Part003CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block130Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block130Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block130Part003CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block130Part003SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block130Part003] using hcert

def TailChunk001Sub000Block130Part004SupportExplicit : Finset ℕ :=
  ([21845] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block130Part004 : ℚ :=
  (8496365535125 : ℚ) / 90090006945919401984

def SurrogateDiagonalTailChunk001Sub000Block130Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21845
    = surrogateDiagTailX0RatChunk001Sub000Block130Part004

theorem surrogateDiagonalTailChunk001Sub000Block130Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block130Part004CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block130Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block130Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block130Part004CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block130Part004SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block130Part004] using hcert

def TailChunk001Sub000Block130Part005SupportExplicit : Finset ℕ :=
  ([21846] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block130Part005 : ℚ :=
  (58112362181 : ℚ) / 94892654736000000

def SurrogateDiagonalTailChunk001Sub000Block130Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21846
    = surrogateDiagTailX0RatChunk001Sub000Block130Part005

theorem surrogateDiagonalTailChunk001Sub000Block130Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block130Part005CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block130Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block130Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block130Part005CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block130Part005SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block130Part005] using hcert

def TailChunk001Sub000Block130Part006SupportExplicit : Finset ℕ :=
  ([21847] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block130Part006 : ℚ :=
  (97352303773 : ℚ) / 1364795928988876800

def SurrogateDiagonalTailChunk001Sub000Block130Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21847
    = surrogateDiagTailX0RatChunk001Sub000Block130Part006

theorem surrogateDiagonalTailChunk001Sub000Block130Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block130Part006CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block130Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block130Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block130Part006CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block130Part006SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block130Part006] using hcert

def TailChunk001Sub000Block130Part007SupportExplicit : Finset ℕ :=
  ([21849] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block130Part007 : ℚ :=
  (1205227751975 : ℚ) / 10227202491748691328

def SurrogateDiagonalTailChunk001Sub000Block130Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21849
    = surrogateDiagTailX0RatChunk001Sub000Block130Part007

theorem surrogateDiagonalTailChunk001Sub000Block130Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block130Part007CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block130Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block130Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block130Part007CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block130Part007SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block130Part007] using hcert

def TailChunk001Sub000Block130Part008SupportExplicit : Finset ℕ :=
  ([21851] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block130Part008 : ℚ :=
  (477466201 : ℚ) / 9119113198198050

def SurrogateDiagonalTailChunk001Sub000Block130Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21851
    = surrogateDiagTailX0RatChunk001Sub000Block130Part008

theorem surrogateDiagonalTailChunk001Sub000Block130Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block130Part008CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block130Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block130Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block130Part008CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block130Part008SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block130Part008] using hcert

def TailChunk001Sub000Block130Part009SupportExplicit : Finset ℕ :=
  ([21855] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block130Part009 : ℚ :=
  (107061588763 : ℚ) / 495269848114790400

def SurrogateDiagonalTailChunk001Sub000Block130Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21855
    = surrogateDiagTailX0RatChunk001Sub000Block130Part009

theorem surrogateDiagonalTailChunk001Sub000Block130Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block130Part009CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block130Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block130Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block130Part009CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block130Part009SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block130Part009] using hcert

def TailChunk001Sub000Block130Part010SupportExplicit : Finset ℕ :=
  ([21857] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block130Part010 : ℚ :=
  (62873108821 : ℚ) / 972487088927080200

def SurrogateDiagonalTailChunk001Sub000Block130Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21857
    = surrogateDiagTailX0RatChunk001Sub000Block130Part010

theorem surrogateDiagonalTailChunk001Sub000Block130Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block130Part010CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block130Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block130Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block130Part010CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block130Part010SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block130Part010] using hcert

def TailChunk001Sub000Block130Part011SupportExplicit : Finset ℕ :=
  ([21858] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block130Part011 : ℚ :=
  (3316665635725 : ℚ) / 7038929369128791168

def SurrogateDiagonalTailChunk001Sub000Block130Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21858
    = surrogateDiagTailX0RatChunk001Sub000Block130Part011

theorem surrogateDiagonalTailChunk001Sub000Block130Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block130Part011CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block130Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block130Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block130Part011CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block130Part011SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block130Part011] using hcert

def TailChunk001Sub000Block130Part012SupportExplicit : Finset ℕ :=
  ([21859] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block130Part012 : ℚ :=
  (7465873140625 : ℚ) / 142694933713363465362

def SurrogateDiagonalTailChunk001Sub000Block130Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21859
    = surrogateDiagTailX0RatChunk001Sub000Block130Part012

theorem surrogateDiagonalTailChunk001Sub000Block130Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block130Part012CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block130Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block130Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block130Part012CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block130Part012SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block130Part012] using hcert

def TailChunk001Sub000Block130Part013SupportExplicit : Finset ℕ :=
  ([21862] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block130Part013 : ℚ :=
  (1130144072375 : ℚ) / 4639761441548402688

def SurrogateDiagonalTailChunk001Sub000Block130Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21862
    = surrogateDiagTailX0RatChunk001Sub000Block130Part013

theorem surrogateDiagonalTailChunk001Sub000Block130Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block130Part013CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block130Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block130Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block130Part013CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block130Part013SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block130Part013] using hcert

def TailChunk001Sub000Block130Part014SupportExplicit : Finset ℕ :=
  ([21863] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block130Part014 : ℚ :=
  (7468605765625 : ℚ) / 142799414714819752242

def SurrogateDiagonalTailChunk001Sub000Block130Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21863
    = surrogateDiagTailX0RatChunk001Sub000Block130Part014

theorem surrogateDiagonalTailChunk001Sub000Block130Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block130Part014CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block130Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block130Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block130Part014CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block130Part014SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block130Part014] using hcert

def TailChunk001Sub000Block130Part015SupportExplicit : Finset ℕ :=
  ([21865] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block130Part015 : ℚ :=
  (1194727140625 : ℚ) / 14617309905383835648

def SurrogateDiagonalTailChunk001Sub000Block130Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21865
    = surrogateDiagTailX0RatChunk001Sub000Block130Part015

theorem surrogateDiagonalTailChunk001Sub000Block130Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block130Part015CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block130Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block130Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block130Part015CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block130Part015SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block130Part015] using hcert

def TailChunk001Sub000Block130Part016SupportExplicit : Finset ℕ :=
  ([21867] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block130Part016 : ℚ :=
  (199631223425 : ℚ) / 1574129944676007936

def SurrogateDiagonalTailChunk001Sub000Block130Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21867
    = surrogateDiagTailX0RatChunk001Sub000Block130Part016

theorem surrogateDiagonalTailChunk001Sub000Block130Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block130Part016CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block130Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block130Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block130Part016CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block130Part016SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block130Part016] using hcert

def TailChunk001Sub000Block130Part017SupportExplicit : Finset ℕ :=
  ([21869] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block130Part017 : ℚ :=
  (1081434971881 : ℚ) / 18364040083602000000

def SurrogateDiagonalTailChunk001Sub000Block130Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21869
    = surrogateDiagTailX0RatChunk001Sub000Block130Part017

theorem surrogateDiagonalTailChunk001Sub000Block130Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block130Part017CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block130Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block130Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block130Part017CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block130Part017SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block130Part017] using hcert

def TailChunk001Sub000Block130Part018SupportExplicit : Finset ℕ :=
  ([21871] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block130Part018 : ℚ :=
  (11958516025 : ℚ) / 228813678134519922

def SurrogateDiagonalTailChunk001Sub000Block130Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21871
    = surrogateDiagTailX0RatChunk001Sub000Block130Part018

theorem surrogateDiagonalTailChunk001Sub000Block130Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block130Part018CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block130Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block130Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block130Part018CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block130Part018SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block130Part018] using hcert

def TailChunk001Sub000Block130Part019SupportExplicit : Finset ℕ :=
  ([21873] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block130Part019 : ℚ :=
  (372224128875 : ℚ) / 2831861149562863616

def SurrogateDiagonalTailChunk001Sub000Block130Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21873
    = surrogateDiagTailX0RatChunk001Sub000Block130Part019

theorem surrogateDiagonalTailChunk001Sub000Block130Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block130Part019CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block130Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block130Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block130Part019CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block130Part019SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block130Part019] using hcert

def TailChunk001Sub000Block130Part020SupportExplicit : Finset ℕ :=
  ([21874] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block130Part020 : ℚ :=
  (1869030765625 : ℚ) / 8941304264798065152

def SurrogateDiagonalTailChunk001Sub000Block130Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21874
    = surrogateDiagTailX0RatChunk001Sub000Block130Part020

theorem surrogateDiagonalTailChunk001Sub000Block130Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block130Part020CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block130Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block130Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block130Part020CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block130Part020SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block130Part020] using hcert

def TailChunk001Sub000Block130Part021SupportExplicit : Finset ℕ :=
  ([21877] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block130Part021 : ℚ :=
  (1167833585977 : ℚ) / 21691651160035459200

def SurrogateDiagonalTailChunk001Sub000Block130Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21877
    = surrogateDiagTailX0RatChunk001Sub000Block130Part021

theorem surrogateDiagonalTailChunk001Sub000Block130Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block130Part021CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block130Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block130Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block130Part021CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block130Part021SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block130Part021] using hcert

def TailChunk001Sub000Block130Part022SupportExplicit : Finset ℕ :=
  ([21878] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block130Part022 : ℚ :=
  (1869714390625 : ℚ) / 8947846881749253042

def SurrogateDiagonalTailChunk001Sub000Block130Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21878
    = surrogateDiagTailX0RatChunk001Sub000Block130Part022

theorem surrogateDiagonalTailChunk001Sub000Block130Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block130Part022CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block130Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block130Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block130Part022CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block130Part022SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block130Part022] using hcert

def TailChunk001Sub000Block130Part023SupportExplicit : Finset ℕ :=
  ([21881] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block130Part023 : ℚ :=
  (11969454025 : ℚ) / 229232463068508672

def SurrogateDiagonalTailChunk001Sub000Block130Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21881
    = surrogateDiagTailX0RatChunk001Sub000Block130Part023

theorem surrogateDiagonalTailChunk001Sub000Block130Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block130Part023CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block130Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block130Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block130Part023CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block130Part023SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block130Part023] using hcert

def TailChunk001Sub000Block130Part024SupportExplicit : Finset ℕ :=
  ([21882] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block130Part024 : ℚ :=
  (2030813677 : ℚ) / 2808222076108800

def SurrogateDiagonalTailChunk001Sub000Block130Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21882
    = surrogateDiagTailX0RatChunk001Sub000Block130Part024

theorem surrogateDiagonalTailChunk001Sub000Block130Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block130Part024CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block130Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block130Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block130Part024CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block130Part024SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block130Part024] using hcert

def surrogateDiagonalTailChunk001Sub000Block130HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block130Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block130Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block130Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block130Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block130Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block130Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block130Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block130Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block130Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block130Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block130Head : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block130Part000
    + surrogateDiagTailX0RatChunk001Sub000Block130Part001
    + surrogateDiagTailX0RatChunk001Sub000Block130Part002
    + surrogateDiagTailX0RatChunk001Sub000Block130Part003
    + surrogateDiagTailX0RatChunk001Sub000Block130Part004
    + surrogateDiagTailX0RatChunk001Sub000Block130Part005
    + surrogateDiagTailX0RatChunk001Sub000Block130Part006
    + surrogateDiagTailX0RatChunk001Sub000Block130Part007
    + surrogateDiagTailX0RatChunk001Sub000Block130Part008
    + surrogateDiagTailX0RatChunk001Sub000Block130Part009

def surrogateDiagonalTailChunk001Sub000Block130MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block130Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block130Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block130Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block130Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block130Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block130Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block130Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block130Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block130Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block130Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block130Mid : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block130Part010
    + surrogateDiagTailX0RatChunk001Sub000Block130Part011
    + surrogateDiagTailX0RatChunk001Sub000Block130Part012
    + surrogateDiagTailX0RatChunk001Sub000Block130Part013
    + surrogateDiagTailX0RatChunk001Sub000Block130Part014
    + surrogateDiagTailX0RatChunk001Sub000Block130Part015
    + surrogateDiagTailX0RatChunk001Sub000Block130Part016
    + surrogateDiagTailX0RatChunk001Sub000Block130Part017
    + surrogateDiagTailX0RatChunk001Sub000Block130Part018
    + surrogateDiagTailX0RatChunk001Sub000Block130Part019

def surrogateDiagonalTailChunk001Sub000Block130TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block130Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block130Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block130Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block130Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block130Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block130Tail : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block130Part020
    + surrogateDiagTailX0RatChunk001Sub000Block130Part021
    + surrogateDiagTailX0RatChunk001Sub000Block130Part022
    + surrogateDiagTailX0RatChunk001Sub000Block130Part023
    + surrogateDiagTailX0RatChunk001Sub000Block130Part024

def surrogateDiagonalTailChunk001Sub000Block130Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk001Sub000Block130HeadSum X0
    + surrogateDiagonalTailChunk001Sub000Block130MidSum X0
    + surrogateDiagonalTailChunk001Sub000Block130TailSum X0

def surrogateDiagTailX0RatChunk001Sub000Block130 : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block130Part000
    + surrogateDiagTailX0RatChunk001Sub000Block130Part001
    + surrogateDiagTailX0RatChunk001Sub000Block130Part002
    + surrogateDiagTailX0RatChunk001Sub000Block130Part003
    + surrogateDiagTailX0RatChunk001Sub000Block130Part004
    + surrogateDiagTailX0RatChunk001Sub000Block130Part005
    + surrogateDiagTailX0RatChunk001Sub000Block130Part006
    + surrogateDiagTailX0RatChunk001Sub000Block130Part007
    + surrogateDiagTailX0RatChunk001Sub000Block130Part008
    + surrogateDiagTailX0RatChunk001Sub000Block130Part009
    + surrogateDiagTailX0RatChunk001Sub000Block130Part010
    + surrogateDiagTailX0RatChunk001Sub000Block130Part011
    + surrogateDiagTailX0RatChunk001Sub000Block130Part012
    + surrogateDiagTailX0RatChunk001Sub000Block130Part013
    + surrogateDiagTailX0RatChunk001Sub000Block130Part014
    + surrogateDiagTailX0RatChunk001Sub000Block130Part015
    + surrogateDiagTailX0RatChunk001Sub000Block130Part016
    + surrogateDiagTailX0RatChunk001Sub000Block130Part017
    + surrogateDiagTailX0RatChunk001Sub000Block130Part018
    + surrogateDiagTailX0RatChunk001Sub000Block130Part019
    + surrogateDiagTailX0RatChunk001Sub000Block130Part020
    + surrogateDiagTailX0RatChunk001Sub000Block130Part021
    + surrogateDiagTailX0RatChunk001Sub000Block130Part022
    + surrogateDiagTailX0RatChunk001Sub000Block130Part023
    + surrogateDiagTailX0RatChunk001Sub000Block130Part024

theorem surrogateDiagTailX0RatChunk001Sub000Block130_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk001Sub000Block130Head + surrogateDiagTailX0RatChunk001Sub000Block130Mid + surrogateDiagTailX0RatChunk001Sub000Block130Tail =
      surrogateDiagTailX0RatChunk001Sub000Block130 := by
  unfold surrogateDiagTailX0RatChunk001Sub000Block130Head surrogateDiagTailX0RatChunk001Sub000Block130Mid surrogateDiagTailX0RatChunk001Sub000Block130Tail surrogateDiagTailX0RatChunk001Sub000Block130
  ring

def SurrogateDiagonalTailChunk001Sub000Block130HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block130HeadSum X0 = surrogateDiagTailX0RatChunk001Sub000Block130Head

def SurrogateDiagonalTailChunk001Sub000Block130MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block130MidSum X0 = surrogateDiagTailX0RatChunk001Sub000Block130Mid

def SurrogateDiagonalTailChunk001Sub000Block130TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block130TailSum X0 = surrogateDiagTailX0RatChunk001Sub000Block130Tail

theorem surrogateDiagonalTailChunk001Sub000Block130_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk001Sub000Block130HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk001Sub000Block130MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk001Sub000Block130TailCertificateAt X0) :
    surrogateDiagonalTailChunk001Sub000Block130Sum X0 = surrogateDiagTailX0RatChunk001Sub000Block130 := by
  unfold SurrogateDiagonalTailChunk001Sub000Block130HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk001Sub000Block130MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk001Sub000Block130TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk001Sub000Block130Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk001Sub000Block130_eq_head_add_mid_add_tail

/-- Block 131 covers tail-support indices [13275,13300) and q from 21883 to 21922. -/

def TailChunk001Sub000Block131Part000SupportExplicit : Finset ℕ :=
  ([21883] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block131Part000 : ℚ :=
  (7268244802075 : ℚ) / 134270809299905720832

def SurrogateDiagonalTailChunk001Sub000Block131Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21883
    = surrogateDiagTailX0RatChunk001Sub000Block131Part000

theorem surrogateDiagonalTailChunk001Sub000Block131Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block131Part000CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block131Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block131Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block131Part000CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block131Part000SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block131Part000] using hcert

def TailChunk001Sub000Block131Part001SupportExplicit : Finset ℕ :=
  ([21885] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block131Part001 : ℚ :=
  (2967563290175 : ℚ) / 15427503302699483136

def SurrogateDiagonalTailChunk001Sub000Block131Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21885
    = surrogateDiagTailX0RatChunk001Sub000Block131Part001

theorem surrogateDiagonalTailChunk001Sub000Block131Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block131Part001CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block131Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block131Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block131Part001CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block131Part001SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block131Part001] using hcert

def TailChunk001Sub000Block131Part002SupportExplicit : Finset ℕ :=
  ([21886] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block131Part002 : ℚ :=
  (283221518029 : ℚ) / 1243777004155699200

def SurrogateDiagonalTailChunk001Sub000Block131Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21886
    = surrogateDiagTailX0RatChunk001Sub000Block131Part002

theorem surrogateDiagonalTailChunk001Sub000Block131Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block131Part002CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block131Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block131Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block131Part002CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block131Part002SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block131Part002] using hcert

def TailChunk001Sub000Block131Part003SupportExplicit : Finset ℕ :=
  ([21887] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block131Part003 : ℚ :=
  (3179113166225 : ℚ) / 57575319966499571712

def SurrogateDiagonalTailChunk001Sub000Block131Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21887
    = surrogateDiagTailX0RatChunk001Sub000Block131Part003

theorem surrogateDiagonalTailChunk001Sub000Block131Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block131Part003CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block131Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block131Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block131Part003CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block131Part003SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block131Part003] using hcert

def TailChunk001Sub000Block131Part004SupportExplicit : Finset ℕ :=
  ([21889] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block131Part004 : ℚ :=
  (21229139669125 : ℚ) / 268137285958661603328

def SurrogateDiagonalTailChunk001Sub000Block131Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21889
    = surrogateDiagTailX0RatChunk001Sub000Block131Part004

theorem surrogateDiagonalTailChunk001Sub000Block131Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block131Part004CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block131Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block131Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block131Part004CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block131Part004SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block131Part004] using hcert

def TailChunk001Sub000Block131Part005SupportExplicit : Finset ℕ :=
  ([21890] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block131Part005 : ℚ :=
  (43815330763 : ℚ) / 98384704430284800

def SurrogateDiagonalTailChunk001Sub000Block131Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21890
    = surrogateDiagTailX0RatChunk001Sub000Block131Part005

theorem surrogateDiagonalTailChunk001Sub000Block131Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block131Part005CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block131Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block131Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block131Part005CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block131Part005SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block131Part005] using hcert

def TailChunk001Sub000Block131Part006SupportExplicit : Finset ℕ :=
  ([21891] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block131Part006 : ℚ :=
  (13308528270325 : ℚ) / 113366866518394011648

def SurrogateDiagonalTailChunk001Sub000Block131Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21891
    = surrogateDiagTailX0RatChunk001Sub000Block131Part006

theorem surrogateDiagonalTailChunk001Sub000Block131Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block131Part006CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block131Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block131Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block131Part006CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block131Part006SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block131Part006] using hcert

def TailChunk001Sub000Block131Part007SupportExplicit : Finset ℕ :=
  ([21893] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block131Part007 : ℚ :=
  (7489116390625 : ℚ) / 143584852189062734112

def SurrogateDiagonalTailChunk001Sub000Block131Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21893
    = surrogateDiagTailX0RatChunk001Sub000Block131Part007

theorem surrogateDiagonalTailChunk001Sub000Block131Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block131Part007CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block131Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block131Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block131Part007CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block131Part007SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block131Part007] using hcert

def TailChunk001Sub000Block131Part008SupportExplicit : Finset ℕ :=
  ([21894] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block131Part008 : ℚ :=
  (8467192983 : ℚ) / 16378956433326080

def SurrogateDiagonalTailChunk001Sub000Block131Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21894
    = surrogateDiagTailX0RatChunk001Sub000Block131Part008

theorem surrogateDiagonalTailChunk001Sub000Block131Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block131Part008CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block131Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block131Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block131Part008CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block131Part008SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block131Part008] using hcert

def TailChunk001Sub000Block131Part009SupportExplicit : Finset ℕ :=
  ([21895] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block131Part009 : ℚ :=
  (142590442691 : ℚ) / 1593506989670400000

def SurrogateDiagonalTailChunk001Sub000Block131Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21895
    = surrogateDiagTailX0RatChunk001Sub000Block131Part009

theorem surrogateDiagonalTailChunk001Sub000Block131Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block131Part009CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block131Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block131Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block131Part009CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block131Part009SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block131Part009] using hcert

def TailChunk001Sub000Block131Part010SupportExplicit : Finset ℕ :=
  ([21898] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block131Part010 : ℚ :=
  (1873134390625 : ℚ) / 8980613841465329952

def SurrogateDiagonalTailChunk001Sub000Block131Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21898
    = surrogateDiagTailX0RatChunk001Sub000Block131Part010

theorem surrogateDiagonalTailChunk001Sub000Block131Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block131Part010CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block131Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block131Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block131Part010CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block131Part010SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block131Part010] using hcert

def TailChunk001Sub000Block131Part011SupportExplicit : Finset ℕ :=
  ([21899] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block131Part011 : ℚ :=
  (386157313109 : ℚ) / 7097455914413414400

def SurrogateDiagonalTailChunk001Sub000Block131Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21899
    = surrogateDiagTailX0RatChunk001Sub000Block131Part011

theorem surrogateDiagonalTailChunk001Sub000Block131Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block131Part011CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block131Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block131Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block131Part011CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block131Part011SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block131Part011] using hcert

def TailChunk001Sub000Block131Part012SupportExplicit : Finset ℕ :=
  ([21902] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block131Part012 : ℚ :=
  (2401357527525 : ℚ) / 10811572637175218176

def SurrogateDiagonalTailChunk001Sub000Block131Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21902
    = surrogateDiagTailX0RatChunk001Sub000Block131Part012

theorem surrogateDiagonalTailChunk001Sub000Block131Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block131Part012CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block131Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block131Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block131Part012CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block131Part012SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block131Part012] using hcert

def TailChunk001Sub000Block131Part013SupportExplicit : Finset ℕ :=
  ([21905] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block131Part013 : ℚ :=
  (18506509025 : ℚ) / 188816919644602368

def SurrogateDiagonalTailChunk001Sub000Block131Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21905
    = surrogateDiagTailX0RatChunk001Sub000Block131Part013

theorem surrogateDiagonalTailChunk001Sub000Block131Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block131Part013CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block131Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block131Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block131Part013CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block131Part013SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block131Part013] using hcert

def TailChunk001Sub000Block131Part014SupportExplicit : Finset ℕ :=
  ([21907] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block131Part014 : ℚ :=
  (27129974402875 : ℚ) / 462303089367038558208

def SurrogateDiagonalTailChunk001Sub000Block131Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21907
    = surrogateDiagTailX0RatChunk001Sub000Block131Part014

theorem surrogateDiagonalTailChunk001Sub000Block131Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block131Part014CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block131Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block131Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block131Part014CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block131Part014SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block131Part014] using hcert

def TailChunk001Sub000Block131Part015SupportExplicit : Finset ℕ :=
  ([21909] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block131Part015 : ℚ :=
  (237143191625 : ℚ) / 1912598654124736512

def SurrogateDiagonalTailChunk001Sub000Block131Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21909
    = surrogateDiagTailX0RatChunk001Sub000Block131Part015

theorem surrogateDiagonalTailChunk001Sub000Block131Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block131Part015CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block131Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block131Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block131Part015CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block131Part015SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block131Part015] using hcert

def TailChunk001Sub000Block131Part016SupportExplicit : Finset ℕ :=
  ([21910] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block131Part016 : ℚ :=
  (124961736875 : ℚ) / 245663267217997824

def SurrogateDiagonalTailChunk001Sub000Block131Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21910
    = surrogateDiagTailX0RatChunk001Sub000Block131Part016

theorem surrogateDiagonalTailChunk001Sub000Block131Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block131Part016CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block131Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block131Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block131Part016CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block131Part016SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block131Part016] using hcert

def TailChunk001Sub000Block131Part017SupportExplicit : Finset ℕ :=
  ([21911] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block131Part017 : ℚ :=
  (12002298025 : ℚ) / 230492267549272722

def SurrogateDiagonalTailChunk001Sub000Block131Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21911
    = surrogateDiagTailX0RatChunk001Sub000Block131Part017

theorem surrogateDiagonalTailChunk001Sub000Block131Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block131Part017CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block131Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block131Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block131Part017CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block131Part017SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block131Part017] using hcert

def TailChunk001Sub000Block131Part018SupportExplicit : Finset ℕ :=
  ([21913] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block131Part018 : ℚ :=
  (1678812412975 : ℚ) / 28187091089152278528

def SurrogateDiagonalTailChunk001Sub000Block131Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21913
    = surrogateDiagTailX0RatChunk001Sub000Block131Part018

theorem surrogateDiagonalTailChunk001Sub000Block131Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block131Part018CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block131Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block131Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block131Part018CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block131Part018SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block131Part018] using hcert

def TailChunk001Sub000Block131Part019SupportExplicit : Finset ℕ :=
  ([21914] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block131Part019 : ℚ :=
  (1875872640625 : ℚ) / 9006892138006516512

def SurrogateDiagonalTailChunk001Sub000Block131Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21914
    = surrogateDiagTailX0RatChunk001Sub000Block131Part019

theorem surrogateDiagonalTailChunk001Sub000Block131Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block131Part019CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block131Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block131Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block131Part019CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block131Part019SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block131Part019] using hcert

def TailChunk001Sub000Block131Part020SupportExplicit : Finset ℕ :=
  ([21917] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block131Part020 : ℚ :=
  (93461812381 : ℚ) / 1166633280000000000

def SurrogateDiagonalTailChunk001Sub000Block131Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21917
    = surrogateDiagTailX0RatChunk001Sub000Block131Part020

theorem surrogateDiagonalTailChunk001Sub000Block131Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block131Part020CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block131Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block131Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block131Part020CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block131Part020SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block131Part020] using hcert

def TailChunk001Sub000Block131Part021SupportExplicit : Finset ℕ :=
  ([21918] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block131Part021 : ℚ :=
  (49172274677 : ℚ) / 67989631559270400

def SurrogateDiagonalTailChunk001Sub000Block131Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21918
    = surrogateDiagTailX0RatChunk001Sub000Block131Part021

theorem surrogateDiagonalTailChunk001Sub000Block131Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block131Part021CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block131Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block131Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block131Part021CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block131Part021SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block131Part021] using hcert

def TailChunk001Sub000Block131Part022SupportExplicit : Finset ℕ :=
  ([21919] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block131Part022 : ℚ :=
  (114260132375 : ℚ) / 1988153947085881344

def SurrogateDiagonalTailChunk001Sub000Block131Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21919
    = surrogateDiagTailX0RatChunk001Sub000Block131Part022

theorem surrogateDiagonalTailChunk001Sub000Block131Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block131Part022CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block131Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block131Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block131Part022CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block131Part022SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block131Part022] using hcert

def TailChunk001Sub000Block131Part023SupportExplicit : Finset ℕ :=
  ([21921] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block131Part023 : ℚ :=
  (13345033269325 : ℚ) / 113989674374139427968

def SurrogateDiagonalTailChunk001Sub000Block131Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21921
    = surrogateDiagTailX0RatChunk001Sub000Block131Part023

theorem surrogateDiagonalTailChunk001Sub000Block131Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block131Part023CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block131Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block131Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block131Part023CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block131Part023SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block131Part023] using hcert

def TailChunk001Sub000Block131Part024SupportExplicit : Finset ℕ :=
  ([21922] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block131Part024 : ℚ :=
  (65094242575 : ℚ) / 298377354500112384

def SurrogateDiagonalTailChunk001Sub000Block131Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21922
    = surrogateDiagTailX0RatChunk001Sub000Block131Part024

theorem surrogateDiagonalTailChunk001Sub000Block131Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block131Part024CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block131Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block131Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block131Part024CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block131Part024SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block131Part024] using hcert

def surrogateDiagonalTailChunk001Sub000Block131HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block131Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block131Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block131Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block131Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block131Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block131Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block131Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block131Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block131Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block131Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block131Head : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block131Part000
    + surrogateDiagTailX0RatChunk001Sub000Block131Part001
    + surrogateDiagTailX0RatChunk001Sub000Block131Part002
    + surrogateDiagTailX0RatChunk001Sub000Block131Part003
    + surrogateDiagTailX0RatChunk001Sub000Block131Part004
    + surrogateDiagTailX0RatChunk001Sub000Block131Part005
    + surrogateDiagTailX0RatChunk001Sub000Block131Part006
    + surrogateDiagTailX0RatChunk001Sub000Block131Part007
    + surrogateDiagTailX0RatChunk001Sub000Block131Part008
    + surrogateDiagTailX0RatChunk001Sub000Block131Part009

def surrogateDiagonalTailChunk001Sub000Block131MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block131Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block131Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block131Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block131Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block131Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block131Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block131Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block131Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block131Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block131Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block131Mid : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block131Part010
    + surrogateDiagTailX0RatChunk001Sub000Block131Part011
    + surrogateDiagTailX0RatChunk001Sub000Block131Part012
    + surrogateDiagTailX0RatChunk001Sub000Block131Part013
    + surrogateDiagTailX0RatChunk001Sub000Block131Part014
    + surrogateDiagTailX0RatChunk001Sub000Block131Part015
    + surrogateDiagTailX0RatChunk001Sub000Block131Part016
    + surrogateDiagTailX0RatChunk001Sub000Block131Part017
    + surrogateDiagTailX0RatChunk001Sub000Block131Part018
    + surrogateDiagTailX0RatChunk001Sub000Block131Part019

def surrogateDiagonalTailChunk001Sub000Block131TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block131Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block131Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block131Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block131Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block131Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block131Tail : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block131Part020
    + surrogateDiagTailX0RatChunk001Sub000Block131Part021
    + surrogateDiagTailX0RatChunk001Sub000Block131Part022
    + surrogateDiagTailX0RatChunk001Sub000Block131Part023
    + surrogateDiagTailX0RatChunk001Sub000Block131Part024

def surrogateDiagonalTailChunk001Sub000Block131Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk001Sub000Block131HeadSum X0
    + surrogateDiagonalTailChunk001Sub000Block131MidSum X0
    + surrogateDiagonalTailChunk001Sub000Block131TailSum X0

def surrogateDiagTailX0RatChunk001Sub000Block131 : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block131Part000
    + surrogateDiagTailX0RatChunk001Sub000Block131Part001
    + surrogateDiagTailX0RatChunk001Sub000Block131Part002
    + surrogateDiagTailX0RatChunk001Sub000Block131Part003
    + surrogateDiagTailX0RatChunk001Sub000Block131Part004
    + surrogateDiagTailX0RatChunk001Sub000Block131Part005
    + surrogateDiagTailX0RatChunk001Sub000Block131Part006
    + surrogateDiagTailX0RatChunk001Sub000Block131Part007
    + surrogateDiagTailX0RatChunk001Sub000Block131Part008
    + surrogateDiagTailX0RatChunk001Sub000Block131Part009
    + surrogateDiagTailX0RatChunk001Sub000Block131Part010
    + surrogateDiagTailX0RatChunk001Sub000Block131Part011
    + surrogateDiagTailX0RatChunk001Sub000Block131Part012
    + surrogateDiagTailX0RatChunk001Sub000Block131Part013
    + surrogateDiagTailX0RatChunk001Sub000Block131Part014
    + surrogateDiagTailX0RatChunk001Sub000Block131Part015
    + surrogateDiagTailX0RatChunk001Sub000Block131Part016
    + surrogateDiagTailX0RatChunk001Sub000Block131Part017
    + surrogateDiagTailX0RatChunk001Sub000Block131Part018
    + surrogateDiagTailX0RatChunk001Sub000Block131Part019
    + surrogateDiagTailX0RatChunk001Sub000Block131Part020
    + surrogateDiagTailX0RatChunk001Sub000Block131Part021
    + surrogateDiagTailX0RatChunk001Sub000Block131Part022
    + surrogateDiagTailX0RatChunk001Sub000Block131Part023
    + surrogateDiagTailX0RatChunk001Sub000Block131Part024

theorem surrogateDiagTailX0RatChunk001Sub000Block131_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk001Sub000Block131Head + surrogateDiagTailX0RatChunk001Sub000Block131Mid + surrogateDiagTailX0RatChunk001Sub000Block131Tail =
      surrogateDiagTailX0RatChunk001Sub000Block131 := by
  unfold surrogateDiagTailX0RatChunk001Sub000Block131Head surrogateDiagTailX0RatChunk001Sub000Block131Mid surrogateDiagTailX0RatChunk001Sub000Block131Tail surrogateDiagTailX0RatChunk001Sub000Block131
  ring

def SurrogateDiagonalTailChunk001Sub000Block131HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block131HeadSum X0 = surrogateDiagTailX0RatChunk001Sub000Block131Head

def SurrogateDiagonalTailChunk001Sub000Block131MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block131MidSum X0 = surrogateDiagTailX0RatChunk001Sub000Block131Mid

def SurrogateDiagonalTailChunk001Sub000Block131TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block131TailSum X0 = surrogateDiagTailX0RatChunk001Sub000Block131Tail

theorem surrogateDiagonalTailChunk001Sub000Block131_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk001Sub000Block131HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk001Sub000Block131MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk001Sub000Block131TailCertificateAt X0) :
    surrogateDiagonalTailChunk001Sub000Block131Sum X0 = surrogateDiagTailX0RatChunk001Sub000Block131 := by
  unfold SurrogateDiagonalTailChunk001Sub000Block131HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk001Sub000Block131MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk001Sub000Block131TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk001Sub000Block131Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk001Sub000Block131_eq_head_add_mid_add_tail

/-- Block 132 covers tail-support indices [13300,13325) and q from 21923 to 21962. -/

def TailChunk001Sub000Block132Part000SupportExplicit : Finset ℕ :=
  ([21923] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block132Part000 : ℚ :=
  (253014133609 : ℚ) / 3937170253619404800

def SurrogateDiagonalTailChunk001Sub000Block132Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21923
    = surrogateDiagTailX0RatChunk001Sub000Block132Part000

theorem surrogateDiagonalTailChunk001Sub000Block132Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block132Part000CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block132Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block132Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block132Part000CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block132Part000SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block132Part000] using hcert

def TailChunk001Sub000Block132Part001SupportExplicit : Finset ℕ :=
  ([21926] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block132Part001 : ℚ :=
  (6890914377175 : ℚ) / 28893943085439909888

def SurrogateDiagonalTailChunk001Sub000Block132Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21926
    = surrogateDiagTailX0RatChunk001Sub000Block132Part001

theorem surrogateDiagonalTailChunk001Sub000Block132Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block132Part001CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block132Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block132Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block132Part001CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block132Part001SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block132Part001] using hcert

def TailChunk001Sub000Block132Part002SupportExplicit : Finset ℕ :=
  ([21927] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block132Part002 : ℚ :=
  (13352340269125 : ℚ) / 114114543237558355968

def SurrogateDiagonalTailChunk001Sub000Block132Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21927
    = surrogateDiagTailX0RatChunk001Sub000Block132Part002

theorem surrogateDiagonalTailChunk001Sub000Block132Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block132Part002CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block132Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block132Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block132Part002CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block132Part002SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block132Part002] using hcert

def TailChunk001Sub000Block132Part003SupportExplicit : Finset ℕ :=
  ([21929] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block132Part003 : ℚ :=
  (7513766265625 : ℚ) / 144531648997845791232

def SurrogateDiagonalTailChunk001Sub000Block132Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21929
    = surrogateDiagTailX0RatChunk001Sub000Block132Part003

theorem surrogateDiagonalTailChunk001Sub000Block132Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block132Part003CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block132Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block132Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block132Part003CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block132Part003SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block132Part003] using hcert

def TailChunk001Sub000Block132Part004SupportExplicit : Finset ℕ :=
  ([21930] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block132Part004 : ℚ :=
  (2696187635875 : ℚ) / 2088641481500786688

def SurrogateDiagonalTailChunk001Sub000Block132Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21930
    = surrogateDiagTailX0RatChunk001Sub000Block132Part004

theorem surrogateDiagonalTailChunk001Sub000Block132Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block132Part004CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block132Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block132Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block132Part004CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block132Part004SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block132Part004] using hcert

def TailChunk001Sub000Block132Part005SupportExplicit : Finset ℕ :=
  ([21931] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block132Part005 : ℚ :=
  (78096879793 : ℚ) / 891788366834565120

def SurrogateDiagonalTailChunk001Sub000Block132Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21931
    = surrogateDiagTailX0RatChunk001Sub000Block132Part005

theorem surrogateDiagonalTailChunk001Sub000Block132Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block132Part005CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block132Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block132Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block132Part005CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block132Part005SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block132Part005] using hcert

def TailChunk001Sub000Block132Part006SupportExplicit : Finset ℕ :=
  ([21934] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block132Part006 : ℚ :=
  (258082756561 : ℚ) / 984292563404851200

def SurrogateDiagonalTailChunk001Sub000Block132Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21934
    = surrogateDiagTailX0RatChunk001Sub000Block132Part006

theorem surrogateDiagonalTailChunk001Sub000Block132Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block132Part006CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block132Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block132Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block132Part006CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block132Part006SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block132Part006] using hcert

def TailChunk001Sub000Block132Part007SupportExplicit : Finset ℕ :=
  ([21935] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block132Part007 : ℚ :=
  (128442465249 : ℚ) / 1379237293142835200

def SurrogateDiagonalTailChunk001Sub000Block132Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21935
    = surrogateDiagTailX0RatChunk001Sub000Block132Part007

theorem surrogateDiagonalTailChunk001Sub000Block132Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block132Part007CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block132Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block132Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block132Part007CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block132Part007SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block132Part007] using hcert

def TailChunk001Sub000Block132Part008SupportExplicit : Finset ℕ :=
  ([21937] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block132Part008 : ℚ :=
  (7519249515625 : ℚ) / 144742682580532273152

def SurrogateDiagonalTailChunk001Sub000Block132Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21937
    = surrogateDiagTailX0RatChunk001Sub000Block132Part008

theorem surrogateDiagonalTailChunk001Sub000Block132Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block132Part008CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block132Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block132Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block132Part008CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block132Part008SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block132Part008] using hcert

def TailChunk001Sub000Block132Part009SupportExplicit : Finset ℕ :=
  ([21938] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block132Part009 : ℚ :=
  (364180702375 : ℚ) / 1218088684047044808

def SurrogateDiagonalTailChunk001Sub000Block132Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21938
    = surrogateDiagTailX0RatChunk001Sub000Block132Part009

theorem surrogateDiagonalTailChunk001Sub000Block132Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block132Part009CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block132Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block132Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block132Part009CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block132Part009SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block132Part009] using hcert

def TailChunk001Sub000Block132Part010SupportExplicit : Finset ℕ :=
  ([21939] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block132Part010 : ℚ :=
  (11419152667 : ℚ) / 92424512002959360

def SurrogateDiagonalTailChunk001Sub000Block132Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21939
    = surrogateDiagTailX0RatChunk001Sub000Block132Part010

theorem surrogateDiagonalTailChunk001Sub000Block132Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block132Part010CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block132Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block132Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block132Part010CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block132Part010SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block132Part010] using hcert

def TailChunk001Sub000Block132Part011SupportExplicit : Finset ℕ :=
  ([21941] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block132Part011 : ℚ :=
  (28554080811325 : ℚ) / 515850301658961543168

def SurrogateDiagonalTailChunk001Sub000Block132Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21941
    = surrogateDiagTailX0RatChunk001Sub000Block132Part011

theorem surrogateDiagonalTailChunk001Sub000Block132Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block132Part011CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block132Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block132Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block132Part011CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block132Part011SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block132Part011] using hcert

def TailChunk001Sub000Block132Part012SupportExplicit : Finset ℕ :=
  ([21943] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block132Part012 : ℚ :=
  (7523363265625 : ℚ) / 144901109362899992562

def SurrogateDiagonalTailChunk001Sub000Block132Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21943
    = surrogateDiagTailX0RatChunk001Sub000Block132Part012

theorem surrogateDiagonalTailChunk001Sub000Block132Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block132Part012CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block132Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block132Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block132Part012CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block132Part012SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block132Part012] using hcert

def TailChunk001Sub000Block132Part013SupportExplicit : Finset ℕ :=
  ([21945] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block132Part013 : ℚ :=
  (38351242567 : ℚ) / 92894621545267200

def SurrogateDiagonalTailChunk001Sub000Block132Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21945
    = surrogateDiagTailX0RatChunk001Sub000Block132Part013

theorem surrogateDiagonalTailChunk001Sub000Block132Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block132Part013CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block132Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block132Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block132Part013CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block132Part013SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block132Part013] using hcert

def TailChunk001Sub000Block132Part014SupportExplicit : Finset ℕ :=
  ([21946] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block132Part014 : ℚ :=
  (1881355140625 : ℚ) / 9059621698731500832

def SurrogateDiagonalTailChunk001Sub000Block132Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21946
    = surrogateDiagTailX0RatChunk001Sub000Block132Part014

theorem surrogateDiagonalTailChunk001Sub000Block132Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block132Part014CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block132Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block132Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block132Part014CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block132Part014SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block132Part014] using hcert

def TailChunk001Sub000Block132Part015SupportExplicit : Finset ℕ :=
  ([21947] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block132Part015 : ℚ :=
  (269444671477 : ℚ) / 4538011903200460800

def SurrogateDiagonalTailChunk001Sub000Block132Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21947
    = surrogateDiagTailX0RatChunk001Sub000Block132Part015

theorem surrogateDiagonalTailChunk001Sub000Block132Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block132Part015CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block132Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block132Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block132Part015CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block132Part015SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block132Part015] using hcert

def TailChunk001Sub000Block132Part016SupportExplicit : Finset ℕ :=
  ([21949] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block132Part016 : ℚ :=
  (7217756947375 : ℚ) / 131990252914774309152

def SurrogateDiagonalTailChunk001Sub000Block132Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21949
    = surrogateDiagTailX0RatChunk001Sub000Block132Part016

theorem surrogateDiagonalTailChunk001Sub000Block132Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block132Part016CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block132Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block132Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block132Part016CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block132Part016SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block132Part016] using hcert

def TailChunk001Sub000Block132Part017SupportExplicit : Finset ℕ :=
  ([21953] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block132Part017 : ℚ :=
  (4032920532925 : ℚ) / 71721295604300611584

def SurrogateDiagonalTailChunk001Sub000Block132Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21953
    = surrogateDiagTailX0RatChunk001Sub000Block132Part017

theorem surrogateDiagonalTailChunk001Sub000Block132Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block132Part017CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block132Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block132Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block132Part017CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block132Part017SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block132Part017] using hcert

def TailChunk001Sub000Block132Part018SupportExplicit : Finset ℕ :=
  ([21954] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block132Part018 : ℚ :=
  (522855643025 : ℚ) / 895430038044049296

def SurrogateDiagonalTailChunk001Sub000Block132Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21954
    = surrogateDiagTailX0RatChunk001Sub000Block132Part018

theorem surrogateDiagonalTailChunk001Sub000Block132Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block132Part018CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block132Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block132Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block132Part018CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block132Part018SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block132Part018] using hcert

def TailChunk001Sub000Block132Part019SupportExplicit : Finset ℕ :=
  ([21955] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block132Part019 : ℚ :=
  (819191359069 : ℚ) / 9510095902148659200

def SurrogateDiagonalTailChunk001Sub000Block132Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21955
    = surrogateDiagTailX0RatChunk001Sub000Block132Part019

theorem surrogateDiagonalTailChunk001Sub000Block132Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block132Part019CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block132Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block132Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block132Part019CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block132Part019SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block132Part019] using hcert

def TailChunk001Sub000Block132Part020SupportExplicit : Finset ℕ :=
  ([21957] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block132Part020 : ℚ :=
  (283901243125 : ℚ) / 82759353237707194368

def SurrogateDiagonalTailChunk001Sub000Block132Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21957
    = surrogateDiagTailX0RatChunk001Sub000Block132Part020

theorem surrogateDiagonalTailChunk001Sub000Block132Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block132Part020CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block132Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block132Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block132Part020CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block132Part020SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block132Part020] using hcert

def TailChunk001Sub000Block132Part021SupportExplicit : Finset ℕ :=
  ([21958] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block132Part021 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block132Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21958
    = surrogateDiagTailX0RatChunk001Sub000Block132Part021

theorem surrogateDiagonalTailChunk001Sub000Block132Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block132Part021CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block132Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block132Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block132Part021CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block132Part021SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block132Part021] using hcert

def TailChunk001Sub000Block132Part022SupportExplicit : Finset ℕ :=
  ([21959] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block132Part022 : ℚ :=
  (616530906625 : ℚ) / 313426762317711802368

def SurrogateDiagonalTailChunk001Sub000Block132Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21959
    = surrogateDiagTailX0RatChunk001Sub000Block132Part022

theorem surrogateDiagonalTailChunk001Sub000Block132Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block132Part022CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block132Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block132Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block132Part022CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block132Part022SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block132Part022] using hcert

def TailChunk001Sub000Block132Part023SupportExplicit : Finset ℕ :=
  ([21961] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block132Part023 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block132Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21961
    = surrogateDiagTailX0RatChunk001Sub000Block132Part023

theorem surrogateDiagonalTailChunk001Sub000Block132Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block132Part023CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block132Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block132Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block132Part023CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block132Part023SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block132Part023] using hcert

def TailChunk001Sub000Block132Part024SupportExplicit : Finset ℕ :=
  ([21962] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block132Part024 : ℚ :=
  (2474612675 : ℚ) / 1243248234258386304

def SurrogateDiagonalTailChunk001Sub000Block132Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21962
    = surrogateDiagTailX0RatChunk001Sub000Block132Part024

theorem surrogateDiagonalTailChunk001Sub000Block132Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block132Part024CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block132Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block132Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block132Part024CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block132Part024SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block132Part024] using hcert

def surrogateDiagonalTailChunk001Sub000Block132HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block132Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block132Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block132Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block132Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block132Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block132Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block132Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block132Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block132Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block132Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block132Head : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block132Part000
    + surrogateDiagTailX0RatChunk001Sub000Block132Part001
    + surrogateDiagTailX0RatChunk001Sub000Block132Part002
    + surrogateDiagTailX0RatChunk001Sub000Block132Part003
    + surrogateDiagTailX0RatChunk001Sub000Block132Part004
    + surrogateDiagTailX0RatChunk001Sub000Block132Part005
    + surrogateDiagTailX0RatChunk001Sub000Block132Part006
    + surrogateDiagTailX0RatChunk001Sub000Block132Part007
    + surrogateDiagTailX0RatChunk001Sub000Block132Part008
    + surrogateDiagTailX0RatChunk001Sub000Block132Part009

def surrogateDiagonalTailChunk001Sub000Block132MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block132Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block132Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block132Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block132Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block132Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block132Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block132Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block132Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block132Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block132Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block132Mid : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block132Part010
    + surrogateDiagTailX0RatChunk001Sub000Block132Part011
    + surrogateDiagTailX0RatChunk001Sub000Block132Part012
    + surrogateDiagTailX0RatChunk001Sub000Block132Part013
    + surrogateDiagTailX0RatChunk001Sub000Block132Part014
    + surrogateDiagTailX0RatChunk001Sub000Block132Part015
    + surrogateDiagTailX0RatChunk001Sub000Block132Part016
    + surrogateDiagTailX0RatChunk001Sub000Block132Part017
    + surrogateDiagTailX0RatChunk001Sub000Block132Part018
    + surrogateDiagTailX0RatChunk001Sub000Block132Part019

def surrogateDiagonalTailChunk001Sub000Block132TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block132Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block132Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block132Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block132Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block132Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block132Tail : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block132Part020
    + surrogateDiagTailX0RatChunk001Sub000Block132Part021
    + surrogateDiagTailX0RatChunk001Sub000Block132Part022
    + surrogateDiagTailX0RatChunk001Sub000Block132Part023
    + surrogateDiagTailX0RatChunk001Sub000Block132Part024

def surrogateDiagonalTailChunk001Sub000Block132Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk001Sub000Block132HeadSum X0
    + surrogateDiagonalTailChunk001Sub000Block132MidSum X0
    + surrogateDiagonalTailChunk001Sub000Block132TailSum X0

def surrogateDiagTailX0RatChunk001Sub000Block132 : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block132Part000
    + surrogateDiagTailX0RatChunk001Sub000Block132Part001
    + surrogateDiagTailX0RatChunk001Sub000Block132Part002
    + surrogateDiagTailX0RatChunk001Sub000Block132Part003
    + surrogateDiagTailX0RatChunk001Sub000Block132Part004
    + surrogateDiagTailX0RatChunk001Sub000Block132Part005
    + surrogateDiagTailX0RatChunk001Sub000Block132Part006
    + surrogateDiagTailX0RatChunk001Sub000Block132Part007
    + surrogateDiagTailX0RatChunk001Sub000Block132Part008
    + surrogateDiagTailX0RatChunk001Sub000Block132Part009
    + surrogateDiagTailX0RatChunk001Sub000Block132Part010
    + surrogateDiagTailX0RatChunk001Sub000Block132Part011
    + surrogateDiagTailX0RatChunk001Sub000Block132Part012
    + surrogateDiagTailX0RatChunk001Sub000Block132Part013
    + surrogateDiagTailX0RatChunk001Sub000Block132Part014
    + surrogateDiagTailX0RatChunk001Sub000Block132Part015
    + surrogateDiagTailX0RatChunk001Sub000Block132Part016
    + surrogateDiagTailX0RatChunk001Sub000Block132Part017
    + surrogateDiagTailX0RatChunk001Sub000Block132Part018
    + surrogateDiagTailX0RatChunk001Sub000Block132Part019
    + surrogateDiagTailX0RatChunk001Sub000Block132Part020
    + surrogateDiagTailX0RatChunk001Sub000Block132Part021
    + surrogateDiagTailX0RatChunk001Sub000Block132Part022
    + surrogateDiagTailX0RatChunk001Sub000Block132Part023
    + surrogateDiagTailX0RatChunk001Sub000Block132Part024

theorem surrogateDiagTailX0RatChunk001Sub000Block132_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk001Sub000Block132Head + surrogateDiagTailX0RatChunk001Sub000Block132Mid + surrogateDiagTailX0RatChunk001Sub000Block132Tail =
      surrogateDiagTailX0RatChunk001Sub000Block132 := by
  unfold surrogateDiagTailX0RatChunk001Sub000Block132Head surrogateDiagTailX0RatChunk001Sub000Block132Mid surrogateDiagTailX0RatChunk001Sub000Block132Tail surrogateDiagTailX0RatChunk001Sub000Block132
  ring

def SurrogateDiagonalTailChunk001Sub000Block132HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block132HeadSum X0 = surrogateDiagTailX0RatChunk001Sub000Block132Head

def SurrogateDiagonalTailChunk001Sub000Block132MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block132MidSum X0 = surrogateDiagTailX0RatChunk001Sub000Block132Mid

def SurrogateDiagonalTailChunk001Sub000Block132TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block132TailSum X0 = surrogateDiagTailX0RatChunk001Sub000Block132Tail

theorem surrogateDiagonalTailChunk001Sub000Block132_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk001Sub000Block132HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk001Sub000Block132MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk001Sub000Block132TailCertificateAt X0) :
    surrogateDiagonalTailChunk001Sub000Block132Sum X0 = surrogateDiagTailX0RatChunk001Sub000Block132 := by
  unfold SurrogateDiagonalTailChunk001Sub000Block132HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk001Sub000Block132MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk001Sub000Block132TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk001Sub000Block132Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk001Sub000Block132_eq_head_add_mid_add_tail

/-- Block 133 covers tail-support indices [13325,13350) and q from 21963 to 22003. -/

def TailChunk001Sub000Block133Part000SupportExplicit : Finset ℕ :=
  ([21963] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block133Part000 : ℚ :=
  (1667 : ℚ) / 306247849574400

def SurrogateDiagonalTailChunk001Sub000Block133Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21963
    = surrogateDiagTailX0RatChunk001Sub000Block133Part000

theorem surrogateDiagonalTailChunk001Sub000Block133Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block133Part000CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block133Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block133Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block133Part000CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block133Part000SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block133Part000] using hcert

def TailChunk001Sub000Block133Part001SupportExplicit : Finset ℕ :=
  ([21965] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block133Part001 : ℚ :=
  (53815216567 : ℚ) / 7816852959036211200

def SurrogateDiagonalTailChunk001Sub000Block133Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21965
    = surrogateDiagTailX0RatChunk001Sub000Block133Part001

theorem surrogateDiagonalTailChunk001Sub000Block133Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block133Part001CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block133Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block133Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block133Part001CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block133Part001SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block133Part001] using hcert

def TailChunk001Sub000Block133Part002SupportExplicit : Finset ℕ :=
  ([21966] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block133Part002 : ℚ :=
  (453181272875 : ℚ) / 1924880883432367104

def SurrogateDiagonalTailChunk001Sub000Block133Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21966
    = surrogateDiagTailX0RatChunk001Sub000Block133Part002

theorem surrogateDiagonalTailChunk001Sub000Block133Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block133Part002CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block133Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block133Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block133Part002CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block133Part002SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block133Part002] using hcert

def TailChunk001Sub000Block133Part003SupportExplicit : Finset ℕ :=
  ([21967] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block133Part003 : ℚ :=
  (5010301759 : ℚ) / 3968889491238412800

def SurrogateDiagonalTailChunk001Sub000Block133Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21967
    = surrogateDiagTailX0RatChunk001Sub000Block133Part003

theorem surrogateDiagonalTailChunk001Sub000Block133Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block133Part003CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block133Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block133Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block133Part003CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block133Part003SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block133Part003] using hcert

def TailChunk001Sub000Block133Part004SupportExplicit : Finset ℕ :=
  ([21971] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block133Part004 : ℚ :=
  (23084237725 : ℚ) / 137899545772863877632

def SurrogateDiagonalTailChunk001Sub000Block133Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21971
    = surrogateDiagTailX0RatChunk001Sub000Block133Part004

theorem surrogateDiagonalTailChunk001Sub000Block133Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block133Part004CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block133Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block133Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block133Part004CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block133Part004SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block133Part004] using hcert

def TailChunk001Sub000Block133Part005SupportExplicit : Finset ℕ :=
  ([21973] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block133Part005 : ℚ :=
  (195754404175 : ℚ) / 67748395847794163712

def SurrogateDiagonalTailChunk001Sub000Block133Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21973
    = surrogateDiagTailX0RatChunk001Sub000Block133Part005

theorem surrogateDiagonalTailChunk001Sub000Block133Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block133Part005CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block133Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block133Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block133Part005CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block133Part005SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block133Part005] using hcert

def TailChunk001Sub000Block133Part006SupportExplicit : Finset ℕ :=
  ([21974] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block133Part006 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block133Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21974
    = surrogateDiagTailX0RatChunk001Sub000Block133Part006

theorem surrogateDiagonalTailChunk001Sub000Block133Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block133Part006CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block133Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block133Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block133Part006CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block133Part006SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block133Part006] using hcert

def TailChunk001Sub000Block133Part007SupportExplicit : Finset ℕ :=
  ([21977] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block133Part007 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block133Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21977
    = surrogateDiagTailX0RatChunk001Sub000Block133Part007

theorem surrogateDiagonalTailChunk001Sub000Block133Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block133Part007CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block133Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block133Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block133Part007CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block133Part007SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block133Part007] using hcert

def TailChunk001Sub000Block133Part008SupportExplicit : Finset ℕ :=
  ([21979] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block133Part008 : ℚ :=
  (507556427 : ℚ) / 1130921328669926400

def SurrogateDiagonalTailChunk001Sub000Block133Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21979
    = surrogateDiagTailX0RatChunk001Sub000Block133Part008

theorem surrogateDiagonalTailChunk001Sub000Block133Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block133Part008CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block133Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block133Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block133Part008CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block133Part008SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block133Part008] using hcert

def TailChunk001Sub000Block133Part009SupportExplicit : Finset ℕ :=
  ([21981] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block133Part009 : ℚ :=
  (11033660929 : ℚ) / 3585589651911475200

def SurrogateDiagonalTailChunk001Sub000Block133Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21981
    = surrogateDiagTailX0RatChunk001Sub000Block133Part009

theorem surrogateDiagonalTailChunk001Sub000Block133Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block133Part009CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block133Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block133Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block133Part009CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block133Part009SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block133Part009] using hcert

def TailChunk001Sub000Block133Part010SupportExplicit : Finset ℕ :=
  ([21982] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block133Part010 : ℚ :=
  (185335375 : ℚ) / 46693551825716544

def SurrogateDiagonalTailChunk001Sub000Block133Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21982
    = surrogateDiagTailX0RatChunk001Sub000Block133Part010

theorem surrogateDiagonalTailChunk001Sub000Block133Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block133Part010CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block133Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block133Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block133Part010CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block133Part010SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block133Part010] using hcert

def TailChunk001Sub000Block133Part011SupportExplicit : Finset ℕ :=
  ([21983] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block133Part011 : ℚ :=
  (840038495125 : ℚ) / 326416836970621698048

def SurrogateDiagonalTailChunk001Sub000Block133Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21983
    = surrogateDiagTailX0RatChunk001Sub000Block133Part011

theorem surrogateDiagonalTailChunk001Sub000Block133Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block133Part011CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block133Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block133Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block133Part011CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block133Part011SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block133Part011] using hcert

def TailChunk001Sub000Block133Part012SupportExplicit : Finset ℕ :=
  ([21985] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block133Part012 : ℚ :=
  (403017212625 : ℚ) / 79684950002462457856

def SurrogateDiagonalTailChunk001Sub000Block133Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21985
    = surrogateDiagTailX0RatChunk001Sub000Block133Part012

theorem surrogateDiagonalTailChunk001Sub000Block133Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block133Part012CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block133Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block133Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block133Part012CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block133Part012SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block133Part012] using hcert

def TailChunk001Sub000Block133Part013SupportExplicit : Finset ℕ :=
  ([21986] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block133Part013 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block133Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21986
    = surrogateDiagTailX0RatChunk001Sub000Block133Part013

theorem surrogateDiagonalTailChunk001Sub000Block133Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block133Part013CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block133Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block133Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block133Part013CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block133Part013SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block133Part013] using hcert

def TailChunk001Sub000Block133Part014SupportExplicit : Finset ℕ :=
  ([21989] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block133Part014 : ℚ :=
  (418357063 : ℚ) / 332068399066733400

def SurrogateDiagonalTailChunk001Sub000Block133Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21989
    = surrogateDiagTailX0RatChunk001Sub000Block133Part014

theorem surrogateDiagonalTailChunk001Sub000Block133Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block133Part014CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block133Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block133Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block133Part014CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block133Part014SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block133Part014] using hcert

def TailChunk001Sub000Block133Part015SupportExplicit : Finset ℕ :=
  ([21990] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block133Part015 : ℚ :=
  (906715789975 : ℚ) / 2940567351785422848

def SurrogateDiagonalTailChunk001Sub000Block133Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21990
    = surrogateDiagTailX0RatChunk001Sub000Block133Part015

theorem surrogateDiagonalTailChunk001Sub000Block133Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block133Part015CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block133Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block133Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block133Part015CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block133Part015SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block133Part015] using hcert

def TailChunk001Sub000Block133Part016SupportExplicit : Finset ℕ :=
  ([21991] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block133Part016 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block133Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21991
    = surrogateDiagTailX0RatChunk001Sub000Block133Part016

theorem surrogateDiagonalTailChunk001Sub000Block133Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block133Part016CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block133Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block133Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block133Part016CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block133Part016SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block133Part016] using hcert

def TailChunk001Sub000Block133Part017SupportExplicit : Finset ℕ :=
  ([21993] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block133Part017 : ℚ :=
  (5001 : ℚ) / 923774302467200

def SurrogateDiagonalTailChunk001Sub000Block133Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21993
    = surrogateDiagTailX0RatChunk001Sub000Block133Part017

theorem surrogateDiagonalTailChunk001Sub000Block133Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block133Part017CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block133Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block133Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block133Part017CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block133Part017SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block133Part017] using hcert

def TailChunk001Sub000Block133Part018SupportExplicit : Finset ℕ :=
  ([21994] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block133Part018 : ℚ :=
  (1030796683 : ℚ) / 43754019526094400

def SurrogateDiagonalTailChunk001Sub000Block133Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21994
    = surrogateDiagTailX0RatChunk001Sub000Block133Part018

theorem surrogateDiagonalTailChunk001Sub000Block133Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block133Part018CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block133Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block133Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block133Part018CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block133Part018SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block133Part018] using hcert

def TailChunk001Sub000Block133Part019SupportExplicit : Finset ℕ :=
  ([21995] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block133Part019 : ℚ :=
  (521665875 : ℚ) / 84779534423154688

def SurrogateDiagonalTailChunk001Sub000Block133Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21995
    = surrogateDiagTailX0RatChunk001Sub000Block133Part019

theorem surrogateDiagonalTailChunk001Sub000Block133Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block133Part019CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block133Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block133Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block133Part019CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block133Part019SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block133Part019] using hcert

def TailChunk001Sub000Block133Part020SupportExplicit : Finset ℕ :=
  ([21997] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block133Part020 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block133Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21997
    = surrogateDiagTailX0RatChunk001Sub000Block133Part020

theorem surrogateDiagonalTailChunk001Sub000Block133Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block133Part020CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block133Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block133Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block133Part020CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block133Part020SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block133Part020] using hcert

def TailChunk001Sub000Block133Part021SupportExplicit : Finset ℕ :=
  ([21998] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block133Part021 : ℚ :=
  (11229679975 : ℚ) / 1502046094905311232

def SurrogateDiagonalTailChunk001Sub000Block133Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21998
    = surrogateDiagTailX0RatChunk001Sub000Block133Part021

theorem surrogateDiagonalTailChunk001Sub000Block133Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block133Part021CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block133Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block133Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block133Part021CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block133Part021SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block133Part021] using hcert

def TailChunk001Sub000Block133Part022SupportExplicit : Finset ℕ :=
  ([21999] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block133Part022 : ℚ :=
  (41675 : ℚ) / 7706524393691136

def SurrogateDiagonalTailChunk001Sub000Block133Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21999
    = surrogateDiagTailX0RatChunk001Sub000Block133Part022

theorem surrogateDiagonalTailChunk001Sub000Block133Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block133Part022CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block133Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block133Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block133Part022CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block133Part022SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block133Part022] using hcert

def TailChunk001Sub000Block133Part023SupportExplicit : Finset ℕ :=
  ([22002] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block133Part023 : ℚ :=
  (32501180125 : ℚ) / 211386872138563584

def SurrogateDiagonalTailChunk001Sub000Block133Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22002
    = surrogateDiagTailX0RatChunk001Sub000Block133Part023

theorem surrogateDiagonalTailChunk001Sub000Block133Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block133Part023CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block133Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block133Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block133Part023CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block133Part023SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block133Part023] using hcert

def TailChunk001Sub000Block133Part024SupportExplicit : Finset ℕ :=
  ([22003] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block133Part024 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block133Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22003
    = surrogateDiagTailX0RatChunk001Sub000Block133Part024

theorem surrogateDiagonalTailChunk001Sub000Block133Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block133Part024CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block133Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block133Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block133Part024CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block133Part024SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block133Part024] using hcert

def surrogateDiagonalTailChunk001Sub000Block133HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block133Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block133Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block133Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block133Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block133Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block133Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block133Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block133Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block133Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block133Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block133Head : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block133Part000
    + surrogateDiagTailX0RatChunk001Sub000Block133Part001
    + surrogateDiagTailX0RatChunk001Sub000Block133Part002
    + surrogateDiagTailX0RatChunk001Sub000Block133Part003
    + surrogateDiagTailX0RatChunk001Sub000Block133Part004
    + surrogateDiagTailX0RatChunk001Sub000Block133Part005
    + surrogateDiagTailX0RatChunk001Sub000Block133Part006
    + surrogateDiagTailX0RatChunk001Sub000Block133Part007
    + surrogateDiagTailX0RatChunk001Sub000Block133Part008
    + surrogateDiagTailX0RatChunk001Sub000Block133Part009

def surrogateDiagonalTailChunk001Sub000Block133MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block133Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block133Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block133Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block133Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block133Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block133Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block133Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block133Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block133Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block133Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block133Mid : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block133Part010
    + surrogateDiagTailX0RatChunk001Sub000Block133Part011
    + surrogateDiagTailX0RatChunk001Sub000Block133Part012
    + surrogateDiagTailX0RatChunk001Sub000Block133Part013
    + surrogateDiagTailX0RatChunk001Sub000Block133Part014
    + surrogateDiagTailX0RatChunk001Sub000Block133Part015
    + surrogateDiagTailX0RatChunk001Sub000Block133Part016
    + surrogateDiagTailX0RatChunk001Sub000Block133Part017
    + surrogateDiagTailX0RatChunk001Sub000Block133Part018
    + surrogateDiagTailX0RatChunk001Sub000Block133Part019

def surrogateDiagonalTailChunk001Sub000Block133TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block133Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block133Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block133Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block133Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block133Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block133Tail : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block133Part020
    + surrogateDiagTailX0RatChunk001Sub000Block133Part021
    + surrogateDiagTailX0RatChunk001Sub000Block133Part022
    + surrogateDiagTailX0RatChunk001Sub000Block133Part023
    + surrogateDiagTailX0RatChunk001Sub000Block133Part024

def surrogateDiagonalTailChunk001Sub000Block133Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk001Sub000Block133HeadSum X0
    + surrogateDiagonalTailChunk001Sub000Block133MidSum X0
    + surrogateDiagonalTailChunk001Sub000Block133TailSum X0

def surrogateDiagTailX0RatChunk001Sub000Block133 : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block133Part000
    + surrogateDiagTailX0RatChunk001Sub000Block133Part001
    + surrogateDiagTailX0RatChunk001Sub000Block133Part002
    + surrogateDiagTailX0RatChunk001Sub000Block133Part003
    + surrogateDiagTailX0RatChunk001Sub000Block133Part004
    + surrogateDiagTailX0RatChunk001Sub000Block133Part005
    + surrogateDiagTailX0RatChunk001Sub000Block133Part006
    + surrogateDiagTailX0RatChunk001Sub000Block133Part007
    + surrogateDiagTailX0RatChunk001Sub000Block133Part008
    + surrogateDiagTailX0RatChunk001Sub000Block133Part009
    + surrogateDiagTailX0RatChunk001Sub000Block133Part010
    + surrogateDiagTailX0RatChunk001Sub000Block133Part011
    + surrogateDiagTailX0RatChunk001Sub000Block133Part012
    + surrogateDiagTailX0RatChunk001Sub000Block133Part013
    + surrogateDiagTailX0RatChunk001Sub000Block133Part014
    + surrogateDiagTailX0RatChunk001Sub000Block133Part015
    + surrogateDiagTailX0RatChunk001Sub000Block133Part016
    + surrogateDiagTailX0RatChunk001Sub000Block133Part017
    + surrogateDiagTailX0RatChunk001Sub000Block133Part018
    + surrogateDiagTailX0RatChunk001Sub000Block133Part019
    + surrogateDiagTailX0RatChunk001Sub000Block133Part020
    + surrogateDiagTailX0RatChunk001Sub000Block133Part021
    + surrogateDiagTailX0RatChunk001Sub000Block133Part022
    + surrogateDiagTailX0RatChunk001Sub000Block133Part023
    + surrogateDiagTailX0RatChunk001Sub000Block133Part024

theorem surrogateDiagTailX0RatChunk001Sub000Block133_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk001Sub000Block133Head + surrogateDiagTailX0RatChunk001Sub000Block133Mid + surrogateDiagTailX0RatChunk001Sub000Block133Tail =
      surrogateDiagTailX0RatChunk001Sub000Block133 := by
  unfold surrogateDiagTailX0RatChunk001Sub000Block133Head surrogateDiagTailX0RatChunk001Sub000Block133Mid surrogateDiagTailX0RatChunk001Sub000Block133Tail surrogateDiagTailX0RatChunk001Sub000Block133
  ring

def SurrogateDiagonalTailChunk001Sub000Block133HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block133HeadSum X0 = surrogateDiagTailX0RatChunk001Sub000Block133Head

def SurrogateDiagonalTailChunk001Sub000Block133MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block133MidSum X0 = surrogateDiagTailX0RatChunk001Sub000Block133Mid

def SurrogateDiagonalTailChunk001Sub000Block133TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block133TailSum X0 = surrogateDiagTailX0RatChunk001Sub000Block133Tail

theorem surrogateDiagonalTailChunk001Sub000Block133_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk001Sub000Block133HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk001Sub000Block133MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk001Sub000Block133TailCertificateAt X0) :
    surrogateDiagonalTailChunk001Sub000Block133Sum X0 = surrogateDiagTailX0RatChunk001Sub000Block133 := by
  unfold SurrogateDiagonalTailChunk001Sub000Block133HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk001Sub000Block133MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk001Sub000Block133TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk001Sub000Block133Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk001Sub000Block133_eq_head_add_mid_add_tail

/-- Block 134 covers tail-support indices [13350,13375) and q from 22006 to 22046. -/

def TailChunk001Sub000Block134Part000SupportExplicit : Finset ℕ :=
  ([22006] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block134Part000 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block134Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22006
    = surrogateDiagTailX0RatChunk001Sub000Block134Part000

theorem surrogateDiagonalTailChunk001Sub000Block134Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block134Part000CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block134Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block134Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block134Part000CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block134Part000SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block134Part000] using hcert

def TailChunk001Sub000Block134Part001SupportExplicit : Finset ℕ :=
  ([22007] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block134Part001 : ℚ :=
  (43448400275 : ℚ) / 180629773748752029696

def SurrogateDiagonalTailChunk001Sub000Block134Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22007
    = surrogateDiagTailX0RatChunk001Sub000Block134Part001

theorem surrogateDiagonalTailChunk001Sub000Block134Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block134Part001CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block134Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block134Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block134Part001CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block134Part001SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block134Part001] using hcert

def TailChunk001Sub000Block134Part002SupportExplicit : Finset ℕ :=
  ([22009] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block134Part002 : ℚ :=
  (270162729725 : ℚ) / 212482556135920779264

def SurrogateDiagonalTailChunk001Sub000Block134Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22009
    = surrogateDiagTailX0RatChunk001Sub000Block134Part002

theorem surrogateDiagonalTailChunk001Sub000Block134Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block134Part002CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block134Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block134Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block134Part002CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block134Part002SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block134Part002] using hcert

def TailChunk001Sub000Block134Part003SupportExplicit : Finset ℕ :=
  ([22010] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block134Part003 : ℚ :=
  (26969875699 : ℚ) / 497970934272000000

def SurrogateDiagonalTailChunk001Sub000Block134Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22010
    = surrogateDiagTailX0RatChunk001Sub000Block134Part003

theorem surrogateDiagonalTailChunk001Sub000Block134Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block134Part003CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block134Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block134Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block134Part003CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block134Part003SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block134Part003] using hcert

def TailChunk001Sub000Block134Part004SupportExplicit : Finset ℕ :=
  ([22011] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block134Part004 : ℚ :=
  (2369339103 : ℚ) / 192020871076249600

def SurrogateDiagonalTailChunk001Sub000Block134Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22011
    = surrogateDiagTailX0RatChunk001Sub000Block134Part004

theorem surrogateDiagonalTailChunk001Sub000Block134Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block134Part004CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block134Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block134Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block134Part004CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block134Part004SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block134Part004] using hcert

def TailChunk001Sub000Block134Part005SupportExplicit : Finset ℕ :=
  ([22013] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block134Part005 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block134Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22013
    = surrogateDiagTailX0RatChunk001Sub000Block134Part005

theorem surrogateDiagonalTailChunk001Sub000Block134Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block134Part005CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block134Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block134Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block134Part005CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block134Part005SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block134Part005] using hcert

def TailChunk001Sub000Block134Part006SupportExplicit : Finset ℕ :=
  ([22015] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block134Part006 : ℚ :=
  (924225046325 : ℚ) / 45659564381929734144

def SurrogateDiagonalTailChunk001Sub000Block134Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22015
    = surrogateDiagTailX0RatChunk001Sub000Block134Part006

theorem surrogateDiagonalTailChunk001Sub000Block134Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block134Part006CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block134Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block134Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block134Part006CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block134Part006SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block134Part006] using hcert

def TailChunk001Sub000Block134Part007SupportExplicit : Finset ℕ :=
  ([22017] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block134Part007 : ℚ :=
  (891641367 : ℚ) / 685449646879539200

def SurrogateDiagonalTailChunk001Sub000Block134Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22017
    = surrogateDiagTailX0RatChunk001Sub000Block134Part007

theorem surrogateDiagonalTailChunk001Sub000Block134Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block134Part007CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block134Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block134Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block134Part007CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block134Part007SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block134Part007] using hcert

def TailChunk001Sub000Block134Part008SupportExplicit : Finset ℕ :=
  ([22018] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block134Part008 : ℚ :=
  (16195789 : ℚ) / 8504756611200000

def SurrogateDiagonalTailChunk001Sub000Block134Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22018
    = surrogateDiagTailX0RatChunk001Sub000Block134Part008

theorem surrogateDiagonalTailChunk001Sub000Block134Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block134Part008CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block134Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block134Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block134Part008CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block134Part008SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block134Part008] using hcert

def TailChunk001Sub000Block134Part009SupportExplicit : Finset ℕ :=
  ([22019] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block134Part009 : ℚ :=
  (33397464425 : ℚ) / 184681882567286194176

def SurrogateDiagonalTailChunk001Sub000Block134Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22019
    = surrogateDiagTailX0RatChunk001Sub000Block134Part009

theorem surrogateDiagonalTailChunk001Sub000Block134Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block134Part009CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block134Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block134Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block134Part009CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block134Part009SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block134Part009] using hcert

def TailChunk001Sub000Block134Part010SupportExplicit : Finset ℕ :=
  ([22026] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block134Part010 : ℚ :=
  (3369725383 : ℚ) / 29031607914150720

def SurrogateDiagonalTailChunk001Sub000Block134Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22026
    = surrogateDiagTailX0RatChunk001Sub000Block134Part010

theorem surrogateDiagonalTailChunk001Sub000Block134Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block134Part010CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block134Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block134Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block134Part010CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block134Part010SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block134Part010] using hcert

def TailChunk001Sub000Block134Part011SupportExplicit : Finset ℕ :=
  ([22027] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block134Part011 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block134Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22027
    = surrogateDiagTailX0RatChunk001Sub000Block134Part011

theorem surrogateDiagonalTailChunk001Sub000Block134Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block134Part011CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block134Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block134Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block134Part011CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block134Part011SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block134Part011] using hcert

def TailChunk001Sub000Block134Part012SupportExplicit : Finset ℕ :=
  ([22029] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block134Part012 : ℚ :=
  (758970198925 : ℚ) / 62545630330146521088

def SurrogateDiagonalTailChunk001Sub000Block134Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22029
    = surrogateDiagTailX0RatChunk001Sub000Block134Part012

theorem surrogateDiagonalTailChunk001Sub000Block134Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block134Part012CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block134Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block134Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block134Part012CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block134Part012SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block134Part012] using hcert

def TailChunk001Sub000Block134Part013SupportExplicit : Finset ℕ :=
  ([22030] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block134Part013 : ℚ :=
  (227509248925 : ℚ) / 3762496385673933312

def SurrogateDiagonalTailChunk001Sub000Block134Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22030
    = surrogateDiagTailX0RatChunk001Sub000Block134Part013

theorem surrogateDiagonalTailChunk001Sub000Block134Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block134Part013CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block134Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block134Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block134Part013CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block134Part013SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block134Part013] using hcert

def TailChunk001Sub000Block134Part014SupportExplicit : Finset ℕ :=
  ([22031] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block134Part014 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block134Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22031
    = surrogateDiagTailX0RatChunk001Sub000Block134Part014

theorem surrogateDiagonalTailChunk001Sub000Block134Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block134Part014CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block134Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block134Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block134Part014CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block134Part014SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block134Part014] using hcert

def TailChunk001Sub000Block134Part015SupportExplicit : Finset ℕ :=
  ([22033] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block134Part015 : ℚ :=
  (4310442349 : ℚ) / 2295329840461257600

def SurrogateDiagonalTailChunk001Sub000Block134Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22033
    = surrogateDiagTailX0RatChunk001Sub000Block134Part015

theorem surrogateDiagonalTailChunk001Sub000Block134Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block134Part015CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block134Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block134Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block134Part015CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block134Part015SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block134Part015] using hcert

def TailChunk001Sub000Block134Part016SupportExplicit : Finset ℕ :=
  ([22034] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block134Part016 : ℚ :=
  (27272064675 : ℚ) / 5096569116708648128

def SurrogateDiagonalTailChunk001Sub000Block134Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22034
    = surrogateDiagTailX0RatChunk001Sub000Block134Part016

theorem surrogateDiagonalTailChunk001Sub000Block134Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block134Part016CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block134Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block134Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block134Part016CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block134Part016SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block134Part016] using hcert

def TailChunk001Sub000Block134Part017SupportExplicit : Finset ℕ :=
  ([22035] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block134Part017 : ℚ :=
  (984783211675 : ℚ) / 33418263704012587008

def SurrogateDiagonalTailChunk001Sub000Block134Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22035
    = surrogateDiagTailX0RatChunk001Sub000Block134Part017

theorem surrogateDiagonalTailChunk001Sub000Block134Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block134Part017CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block134Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block134Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block134Part017CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block134Part017SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block134Part017] using hcert

def TailChunk001Sub000Block134Part018SupportExplicit : Finset ℕ :=
  ([22037] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block134Part018 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block134Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22037
    = surrogateDiagTailX0RatChunk001Sub000Block134Part018

theorem surrogateDiagonalTailChunk001Sub000Block134Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block134Part018CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block134Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block134Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block134Part018CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block134Part018SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block134Part018] using hcert

def TailChunk001Sub000Block134Part019SupportExplicit : Finset ℕ :=
  ([22038] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block134Part019 : ℚ :=
  (210837273925 : ℚ) / 1818433988925530112

def SurrogateDiagonalTailChunk001Sub000Block134Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22038
    = surrogateDiagTailX0RatChunk001Sub000Block134Part019

theorem surrogateDiagonalTailChunk001Sub000Block134Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block134Part019CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block134Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block134Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block134Part019CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block134Part019SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block134Part019] using hcert

def TailChunk001Sub000Block134Part020SupportExplicit : Finset ℕ :=
  ([22039] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block134Part020 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block134Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22039
    = surrogateDiagTailX0RatChunk001Sub000Block134Part020

theorem surrogateDiagonalTailChunk001Sub000Block134Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block134Part020CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block134Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block134Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block134Part020CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block134Part020SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block134Part020] using hcert

def TailChunk001Sub000Block134Part021SupportExplicit : Finset ℕ :=
  ([22042] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block134Part021 : ℚ :=
  (64228270075 : ℚ) / 34170474297389655168

def SurrogateDiagonalTailChunk001Sub000Block134Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22042
    = surrogateDiagTailX0RatChunk001Sub000Block134Part021

theorem surrogateDiagonalTailChunk001Sub000Block134Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block134Part021CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block134Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block134Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block134Part021CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block134Part021SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block134Part021] using hcert

def TailChunk001Sub000Block134Part022SupportExplicit : Finset ℕ :=
  ([22043] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block134Part022 : ℚ :=
  (28169793625 : ℚ) / 5735848765099026816

def SurrogateDiagonalTailChunk001Sub000Block134Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22043
    = surrogateDiagTailX0RatChunk001Sub000Block134Part022

theorem surrogateDiagonalTailChunk001Sub000Block134Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block134Part022CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block134Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block134Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block134Part022CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block134Part022SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block134Part022] using hcert

def TailChunk001Sub000Block134Part023SupportExplicit : Finset ℕ :=
  ([22045] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block134Part023 : ℚ :=
  (405218212125 : ℚ) / 80558600499530039296

def SurrogateDiagonalTailChunk001Sub000Block134Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22045
    = surrogateDiagTailX0RatChunk001Sub000Block134Part023

theorem surrogateDiagonalTailChunk001Sub000Block134Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block134Part023CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block134Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block134Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block134Part023CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block134Part023SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block134Part023] using hcert

def TailChunk001Sub000Block134Part024SupportExplicit : Finset ℕ :=
  ([22046] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block134Part024 : ℚ :=
  (1369049249 : ℚ) / 680380528896000000

def SurrogateDiagonalTailChunk001Sub000Block134Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22046
    = surrogateDiagTailX0RatChunk001Sub000Block134Part024

theorem surrogateDiagonalTailChunk001Sub000Block134Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block134Part024CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block134Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block134Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block134Part024CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block134Part024SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block134Part024] using hcert

def surrogateDiagonalTailChunk001Sub000Block134HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block134Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block134Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block134Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block134Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block134Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block134Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block134Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block134Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block134Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block134Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block134Head : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block134Part000
    + surrogateDiagTailX0RatChunk001Sub000Block134Part001
    + surrogateDiagTailX0RatChunk001Sub000Block134Part002
    + surrogateDiagTailX0RatChunk001Sub000Block134Part003
    + surrogateDiagTailX0RatChunk001Sub000Block134Part004
    + surrogateDiagTailX0RatChunk001Sub000Block134Part005
    + surrogateDiagTailX0RatChunk001Sub000Block134Part006
    + surrogateDiagTailX0RatChunk001Sub000Block134Part007
    + surrogateDiagTailX0RatChunk001Sub000Block134Part008
    + surrogateDiagTailX0RatChunk001Sub000Block134Part009

def surrogateDiagonalTailChunk001Sub000Block134MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block134Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block134Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block134Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block134Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block134Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block134Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block134Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block134Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block134Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block134Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block134Mid : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block134Part010
    + surrogateDiagTailX0RatChunk001Sub000Block134Part011
    + surrogateDiagTailX0RatChunk001Sub000Block134Part012
    + surrogateDiagTailX0RatChunk001Sub000Block134Part013
    + surrogateDiagTailX0RatChunk001Sub000Block134Part014
    + surrogateDiagTailX0RatChunk001Sub000Block134Part015
    + surrogateDiagTailX0RatChunk001Sub000Block134Part016
    + surrogateDiagTailX0RatChunk001Sub000Block134Part017
    + surrogateDiagTailX0RatChunk001Sub000Block134Part018
    + surrogateDiagTailX0RatChunk001Sub000Block134Part019

def surrogateDiagonalTailChunk001Sub000Block134TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block134Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block134Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block134Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block134Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block134Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block134Tail : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block134Part020
    + surrogateDiagTailX0RatChunk001Sub000Block134Part021
    + surrogateDiagTailX0RatChunk001Sub000Block134Part022
    + surrogateDiagTailX0RatChunk001Sub000Block134Part023
    + surrogateDiagTailX0RatChunk001Sub000Block134Part024

def surrogateDiagonalTailChunk001Sub000Block134Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk001Sub000Block134HeadSum X0
    + surrogateDiagonalTailChunk001Sub000Block134MidSum X0
    + surrogateDiagonalTailChunk001Sub000Block134TailSum X0

def surrogateDiagTailX0RatChunk001Sub000Block134 : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block134Part000
    + surrogateDiagTailX0RatChunk001Sub000Block134Part001
    + surrogateDiagTailX0RatChunk001Sub000Block134Part002
    + surrogateDiagTailX0RatChunk001Sub000Block134Part003
    + surrogateDiagTailX0RatChunk001Sub000Block134Part004
    + surrogateDiagTailX0RatChunk001Sub000Block134Part005
    + surrogateDiagTailX0RatChunk001Sub000Block134Part006
    + surrogateDiagTailX0RatChunk001Sub000Block134Part007
    + surrogateDiagTailX0RatChunk001Sub000Block134Part008
    + surrogateDiagTailX0RatChunk001Sub000Block134Part009
    + surrogateDiagTailX0RatChunk001Sub000Block134Part010
    + surrogateDiagTailX0RatChunk001Sub000Block134Part011
    + surrogateDiagTailX0RatChunk001Sub000Block134Part012
    + surrogateDiagTailX0RatChunk001Sub000Block134Part013
    + surrogateDiagTailX0RatChunk001Sub000Block134Part014
    + surrogateDiagTailX0RatChunk001Sub000Block134Part015
    + surrogateDiagTailX0RatChunk001Sub000Block134Part016
    + surrogateDiagTailX0RatChunk001Sub000Block134Part017
    + surrogateDiagTailX0RatChunk001Sub000Block134Part018
    + surrogateDiagTailX0RatChunk001Sub000Block134Part019
    + surrogateDiagTailX0RatChunk001Sub000Block134Part020
    + surrogateDiagTailX0RatChunk001Sub000Block134Part021
    + surrogateDiagTailX0RatChunk001Sub000Block134Part022
    + surrogateDiagTailX0RatChunk001Sub000Block134Part023
    + surrogateDiagTailX0RatChunk001Sub000Block134Part024

theorem surrogateDiagTailX0RatChunk001Sub000Block134_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk001Sub000Block134Head + surrogateDiagTailX0RatChunk001Sub000Block134Mid + surrogateDiagTailX0RatChunk001Sub000Block134Tail =
      surrogateDiagTailX0RatChunk001Sub000Block134 := by
  unfold surrogateDiagTailX0RatChunk001Sub000Block134Head surrogateDiagTailX0RatChunk001Sub000Block134Mid surrogateDiagTailX0RatChunk001Sub000Block134Tail surrogateDiagTailX0RatChunk001Sub000Block134
  ring

def SurrogateDiagonalTailChunk001Sub000Block134HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block134HeadSum X0 = surrogateDiagTailX0RatChunk001Sub000Block134Head

def SurrogateDiagonalTailChunk001Sub000Block134MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block134MidSum X0 = surrogateDiagTailX0RatChunk001Sub000Block134Mid

def SurrogateDiagonalTailChunk001Sub000Block134TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block134TailSum X0 = surrogateDiagTailX0RatChunk001Sub000Block134Tail

theorem surrogateDiagonalTailChunk001Sub000Block134_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk001Sub000Block134HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk001Sub000Block134MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk001Sub000Block134TailCertificateAt X0) :
    surrogateDiagonalTailChunk001Sub000Block134Sum X0 = surrogateDiagTailX0RatChunk001Sub000Block134 := by
  unfold SurrogateDiagonalTailChunk001Sub000Block134HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk001Sub000Block134MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk001Sub000Block134TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk001Sub000Block134Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk001Sub000Block134_eq_head_add_mid_add_tail

/-- Block 135 covers tail-support indices [13375,13400) and q from 22047 to 22085. -/

def TailChunk001Sub000Block135Part000SupportExplicit : Finset ℕ :=
  ([22047] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block135Part000 : ℚ :=
  (125025 : ℚ) / 23322042236438528

def SurrogateDiagonalTailChunk001Sub000Block135Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22047
    = surrogateDiagTailX0RatChunk001Sub000Block135Part000

theorem surrogateDiagonalTailChunk001Sub000Block135Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block135Part000CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block135Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block135Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block135Part000CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block135Part000SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block135Part000] using hcert

def TailChunk001Sub000Block135Part001SupportExplicit : Finset ℕ :=
  ([22049] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block135Part001 : ℚ :=
  (424650865075 : ℚ) / 462303089367038558208

def SurrogateDiagonalTailChunk001Sub000Block135Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22049
    = surrogateDiagTailX0RatChunk001Sub000Block135Part001

theorem surrogateDiagonalTailChunk001Sub000Block135Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block135Part001CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block135Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block135Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block135Part001CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block135Part001SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block135Part001] using hcert

def TailChunk001Sub000Block135Part002SupportExplicit : Finset ℕ :=
  ([22051] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block135Part002 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block135Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22051
    = surrogateDiagTailX0RatChunk001Sub000Block135Part002

theorem surrogateDiagonalTailChunk001Sub000Block135Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block135Part002CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block135Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block135Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block135Part002CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block135Part002SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block135Part002] using hcert

def TailChunk001Sub000Block135Part003SupportExplicit : Finset ℕ :=
  ([22053] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block135Part003 : ℚ :=
  (1667 : ℚ) / 311299254000000

def SurrogateDiagonalTailChunk001Sub000Block135Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22053
    = surrogateDiagTailX0RatChunk001Sub000Block135Part003

theorem surrogateDiagonalTailChunk001Sub000Block135Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block135Part003CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block135Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block135Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block135Part003CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block135Part003SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block135Part003] using hcert

def TailChunk001Sub000Block135Part004SupportExplicit : Finset ℕ :=
  ([22054] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block135Part004 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block135Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22054
    = surrogateDiagTailX0RatChunk001Sub000Block135Part004

theorem surrogateDiagonalTailChunk001Sub000Block135Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block135Part004CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block135Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block135Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block135Part004CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block135Part004SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block135Part004] using hcert

def TailChunk001Sub000Block135Part005SupportExplicit : Finset ℕ :=
  ([22055] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block135Part005 : ℚ :=
  (19102154073 : ℚ) / 2184970240000000000

def SurrogateDiagonalTailChunk001Sub000Block135Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22055
    = surrogateDiagTailX0RatChunk001Sub000Block135Part005

theorem surrogateDiagonalTailChunk001Sub000Block135Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block135Part005CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block135Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block135Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block135Part005CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block135Part005SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block135Part005] using hcert

def TailChunk001Sub000Block135Part006SupportExplicit : Finset ℕ :=
  ([22057] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block135Part006 : ℚ :=
  (1402698850075 : ℚ) / 259703747910220382208

def SurrogateDiagonalTailChunk001Sub000Block135Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22057
    = surrogateDiagTailX0RatChunk001Sub000Block135Part006

theorem surrogateDiagonalTailChunk001Sub000Block135Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block135Part006CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block135Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block135Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block135Part006CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block135Part006SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block135Part006] using hcert

def TailChunk001Sub000Block135Part007SupportExplicit : Finset ℕ :=
  ([22058] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block135Part007 : ℚ :=
  (649917681 : ℚ) / 220147998438195200

def SurrogateDiagonalTailChunk001Sub000Block135Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22058
    = surrogateDiagTailX0RatChunk001Sub000Block135Part007

theorem surrogateDiagonalTailChunk001Sub000Block135Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block135Part007CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block135Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block135Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block135Part007CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block135Part007SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block135Part007] using hcert

def TailChunk001Sub000Block135Part008SupportExplicit : Finset ℕ :=
  ([22061] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block135Part008 : ℚ :=
  (271432720475 : ℚ) / 214498983829573730304

def SurrogateDiagonalTailChunk001Sub000Block135Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22061
    = surrogateDiagTailX0RatChunk001Sub000Block135Part008

theorem surrogateDiagonalTailChunk001Sub000Block135Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block135Part008CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block135Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block135Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block135Part008CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block135Part008SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block135Part008] using hcert

def TailChunk001Sub000Block135Part009SupportExplicit : Finset ℕ :=
  ([22062] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block135Part009 : ℚ :=
  (844704466475 : ℚ) / 3652740809613026304

def SurrogateDiagonalTailChunk001Sub000Block135Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22062
    = surrogateDiagTailX0RatChunk001Sub000Block135Part009

theorem surrogateDiagonalTailChunk001Sub000Block135Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block135Part009CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block135Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block135Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block135Part009CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block135Part009SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block135Part009] using hcert

def TailChunk001Sub000Block135Part010SupportExplicit : Finset ℕ :=
  ([22063] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block135Part010 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block135Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22063
    = surrogateDiagTailX0RatChunk001Sub000Block135Part010

theorem surrogateDiagonalTailChunk001Sub000Block135Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block135Part010CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block135Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block135Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block135Part010CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block135Part010SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block135Part010] using hcert

def TailChunk001Sub000Block135Part011SupportExplicit : Finset ℕ :=
  ([22065] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block135Part011 : ℚ :=
  (2478249749 : ℚ) / 39854273772902400

def SurrogateDiagonalTailChunk001Sub000Block135Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22065
    = surrogateDiagTailX0RatChunk001Sub000Block135Part011

theorem surrogateDiagonalTailChunk001Sub000Block135Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block135Part011CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block135Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block135Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block135Part011CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block135Part011SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block135Part011] using hcert

def TailChunk001Sub000Block135Part012SupportExplicit : Finset ℕ :=
  ([22066] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block135Part012 : ℚ :=
  (20099815843 : ℚ) / 741786209432371200

def SurrogateDiagonalTailChunk001Sub000Block135Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22066
    = surrogateDiagTailX0RatChunk001Sub000Block135Part012

theorem surrogateDiagonalTailChunk001Sub000Block135Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block135Part012CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block135Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block135Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block135Part012CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block135Part012SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block135Part012] using hcert

def TailChunk001Sub000Block135Part013SupportExplicit : Finset ℕ :=
  ([22067] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block135Part013 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block135Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22067
    = surrogateDiagTailX0RatChunk001Sub000Block135Part013

theorem surrogateDiagonalTailChunk001Sub000Block135Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block135Part013CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block135Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block135Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block135Part013CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block135Part013SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block135Part013] using hcert

def TailChunk001Sub000Block135Part014SupportExplicit : Finset ℕ :=
  ([22069] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block135Part014 : ℚ :=
  (9004615231 : ℚ) / 20510362903786291200

def SurrogateDiagonalTailChunk001Sub000Block135Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22069
    = surrogateDiagTailX0RatChunk001Sub000Block135Part014

theorem surrogateDiagonalTailChunk001Sub000Block135Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block135Part014CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block135Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block135Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block135Part014CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block135Part014SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block135Part014] using hcert

def TailChunk001Sub000Block135Part015SupportExplicit : Finset ℕ :=
  ([22070] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block135Part015 : ℚ :=
  (609433302025 : ℚ) / 15159638900457228288

def SurrogateDiagonalTailChunk001Sub000Block135Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22070
    = surrogateDiagTailX0RatChunk001Sub000Block135Part015

theorem surrogateDiagonalTailChunk001Sub000Block135Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block135Part015CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block135Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block135Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block135Part015CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block135Part015SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block135Part015] using hcert

def TailChunk001Sub000Block135Part016SupportExplicit : Finset ℕ :=
  ([22071] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block135Part016 : ℚ :=
  (31731845059 : ℚ) / 630244463688000000

def SurrogateDiagonalTailChunk001Sub000Block135Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22071
    = surrogateDiagTailX0RatChunk001Sub000Block135Part016

theorem surrogateDiagonalTailChunk001Sub000Block135Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block135Part016CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block135Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block135Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block135Part016CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block135Part016SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block135Part016] using hcert

def TailChunk001Sub000Block135Part017SupportExplicit : Finset ℕ :=
  ([22073] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block135Part017 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block135Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22073
    = surrogateDiagTailX0RatChunk001Sub000Block135Part017

theorem surrogateDiagonalTailChunk001Sub000Block135Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block135Part017CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block135Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block135Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block135Part017CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block135Part017SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block135Part017] using hcert

def TailChunk001Sub000Block135Part018SupportExplicit : Finset ℕ :=
  ([22074] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block135Part018 : ℚ :=
  (1607545654375 : ℚ) / 5246482867553599488

def SurrogateDiagonalTailChunk001Sub000Block135Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22074
    = surrogateDiagTailX0RatChunk001Sub000Block135Part018

theorem surrogateDiagonalTailChunk001Sub000Block135Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block135Part018CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block135Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block135Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block135Part018CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block135Part018SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block135Part018] using hcert

def TailChunk001Sub000Block135Part019SupportExplicit : Finset ℕ :=
  ([22078] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block135Part019 : ℚ :=
  (149469297775 : ℚ) / 3845185527427379712

def SurrogateDiagonalTailChunk001Sub000Block135Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22078
    = surrogateDiagTailX0RatChunk001Sub000Block135Part019

theorem surrogateDiagonalTailChunk001Sub000Block135Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block135Part019CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block135Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block135Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block135Part019CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block135Part019SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block135Part019] using hcert

def TailChunk001Sub000Block135Part020SupportExplicit : Finset ℕ :=
  ([22079] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block135Part020 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block135Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22079
    = surrogateDiagTailX0RatChunk001Sub000Block135Part020

theorem surrogateDiagonalTailChunk001Sub000Block135Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block135Part020CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block135Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block135Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block135Part020CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block135Part020SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block135Part020] using hcert

def TailChunk001Sub000Block135Part021SupportExplicit : Finset ℕ :=
  ([22081] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block135Part021 : ℚ :=
  (940500749 : ℚ) / 4435634791568400000

def SurrogateDiagonalTailChunk001Sub000Block135Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22081
    = surrogateDiagTailX0RatChunk001Sub000Block135Part021

theorem surrogateDiagonalTailChunk001Sub000Block135Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block135Part021CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block135Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block135Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block135Part021CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block135Part021SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block135Part021] using hcert

def TailChunk001Sub000Block135Part022SupportExplicit : Finset ℕ :=
  ([22082] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block135Part022 : ℚ :=
  (601196753 : ℚ) / 272152211558400000

def SurrogateDiagonalTailChunk001Sub000Block135Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22082
    = surrogateDiagTailX0RatChunk001Sub000Block135Part022

theorem surrogateDiagonalTailChunk001Sub000Block135Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block135Part022CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block135Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block135Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block135Part022CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block135Part022SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block135Part022] using hcert

def TailChunk001Sub000Block135Part023SupportExplicit : Finset ℕ :=
  ([22083] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block135Part023 : ℚ :=
  (3264210480475 : ℚ) / 91319128763859468288

def SurrogateDiagonalTailChunk001Sub000Block135Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22083
    = surrogateDiagTailX0RatChunk001Sub000Block135Part023

theorem surrogateDiagonalTailChunk001Sub000Block135Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block135Part023CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block135Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block135Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block135Part023CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block135Part023SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block135Part023] using hcert

def TailChunk001Sub000Block135Part024SupportExplicit : Finset ℕ :=
  ([22085] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block135Part024 : ℚ :=
  (6061056191 : ℚ) / 435624973301145600

def SurrogateDiagonalTailChunk001Sub000Block135Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22085
    = surrogateDiagTailX0RatChunk001Sub000Block135Part024

theorem surrogateDiagonalTailChunk001Sub000Block135Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block135Part024CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block135Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block135Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block135Part024CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block135Part024SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block135Part024] using hcert

def surrogateDiagonalTailChunk001Sub000Block135HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block135Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block135Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block135Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block135Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block135Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block135Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block135Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block135Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block135Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block135Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block135Head : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block135Part000
    + surrogateDiagTailX0RatChunk001Sub000Block135Part001
    + surrogateDiagTailX0RatChunk001Sub000Block135Part002
    + surrogateDiagTailX0RatChunk001Sub000Block135Part003
    + surrogateDiagTailX0RatChunk001Sub000Block135Part004
    + surrogateDiagTailX0RatChunk001Sub000Block135Part005
    + surrogateDiagTailX0RatChunk001Sub000Block135Part006
    + surrogateDiagTailX0RatChunk001Sub000Block135Part007
    + surrogateDiagTailX0RatChunk001Sub000Block135Part008
    + surrogateDiagTailX0RatChunk001Sub000Block135Part009

def surrogateDiagonalTailChunk001Sub000Block135MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block135Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block135Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block135Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block135Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block135Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block135Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block135Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block135Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block135Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block135Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block135Mid : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block135Part010
    + surrogateDiagTailX0RatChunk001Sub000Block135Part011
    + surrogateDiagTailX0RatChunk001Sub000Block135Part012
    + surrogateDiagTailX0RatChunk001Sub000Block135Part013
    + surrogateDiagTailX0RatChunk001Sub000Block135Part014
    + surrogateDiagTailX0RatChunk001Sub000Block135Part015
    + surrogateDiagTailX0RatChunk001Sub000Block135Part016
    + surrogateDiagTailX0RatChunk001Sub000Block135Part017
    + surrogateDiagTailX0RatChunk001Sub000Block135Part018
    + surrogateDiagTailX0RatChunk001Sub000Block135Part019

def surrogateDiagonalTailChunk001Sub000Block135TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block135Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block135Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block135Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block135Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block135Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block135Tail : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block135Part020
    + surrogateDiagTailX0RatChunk001Sub000Block135Part021
    + surrogateDiagTailX0RatChunk001Sub000Block135Part022
    + surrogateDiagTailX0RatChunk001Sub000Block135Part023
    + surrogateDiagTailX0RatChunk001Sub000Block135Part024

def surrogateDiagonalTailChunk001Sub000Block135Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk001Sub000Block135HeadSum X0
    + surrogateDiagonalTailChunk001Sub000Block135MidSum X0
    + surrogateDiagonalTailChunk001Sub000Block135TailSum X0

def surrogateDiagTailX0RatChunk001Sub000Block135 : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block135Part000
    + surrogateDiagTailX0RatChunk001Sub000Block135Part001
    + surrogateDiagTailX0RatChunk001Sub000Block135Part002
    + surrogateDiagTailX0RatChunk001Sub000Block135Part003
    + surrogateDiagTailX0RatChunk001Sub000Block135Part004
    + surrogateDiagTailX0RatChunk001Sub000Block135Part005
    + surrogateDiagTailX0RatChunk001Sub000Block135Part006
    + surrogateDiagTailX0RatChunk001Sub000Block135Part007
    + surrogateDiagTailX0RatChunk001Sub000Block135Part008
    + surrogateDiagTailX0RatChunk001Sub000Block135Part009
    + surrogateDiagTailX0RatChunk001Sub000Block135Part010
    + surrogateDiagTailX0RatChunk001Sub000Block135Part011
    + surrogateDiagTailX0RatChunk001Sub000Block135Part012
    + surrogateDiagTailX0RatChunk001Sub000Block135Part013
    + surrogateDiagTailX0RatChunk001Sub000Block135Part014
    + surrogateDiagTailX0RatChunk001Sub000Block135Part015
    + surrogateDiagTailX0RatChunk001Sub000Block135Part016
    + surrogateDiagTailX0RatChunk001Sub000Block135Part017
    + surrogateDiagTailX0RatChunk001Sub000Block135Part018
    + surrogateDiagTailX0RatChunk001Sub000Block135Part019
    + surrogateDiagTailX0RatChunk001Sub000Block135Part020
    + surrogateDiagTailX0RatChunk001Sub000Block135Part021
    + surrogateDiagTailX0RatChunk001Sub000Block135Part022
    + surrogateDiagTailX0RatChunk001Sub000Block135Part023
    + surrogateDiagTailX0RatChunk001Sub000Block135Part024

theorem surrogateDiagTailX0RatChunk001Sub000Block135_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk001Sub000Block135Head + surrogateDiagTailX0RatChunk001Sub000Block135Mid + surrogateDiagTailX0RatChunk001Sub000Block135Tail =
      surrogateDiagTailX0RatChunk001Sub000Block135 := by
  unfold surrogateDiagTailX0RatChunk001Sub000Block135Head surrogateDiagTailX0RatChunk001Sub000Block135Mid surrogateDiagTailX0RatChunk001Sub000Block135Tail surrogateDiagTailX0RatChunk001Sub000Block135
  ring

def SurrogateDiagonalTailChunk001Sub000Block135HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block135HeadSum X0 = surrogateDiagTailX0RatChunk001Sub000Block135Head

def SurrogateDiagonalTailChunk001Sub000Block135MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block135MidSum X0 = surrogateDiagTailX0RatChunk001Sub000Block135Mid

def SurrogateDiagonalTailChunk001Sub000Block135TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block135TailSum X0 = surrogateDiagTailX0RatChunk001Sub000Block135Tail

theorem surrogateDiagonalTailChunk001Sub000Block135_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk001Sub000Block135HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk001Sub000Block135MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk001Sub000Block135TailCertificateAt X0) :
    surrogateDiagonalTailChunk001Sub000Block135Sum X0 = surrogateDiagTailX0RatChunk001Sub000Block135 := by
  unfold SurrogateDiagonalTailChunk001Sub000Block135HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk001Sub000Block135MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk001Sub000Block135TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk001Sub000Block135Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk001Sub000Block135_eq_head_add_mid_add_tail

/-- Block 136 covers tail-support indices [13400,13425) and q from 22087 to 22129. -/

def TailChunk001Sub000Block136Part000SupportExplicit : Finset ℕ :=
  ([22087] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block136Part000 : ℚ :=
  (17004302525 : ℚ) / 13469535163456939584

def SurrogateDiagonalTailChunk001Sub000Block136Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22087
    = surrogateDiagTailX0RatChunk001Sub000Block136Part000

theorem surrogateDiagonalTailChunk001Sub000Block136Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block136Part000CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block136Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block136Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block136Part000CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block136Part000SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block136Part000] using hcert

def TailChunk001Sub000Block136Part001SupportExplicit : Finset ℕ :=
  ([22089] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block136Part001 : ℚ :=
  (61399107775 : ℚ) / 1912598654124736512

def SurrogateDiagonalTailChunk001Sub000Block136Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22089
    = surrogateDiagTailX0RatChunk001Sub000Block136Part001

theorem surrogateDiagonalTailChunk001Sub000Block136Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block136Part001CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block136Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block136Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block136Part001CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block136Part001SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block136Part001] using hcert

def TailChunk001Sub000Block136Part002SupportExplicit : Finset ℕ :=
  ([22091] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block136Part002 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block136Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22091
    = surrogateDiagTailX0RatChunk001Sub000Block136Part002

theorem surrogateDiagonalTailChunk001Sub000Block136Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block136Part002CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block136Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block136Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block136Part002CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block136Part002SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block136Part002] using hcert

def TailChunk001Sub000Block136Part003SupportExplicit : Finset ℕ :=
  ([22093] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block136Part003 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block136Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22093
    = surrogateDiagTailX0RatChunk001Sub000Block136Part003

theorem surrogateDiagonalTailChunk001Sub000Block136Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block136Part003CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block136Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block136Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block136Part003CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block136Part003SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block136Part003] using hcert

def TailChunk001Sub000Block136Part004SupportExplicit : Finset ℕ :=
  ([22094] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block136Part004 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block136Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22094
    = surrogateDiagTailX0RatChunk001Sub000Block136Part004

theorem surrogateDiagonalTailChunk001Sub000Block136Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block136Part004CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block136Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block136Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block136Part004CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block136Part004SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block136Part004] using hcert

def TailChunk001Sub000Block136Part005SupportExplicit : Finset ℕ :=
  ([22097] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block136Part005 : ℚ :=
  (71206038425 : ℚ) / 79760917509807860928

def SurrogateDiagonalTailChunk001Sub000Block136Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22097
    = surrogateDiagTailX0RatChunk001Sub000Block136Part005

theorem surrogateDiagonalTailChunk001Sub000Block136Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block136Part005CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block136Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block136Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block136Part005CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block136Part005SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block136Part005] using hcert

def TailChunk001Sub000Block136Part006SupportExplicit : Finset ℕ :=
  ([22098] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block136Part006 : ℚ :=
  (1648223756275 : ℚ) / 6198136657161781248

def SurrogateDiagonalTailChunk001Sub000Block136Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22098
    = surrogateDiagTailX0RatChunk001Sub000Block136Part006

theorem surrogateDiagonalTailChunk001Sub000Block136Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block136Part006CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block136Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block136Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block136Part006CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block136Part006SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block136Part006] using hcert

def TailChunk001Sub000Block136Part007SupportExplicit : Finset ℕ :=
  ([22101] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block136Part007 : ℚ :=
  (833910356875 : ℚ) / 26522628997512241152

def SurrogateDiagonalTailChunk001Sub000Block136Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22101
    = surrogateDiagTailX0RatChunk001Sub000Block136Part007

theorem surrogateDiagonalTailChunk001Sub000Block136Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block136Part007CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block136Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block136Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block136Part007CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block136Part007SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block136Part007] using hcert

def TailChunk001Sub000Block136Part008SupportExplicit : Finset ℕ :=
  ([22102] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block136Part008 : ℚ :=
  (45371899175 : ℚ) / 16709131852006293504

def SurrogateDiagonalTailChunk001Sub000Block136Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22102
    = surrogateDiagTailX0RatChunk001Sub000Block136Part008

theorem surrogateDiagonalTailChunk001Sub000Block136Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block136Part008CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block136Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block136Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block136Part008CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block136Part008SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block136Part008] using hcert

def TailChunk001Sub000Block136Part009SupportExplicit : Finset ℕ :=
  ([22105] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block136Part009 : ℚ :=
  (3259401693 : ℚ) / 651515322274119680

def SurrogateDiagonalTailChunk001Sub000Block136Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22105
    = surrogateDiagTailX0RatChunk001Sub000Block136Part009

theorem surrogateDiagonalTailChunk001Sub000Block136Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block136Part009CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block136Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block136Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block136Part009CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block136Part009SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block136Part009] using hcert

def TailChunk001Sub000Block136Part010SupportExplicit : Finset ℕ :=
  ([22106] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block136Part010 : ℚ :=
  (8677381825 : ℚ) / 372105505843284672

def SurrogateDiagonalTailChunk001Sub000Block136Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22106
    = surrogateDiagTailX0RatChunk001Sub000Block136Part010

theorem surrogateDiagonalTailChunk001Sub000Block136Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block136Part010CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block136Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block136Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block136Part010CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block136Part010SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block136Part010] using hcert

def TailChunk001Sub000Block136Part011SupportExplicit : Finset ℕ :=
  ([22107] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block136Part011 : ℚ :=
  (848397250825 : ℚ) / 29477138294366871552

def SurrogateDiagonalTailChunk001Sub000Block136Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22107
    = surrogateDiagTailX0RatChunk001Sub000Block136Part011

theorem surrogateDiagonalTailChunk001Sub000Block136Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block136Part011CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block136Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block136Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block136Part011CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block136Part011SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block136Part011] using hcert

def TailChunk001Sub000Block136Part012SupportExplicit : Finset ℕ :=
  ([22109] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block136Part012 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block136Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22109
    = surrogateDiagTailX0RatChunk001Sub000Block136Part012

theorem surrogateDiagonalTailChunk001Sub000Block136Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block136Part012CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block136Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block136Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block136Part012CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block136Part012SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block136Part012] using hcert

def TailChunk001Sub000Block136Part013SupportExplicit : Finset ℕ :=
  ([22110] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block136Part013 : ℚ :=
  (53867174641 : ℚ) / 77736062759731200

def SurrogateDiagonalTailChunk001Sub000Block136Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22110
    = surrogateDiagTailX0RatChunk001Sub000Block136Part013

theorem surrogateDiagonalTailChunk001Sub000Block136Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block136Part013CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block136Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block136Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block136Part013CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block136Part013SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block136Part013] using hcert

def TailChunk001Sub000Block136Part014SupportExplicit : Finset ℕ :=
  ([22111] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block136Part014 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block136Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22111
    = surrogateDiagTailX0RatChunk001Sub000Block136Part014

theorem surrogateDiagonalTailChunk001Sub000Block136Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block136Part014CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block136Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block136Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block136Part014CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block136Part014SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block136Part014] using hcert

def TailChunk001Sub000Block136Part015SupportExplicit : Finset ℕ :=
  ([22114] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block136Part015 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block136Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22114
    = surrogateDiagTailX0RatChunk001Sub000Block136Part015

theorem surrogateDiagonalTailChunk001Sub000Block136Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block136Part015CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block136Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block136Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block136Part015CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block136Part015SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block136Part015] using hcert

def TailChunk001Sub000Block136Part016SupportExplicit : Finset ℕ :=
  ([22115] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block136Part016 : ℚ :=
  (1223380884625 : ℚ) / 244760751052333959168

def SurrogateDiagonalTailChunk001Sub000Block136Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22115
    = surrogateDiagTailX0RatChunk001Sub000Block136Part016

theorem surrogateDiagonalTailChunk001Sub000Block136Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block136Part016CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block136Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block136Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block136Part016CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block136Part016SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block136Part016] using hcert

def TailChunk001Sub000Block136Part017SupportExplicit : Finset ℕ :=
  ([22117] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block136Part017 : ℚ :=
  (17089812283 : ℚ) / 18721480507392000000

def SurrogateDiagonalTailChunk001Sub000Block136Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22117
    = surrogateDiagTailX0RatChunk001Sub000Block136Part017

theorem surrogateDiagonalTailChunk001Sub000Block136Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block136Part017CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block136Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block136Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block136Part017CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block136Part017SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block136Part017] using hcert

def TailChunk001Sub000Block136Part018SupportExplicit : Finset ℕ :=
  ([22118] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block136Part018 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block136Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22118
    = surrogateDiagTailX0RatChunk001Sub000Block136Part018

theorem surrogateDiagonalTailChunk001Sub000Block136Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block136Part018CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block136Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block136Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block136Part018CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block136Part018SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block136Part018] using hcert

def TailChunk001Sub000Block136Part019SupportExplicit : Finset ℕ :=
  ([22119] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block136Part019 : ℚ :=
  (133775186809 : ℚ) / 4300676923392000000

def SurrogateDiagonalTailChunk001Sub000Block136Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22119
    = surrogateDiagTailX0RatChunk001Sub000Block136Part019

theorem surrogateDiagonalTailChunk001Sub000Block136Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block136Part019CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block136Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block136Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block136Part019CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block136Part019SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block136Part019] using hcert

def TailChunk001Sub000Block136Part020SupportExplicit : Finset ℕ :=
  ([22121] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block136Part020 : ℚ :=
  (30413719987 : ℚ) / 16325672491602000000

def SurrogateDiagonalTailChunk001Sub000Block136Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22121
    = surrogateDiagTailX0RatChunk001Sub000Block136Part020

theorem surrogateDiagonalTailChunk001Sub000Block136Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block136Part020CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block136Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block136Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block136Part020CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block136Part020SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block136Part020] using hcert

def TailChunk001Sub000Block136Part021SupportExplicit : Finset ℕ :=
  ([22123] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block136Part021 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block136Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22123
    = surrogateDiagTailX0RatChunk001Sub000Block136Part021

theorem surrogateDiagonalTailChunk001Sub000Block136Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block136Part021CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block136Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block136Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block136Part021CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block136Part021SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block136Part021] using hcert

def TailChunk001Sub000Block136Part022SupportExplicit : Finset ℕ :=
  ([22126] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block136Part022 : ℚ :=
  (6116778725 : ℚ) / 283347948759220224

def SurrogateDiagonalTailChunk001Sub000Block136Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22126
    = surrogateDiagTailX0RatChunk001Sub000Block136Part022

theorem surrogateDiagonalTailChunk001Sub000Block136Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block136Part022CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block136Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block136Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block136Part022CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block136Part022SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block136Part022] using hcert

def TailChunk001Sub000Block136Part023SupportExplicit : Finset ℕ :=
  ([22127] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block136Part023 : ℚ :=
  (404420860625 : ℚ) / 135496791695588327424

def SurrogateDiagonalTailChunk001Sub000Block136Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22127
    = surrogateDiagTailX0RatChunk001Sub000Block136Part023

theorem surrogateDiagonalTailChunk001Sub000Block136Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block136Part023CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block136Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block136Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block136Part023CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block136Part023SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block136Part023] using hcert

def TailChunk001Sub000Block136Part024SupportExplicit : Finset ℕ :=
  ([22129] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block136Part024 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block136Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22129
    = surrogateDiagTailX0RatChunk001Sub000Block136Part024

theorem surrogateDiagonalTailChunk001Sub000Block136Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block136Part024CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block136Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block136Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block136Part024CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block136Part024SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block136Part024] using hcert

def surrogateDiagonalTailChunk001Sub000Block136HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block136Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block136Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block136Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block136Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block136Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block136Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block136Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block136Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block136Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block136Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block136Head : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block136Part000
    + surrogateDiagTailX0RatChunk001Sub000Block136Part001
    + surrogateDiagTailX0RatChunk001Sub000Block136Part002
    + surrogateDiagTailX0RatChunk001Sub000Block136Part003
    + surrogateDiagTailX0RatChunk001Sub000Block136Part004
    + surrogateDiagTailX0RatChunk001Sub000Block136Part005
    + surrogateDiagTailX0RatChunk001Sub000Block136Part006
    + surrogateDiagTailX0RatChunk001Sub000Block136Part007
    + surrogateDiagTailX0RatChunk001Sub000Block136Part008
    + surrogateDiagTailX0RatChunk001Sub000Block136Part009

def surrogateDiagonalTailChunk001Sub000Block136MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block136Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block136Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block136Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block136Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block136Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block136Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block136Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block136Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block136Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block136Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block136Mid : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block136Part010
    + surrogateDiagTailX0RatChunk001Sub000Block136Part011
    + surrogateDiagTailX0RatChunk001Sub000Block136Part012
    + surrogateDiagTailX0RatChunk001Sub000Block136Part013
    + surrogateDiagTailX0RatChunk001Sub000Block136Part014
    + surrogateDiagTailX0RatChunk001Sub000Block136Part015
    + surrogateDiagTailX0RatChunk001Sub000Block136Part016
    + surrogateDiagTailX0RatChunk001Sub000Block136Part017
    + surrogateDiagTailX0RatChunk001Sub000Block136Part018
    + surrogateDiagTailX0RatChunk001Sub000Block136Part019

def surrogateDiagonalTailChunk001Sub000Block136TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block136Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block136Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block136Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block136Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block136Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block136Tail : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block136Part020
    + surrogateDiagTailX0RatChunk001Sub000Block136Part021
    + surrogateDiagTailX0RatChunk001Sub000Block136Part022
    + surrogateDiagTailX0RatChunk001Sub000Block136Part023
    + surrogateDiagTailX0RatChunk001Sub000Block136Part024

def surrogateDiagonalTailChunk001Sub000Block136Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk001Sub000Block136HeadSum X0
    + surrogateDiagonalTailChunk001Sub000Block136MidSum X0
    + surrogateDiagonalTailChunk001Sub000Block136TailSum X0

def surrogateDiagTailX0RatChunk001Sub000Block136 : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block136Part000
    + surrogateDiagTailX0RatChunk001Sub000Block136Part001
    + surrogateDiagTailX0RatChunk001Sub000Block136Part002
    + surrogateDiagTailX0RatChunk001Sub000Block136Part003
    + surrogateDiagTailX0RatChunk001Sub000Block136Part004
    + surrogateDiagTailX0RatChunk001Sub000Block136Part005
    + surrogateDiagTailX0RatChunk001Sub000Block136Part006
    + surrogateDiagTailX0RatChunk001Sub000Block136Part007
    + surrogateDiagTailX0RatChunk001Sub000Block136Part008
    + surrogateDiagTailX0RatChunk001Sub000Block136Part009
    + surrogateDiagTailX0RatChunk001Sub000Block136Part010
    + surrogateDiagTailX0RatChunk001Sub000Block136Part011
    + surrogateDiagTailX0RatChunk001Sub000Block136Part012
    + surrogateDiagTailX0RatChunk001Sub000Block136Part013
    + surrogateDiagTailX0RatChunk001Sub000Block136Part014
    + surrogateDiagTailX0RatChunk001Sub000Block136Part015
    + surrogateDiagTailX0RatChunk001Sub000Block136Part016
    + surrogateDiagTailX0RatChunk001Sub000Block136Part017
    + surrogateDiagTailX0RatChunk001Sub000Block136Part018
    + surrogateDiagTailX0RatChunk001Sub000Block136Part019
    + surrogateDiagTailX0RatChunk001Sub000Block136Part020
    + surrogateDiagTailX0RatChunk001Sub000Block136Part021
    + surrogateDiagTailX0RatChunk001Sub000Block136Part022
    + surrogateDiagTailX0RatChunk001Sub000Block136Part023
    + surrogateDiagTailX0RatChunk001Sub000Block136Part024

theorem surrogateDiagTailX0RatChunk001Sub000Block136_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk001Sub000Block136Head + surrogateDiagTailX0RatChunk001Sub000Block136Mid + surrogateDiagTailX0RatChunk001Sub000Block136Tail =
      surrogateDiagTailX0RatChunk001Sub000Block136 := by
  unfold surrogateDiagTailX0RatChunk001Sub000Block136Head surrogateDiagTailX0RatChunk001Sub000Block136Mid surrogateDiagTailX0RatChunk001Sub000Block136Tail surrogateDiagTailX0RatChunk001Sub000Block136
  ring

def SurrogateDiagonalTailChunk001Sub000Block136HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block136HeadSum X0 = surrogateDiagTailX0RatChunk001Sub000Block136Head

def SurrogateDiagonalTailChunk001Sub000Block136MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block136MidSum X0 = surrogateDiagTailX0RatChunk001Sub000Block136Mid

def SurrogateDiagonalTailChunk001Sub000Block136TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block136TailSum X0 = surrogateDiagTailX0RatChunk001Sub000Block136Tail

theorem surrogateDiagonalTailChunk001Sub000Block136_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk001Sub000Block136HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk001Sub000Block136MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk001Sub000Block136TailCertificateAt X0) :
    surrogateDiagonalTailChunk001Sub000Block136Sum X0 = surrogateDiagTailX0RatChunk001Sub000Block136 := by
  unfold SurrogateDiagonalTailChunk001Sub000Block136HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk001Sub000Block136MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk001Sub000Block136TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk001Sub000Block136Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk001Sub000Block136_eq_head_add_mid_add_tail

/-- Block 137 covers tail-support indices [13425,13450) and q from 22130 to 22171. -/

def TailChunk001Sub000Block137Part000SupportExplicit : Finset ℕ :=
  ([22130] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block137Part000 : ℚ :=
  (65593566425 : ℚ) / 1094660076220956672

def SurrogateDiagonalTailChunk001Sub000Block137Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22130
    = surrogateDiagTailX0RatChunk001Sub000Block137Part000

theorem surrogateDiagonalTailChunk001Sub000Block137Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block137Part000CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block137Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block137Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block137Part000CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block137Part000SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block137Part000] using hcert

def TailChunk001Sub000Block137Part001SupportExplicit : Finset ℕ :=
  ([22133] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block137Part001 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block137Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22133
    = surrogateDiagTailX0RatChunk001Sub000Block137Part001

theorem surrogateDiagonalTailChunk001Sub000Block137Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block137Part001CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block137Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block137Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block137Part001CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block137Part001SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block137Part001] using hcert

def TailChunk001Sub000Block137Part002SupportExplicit : Finset ℕ :=
  ([22134] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block137Part002 : ℚ :=
  (11585831 : ℚ) / 33980657172480

def SurrogateDiagonalTailChunk001Sub000Block137Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22134
    = surrogateDiagTailX0RatChunk001Sub000Block137Part002

theorem surrogateDiagonalTailChunk001Sub000Block137Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block137Part002CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block137Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block137Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block137Part002CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block137Part002SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block137Part002] using hcert

def TailChunk001Sub000Block137Part003SupportExplicit : Finset ℕ :=
  ([22135] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block137Part003 : ℚ :=
  (21300694625 : ℚ) / 1678227351753719808

def SurrogateDiagonalTailChunk001Sub000Block137Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22135
    = surrogateDiagTailX0RatChunk001Sub000Block137Part003

theorem surrogateDiagonalTailChunk001Sub000Block137Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block137Part003CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block137Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block137Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block137Part003CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block137Part003SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block137Part003] using hcert

def TailChunk001Sub000Block137Part004SupportExplicit : Finset ℕ :=
  ([22137] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block137Part004 : ℚ :=
  (3344128205575 : ℚ) / 106090515990048964608

def SurrogateDiagonalTailChunk001Sub000Block137Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22137
    = surrogateDiagTailX0RatChunk001Sub000Block137Part004

theorem surrogateDiagonalTailChunk001Sub000Block137Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block137Part004CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block137Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block137Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block137Part004CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block137Part004SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block137Part004] using hcert

def TailChunk001Sub000Block137Part005SupportExplicit : Finset ℕ :=
  ([22138] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block137Part005 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block137Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22138
    = surrogateDiagTailX0RatChunk001Sub000Block137Part005

theorem surrogateDiagonalTailChunk001Sub000Block137Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block137Part005CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block137Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block137Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block137Part005CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block137Part005SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block137Part005] using hcert

def TailChunk001Sub000Block137Part006SupportExplicit : Finset ℕ :=
  ([22141] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block137Part006 : ℚ :=
  (626765157925 : ℚ) / 323950998434894771328

def SurrogateDiagonalTailChunk001Sub000Block137Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22141
    = surrogateDiagTailX0RatChunk001Sub000Block137Part006

theorem surrogateDiagonalTailChunk001Sub000Block137Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block137Part006CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block137Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block137Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block137Part006CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block137Part006SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block137Part006] using hcert

def TailChunk001Sub000Block137Part007SupportExplicit : Finset ℕ :=
  ([22142] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block137Part007 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block137Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22142
    = surrogateDiagTailX0RatChunk001Sub000Block137Part007

theorem surrogateDiagonalTailChunk001Sub000Block137Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block137Part007CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block137Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block137Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block137Part007CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block137Part007SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block137Part007] using hcert

def TailChunk001Sub000Block137Part008SupportExplicit : Finset ℕ :=
  ([22145] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block137Part008 : ℚ :=
  (2472943907725 : ℚ) / 215607901600503595008

def SurrogateDiagonalTailChunk001Sub000Block137Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22145
    = surrogateDiagTailX0RatChunk001Sub000Block137Part008

theorem surrogateDiagonalTailChunk001Sub000Block137Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block137Part008CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block137Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block137Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block137Part008CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block137Part008SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block137Part008] using hcert

def TailChunk001Sub000Block137Part009SupportExplicit : Finset ℕ :=
  ([22146] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block137Part009 : ℚ :=
  (3406525381 : ℚ) / 29669641415334720

def SurrogateDiagonalTailChunk001Sub000Block137Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22146
    = surrogateDiagTailX0RatChunk001Sub000Block137Part009

theorem surrogateDiagonalTailChunk001Sub000Block137Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block137Part009CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block137Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block137Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block137Part009CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block137Part009SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block137Part009] using hcert

def TailChunk001Sub000Block137Part010SupportExplicit : Finset ℕ :=
  ([22147] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block137Part010 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block137Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22147
    = surrogateDiagTailX0RatChunk001Sub000Block137Part010

theorem surrogateDiagonalTailChunk001Sub000Block137Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block137Part010CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block137Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block137Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block137Part010CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block137Part010SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block137Part010] using hcert

def TailChunk001Sub000Block137Part011SupportExplicit : Finset ℕ :=
  ([22151] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block137Part011 : ℚ :=
  (428545526275 : ℚ) / 470923893954367193088

def SurrogateDiagonalTailChunk001Sub000Block137Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22151
    = surrogateDiagTailX0RatChunk001Sub000Block137Part011

theorem surrogateDiagonalTailChunk001Sub000Block137Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block137Part011CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block137Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block137Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block137Part011CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block137Part011SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block137Part011] using hcert

def TailChunk001Sub000Block137Part012SupportExplicit : Finset ℕ :=
  ([22153] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block137Part012 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block137Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22153
    = surrogateDiagTailX0RatChunk001Sub000Block137Part012

theorem surrogateDiagonalTailChunk001Sub000Block137Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block137Part012CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block137Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block137Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block137Part012CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block137Part012SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block137Part012] using hcert

def TailChunk001Sub000Block137Part013SupportExplicit : Finset ℕ :=
  ([22154] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block137Part013 : ℚ :=
  (6607495717 : ℚ) / 255899236685414400

def SurrogateDiagonalTailChunk001Sub000Block137Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22154
    = surrogateDiagTailX0RatChunk001Sub000Block137Part013

theorem surrogateDiagonalTailChunk001Sub000Block137Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block137Part013CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block137Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block137Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block137Part013CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block137Part013SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block137Part013] using hcert

def TailChunk001Sub000Block137Part014SupportExplicit : Finset ℕ :=
  ([22155] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block137Part014 : ℚ :=
  (52550649071 : ℚ) / 516296264653209600

def SurrogateDiagonalTailChunk001Sub000Block137Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22155
    = surrogateDiagTailX0RatChunk001Sub000Block137Part014

theorem surrogateDiagonalTailChunk001Sub000Block137Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block137Part014CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block137Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block137Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block137Part014CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block137Part014SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block137Part014] using hcert

def TailChunk001Sub000Block137Part015SupportExplicit : Finset ℕ :=
  ([22157] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block137Part015 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block137Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22157
    = surrogateDiagTailX0RatChunk001Sub000Block137Part015

theorem surrogateDiagonalTailChunk001Sub000Block137Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block137Part015CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block137Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block137Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block137Part015CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block137Part015SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block137Part015] using hcert

def TailChunk001Sub000Block137Part016SupportExplicit : Finset ℕ :=
  ([22159] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block137Part016 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block137Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22159
    = surrogateDiagTailX0RatChunk001Sub000Block137Part016

theorem surrogateDiagonalTailChunk001Sub000Block137Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block137Part016CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block137Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block137Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block137Part016CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block137Part016SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block137Part016] using hcert

def TailChunk001Sub000Block137Part017SupportExplicit : Finset ℕ :=
  ([22161] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block137Part017 : ℚ :=
  (1679859080525 : ℚ) / 54237909738271801344

def SurrogateDiagonalTailChunk001Sub000Block137Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22161
    = surrogateDiagTailX0RatChunk001Sub000Block137Part017

theorem surrogateDiagonalTailChunk001Sub000Block137Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block137Part017CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block137Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block137Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block137Part017CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block137Part017SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block137Part017] using hcert

def TailChunk001Sub000Block137Part018SupportExplicit : Finset ℕ :=
  ([22162] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block137Part018 : ℚ :=
  (627179995525 : ℚ) / 20298211671938514048

def SurrogateDiagonalTailChunk001Sub000Block137Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22162
    = surrogateDiagTailX0RatChunk001Sub000Block137Part018

theorem surrogateDiagonalTailChunk001Sub000Block137Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block137Part018CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block137Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block137Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block137Part018CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block137Part018SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block137Part018] using hcert

def TailChunk001Sub000Block137Part019SupportExplicit : Finset ℕ :=
  ([22163] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block137Part019 : ℚ :=
  (302095175 : ℚ) / 765075836466699264

def SurrogateDiagonalTailChunk001Sub000Block137Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22163
    = surrogateDiagTailX0RatChunk001Sub000Block137Part019

theorem surrogateDiagonalTailChunk001Sub000Block137Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block137Part019CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block137Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block137Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block137Part019CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block137Part019SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block137Part019] using hcert

def TailChunk001Sub000Block137Part020SupportExplicit : Finset ℕ :=
  ([22165] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block137Part020 : ℚ :=
  (33126523817 : ℚ) / 2150338461696000000

def SurrogateDiagonalTailChunk001Sub000Block137Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22165
    = surrogateDiagTailX0RatChunk001Sub000Block137Part020

theorem surrogateDiagonalTailChunk001Sub000Block137Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block137Part020CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block137Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block137Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block137Part020CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block137Part020SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block137Part020] using hcert

def TailChunk001Sub000Block137Part021SupportExplicit : Finset ℕ :=
  ([22166] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block137Part021 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block137Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22166
    = surrogateDiagTailX0RatChunk001Sub000Block137Part021

theorem surrogateDiagonalTailChunk001Sub000Block137Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block137Part021CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block137Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block137Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block137Part021CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block137Part021SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block137Part021] using hcert

def TailChunk001Sub000Block137Part022SupportExplicit : Finset ℕ :=
  ([22169] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block137Part022 : ℚ :=
  (627284378375 : ℚ) / 162796666136583104064

def SurrogateDiagonalTailChunk001Sub000Block137Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22169
    = surrogateDiagTailX0RatChunk001Sub000Block137Part022

theorem surrogateDiagonalTailChunk001Sub000Block137Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block137Part022CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block137Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block137Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block137Part022CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block137Part022SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block137Part022] using hcert

def TailChunk001Sub000Block137Part023SupportExplicit : Finset ℕ :=
  ([22170] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block137Part023 : ℚ :=
  (318569337875 : ℚ) / 1012723760310091776

def SurrogateDiagonalTailChunk001Sub000Block137Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22170
    = surrogateDiagTailX0RatChunk001Sub000Block137Part023

theorem surrogateDiagonalTailChunk001Sub000Block137Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block137Part023CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block137Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block137Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block137Part023CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block137Part023SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block137Part023] using hcert

def TailChunk001Sub000Block137Part024SupportExplicit : Finset ℕ :=
  ([22171] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block137Part024 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block137Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22171
    = surrogateDiagTailX0RatChunk001Sub000Block137Part024

theorem surrogateDiagonalTailChunk001Sub000Block137Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block137Part024CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block137Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block137Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block137Part024CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block137Part024SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block137Part024] using hcert

def surrogateDiagonalTailChunk001Sub000Block137HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block137Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block137Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block137Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block137Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block137Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block137Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block137Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block137Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block137Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block137Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block137Head : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block137Part000
    + surrogateDiagTailX0RatChunk001Sub000Block137Part001
    + surrogateDiagTailX0RatChunk001Sub000Block137Part002
    + surrogateDiagTailX0RatChunk001Sub000Block137Part003
    + surrogateDiagTailX0RatChunk001Sub000Block137Part004
    + surrogateDiagTailX0RatChunk001Sub000Block137Part005
    + surrogateDiagTailX0RatChunk001Sub000Block137Part006
    + surrogateDiagTailX0RatChunk001Sub000Block137Part007
    + surrogateDiagTailX0RatChunk001Sub000Block137Part008
    + surrogateDiagTailX0RatChunk001Sub000Block137Part009

def surrogateDiagonalTailChunk001Sub000Block137MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block137Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block137Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block137Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block137Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block137Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block137Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block137Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block137Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block137Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block137Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block137Mid : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block137Part010
    + surrogateDiagTailX0RatChunk001Sub000Block137Part011
    + surrogateDiagTailX0RatChunk001Sub000Block137Part012
    + surrogateDiagTailX0RatChunk001Sub000Block137Part013
    + surrogateDiagTailX0RatChunk001Sub000Block137Part014
    + surrogateDiagTailX0RatChunk001Sub000Block137Part015
    + surrogateDiagTailX0RatChunk001Sub000Block137Part016
    + surrogateDiagTailX0RatChunk001Sub000Block137Part017
    + surrogateDiagTailX0RatChunk001Sub000Block137Part018
    + surrogateDiagTailX0RatChunk001Sub000Block137Part019

def surrogateDiagonalTailChunk001Sub000Block137TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block137Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block137Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block137Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block137Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block137Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block137Tail : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block137Part020
    + surrogateDiagTailX0RatChunk001Sub000Block137Part021
    + surrogateDiagTailX0RatChunk001Sub000Block137Part022
    + surrogateDiagTailX0RatChunk001Sub000Block137Part023
    + surrogateDiagTailX0RatChunk001Sub000Block137Part024

def surrogateDiagonalTailChunk001Sub000Block137Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk001Sub000Block137HeadSum X0
    + surrogateDiagonalTailChunk001Sub000Block137MidSum X0
    + surrogateDiagonalTailChunk001Sub000Block137TailSum X0

def surrogateDiagTailX0RatChunk001Sub000Block137 : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block137Part000
    + surrogateDiagTailX0RatChunk001Sub000Block137Part001
    + surrogateDiagTailX0RatChunk001Sub000Block137Part002
    + surrogateDiagTailX0RatChunk001Sub000Block137Part003
    + surrogateDiagTailX0RatChunk001Sub000Block137Part004
    + surrogateDiagTailX0RatChunk001Sub000Block137Part005
    + surrogateDiagTailX0RatChunk001Sub000Block137Part006
    + surrogateDiagTailX0RatChunk001Sub000Block137Part007
    + surrogateDiagTailX0RatChunk001Sub000Block137Part008
    + surrogateDiagTailX0RatChunk001Sub000Block137Part009
    + surrogateDiagTailX0RatChunk001Sub000Block137Part010
    + surrogateDiagTailX0RatChunk001Sub000Block137Part011
    + surrogateDiagTailX0RatChunk001Sub000Block137Part012
    + surrogateDiagTailX0RatChunk001Sub000Block137Part013
    + surrogateDiagTailX0RatChunk001Sub000Block137Part014
    + surrogateDiagTailX0RatChunk001Sub000Block137Part015
    + surrogateDiagTailX0RatChunk001Sub000Block137Part016
    + surrogateDiagTailX0RatChunk001Sub000Block137Part017
    + surrogateDiagTailX0RatChunk001Sub000Block137Part018
    + surrogateDiagTailX0RatChunk001Sub000Block137Part019
    + surrogateDiagTailX0RatChunk001Sub000Block137Part020
    + surrogateDiagTailX0RatChunk001Sub000Block137Part021
    + surrogateDiagTailX0RatChunk001Sub000Block137Part022
    + surrogateDiagTailX0RatChunk001Sub000Block137Part023
    + surrogateDiagTailX0RatChunk001Sub000Block137Part024

theorem surrogateDiagTailX0RatChunk001Sub000Block137_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk001Sub000Block137Head + surrogateDiagTailX0RatChunk001Sub000Block137Mid + surrogateDiagTailX0RatChunk001Sub000Block137Tail =
      surrogateDiagTailX0RatChunk001Sub000Block137 := by
  unfold surrogateDiagTailX0RatChunk001Sub000Block137Head surrogateDiagTailX0RatChunk001Sub000Block137Mid surrogateDiagTailX0RatChunk001Sub000Block137Tail surrogateDiagTailX0RatChunk001Sub000Block137
  ring

def SurrogateDiagonalTailChunk001Sub000Block137HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block137HeadSum X0 = surrogateDiagTailX0RatChunk001Sub000Block137Head

def SurrogateDiagonalTailChunk001Sub000Block137MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block137MidSum X0 = surrogateDiagTailX0RatChunk001Sub000Block137Mid

def SurrogateDiagonalTailChunk001Sub000Block137TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block137TailSum X0 = surrogateDiagTailX0RatChunk001Sub000Block137Tail

theorem surrogateDiagonalTailChunk001Sub000Block137_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk001Sub000Block137HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk001Sub000Block137MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk001Sub000Block137TailCertificateAt X0) :
    surrogateDiagonalTailChunk001Sub000Block137Sum X0 = surrogateDiagTailX0RatChunk001Sub000Block137 := by
  unfold SurrogateDiagonalTailChunk001Sub000Block137HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk001Sub000Block137MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk001Sub000Block137TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk001Sub000Block137Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk001Sub000Block137_eq_head_add_mid_add_tail

/-- Block 138 covers tail-support indices [13450,13475) and q from 22173 to 22213. -/

def TailChunk001Sub000Block138Part000SupportExplicit : Finset ℕ :=
  ([22173] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block138Part000 : ℚ :=
  (3285615121825 : ℚ) / 95183958960296460288

def SurrogateDiagonalTailChunk001Sub000Block138Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22173
    = surrogateDiagTailX0RatChunk001Sub000Block138Part000

theorem surrogateDiagonalTailChunk001Sub000Block138Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block138Part000CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block138Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block138Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block138Part000CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block138Part000SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block138Part000] using hcert

def TailChunk001Sub000Block138Part001SupportExplicit : Finset ℕ :=
  ([22174] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block138Part001 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block138Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22174
    = surrogateDiagTailX0RatChunk001Sub000Block138Part001

theorem surrogateDiagonalTailChunk001Sub000Block138Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block138Part001CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block138Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block138Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block138Part001CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block138Part001SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block138Part001] using hcert

def TailChunk001Sub000Block138Part002SupportExplicit : Finset ℕ :=
  ([22177] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block138Part002 : ℚ :=
  (36306037 : ℚ) / 166718802958773120

def SurrogateDiagonalTailChunk001Sub000Block138Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22177
    = surrogateDiagTailX0RatChunk001Sub000Block138Part002

theorem surrogateDiagonalTailChunk001Sub000Block138Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block138Part002CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block138Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block138Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block138Part002CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block138Part002SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block138Part002] using hcert

def TailChunk001Sub000Block138Part003SupportExplicit : Finset ℕ :=
  ([22178] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block138Part003 : ℚ :=
  (275694382375 : ℚ) / 27321857515324735488

def SurrogateDiagonalTailChunk001Sub000Block138Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22178
    = surrogateDiagTailX0RatChunk001Sub000Block138Part003

theorem surrogateDiagonalTailChunk001Sub000Block138Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block138Part003CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block138Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block138Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block138Part003CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block138Part003SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block138Part003] using hcert

def TailChunk001Sub000Block138Part004SupportExplicit : Finset ℕ :=
  ([22179] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block138Part004 : ℚ :=
  (121990321525 : ℚ) / 4266155124254048256

def SurrogateDiagonalTailChunk001Sub000Block138Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22179
    = surrogateDiagTailX0RatChunk001Sub000Block138Part004

theorem surrogateDiagonalTailChunk001Sub000Block138Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block138Part004CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block138Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block138Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block138Part004CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block138Part004SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block138Part004] using hcert

def TailChunk001Sub000Block138Part005SupportExplicit : Finset ℕ :=
  ([22181] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block138Part005 : ℚ :=
  (1410145757 : ℚ) / 4354435384934400000

def SurrogateDiagonalTailChunk001Sub000Block138Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22181
    = surrogateDiagTailX0RatChunk001Sub000Block138Part005

theorem surrogateDiagonalTailChunk001Sub000Block138Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block138Part005CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block138Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block138Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block138Part005CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block138Part005SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block138Part005] using hcert

def TailChunk001Sub000Block138Part006SupportExplicit : Finset ℕ :=
  ([22182] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block138Part006 : ℚ :=
  (30514324825 : ℚ) / 266634695265878016

def SurrogateDiagonalTailChunk001Sub000Block138Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22182
    = surrogateDiagTailX0RatChunk001Sub000Block138Part006

theorem surrogateDiagonalTailChunk001Sub000Block138Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block138Part006CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block138Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block138Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block138Part006CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block138Part006SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block138Part006] using hcert

def TailChunk001Sub000Block138Part007SupportExplicit : Finset ℕ :=
  ([22183] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block138Part007 : ℚ :=
  (628075970075 : ℚ) / 163208418485310849024

def SurrogateDiagonalTailChunk001Sub000Block138Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22183
    = surrogateDiagTailX0RatChunk001Sub000Block138Part007

theorem surrogateDiagonalTailChunk001Sub000Block138Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block138Part007CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block138Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block138Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block138Part007CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block138Part007SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block138Part007] using hcert

def TailChunk001Sub000Block138Part008SupportExplicit : Finset ℕ :=
  ([22186] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block138Part008 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block138Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22186
    = surrogateDiagTailX0RatChunk001Sub000Block138Part008

theorem surrogateDiagonalTailChunk001Sub000Block138Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block138Part008CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block138Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block138Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block138Part008CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block138Part008SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block138Part008] using hcert

def TailChunk001Sub000Block138Part009SupportExplicit : Finset ℕ :=
  ([22187] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block138Part009 : ℚ :=
  (4370688199 : ℚ) / 2360211495557529600

def SurrogateDiagonalTailChunk001Sub000Block138Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22187
    = surrogateDiagTailX0RatChunk001Sub000Block138Part009

theorem surrogateDiagonalTailChunk001Sub000Block138Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block138Part009CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block138Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block138Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block138Part009CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block138Part009SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block138Part009] using hcert

def TailChunk001Sub000Block138Part010SupportExplicit : Finset ℕ :=
  ([22189] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block138Part010 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block138Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22189
    = surrogateDiagTailX0RatChunk001Sub000Block138Part010

theorem surrogateDiagonalTailChunk001Sub000Block138Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block138Part010CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block138Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block138Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block138Part010CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block138Part010SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block138Part010] using hcert

def TailChunk001Sub000Block138Part011SupportExplicit : Finset ℕ :=
  ([22190] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block138Part011 : ℚ :=
  (825020296375 : ℚ) / 8272183433133293568

def SurrogateDiagonalTailChunk001Sub000Block138Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22190
    = surrogateDiagTailX0RatChunk001Sub000Block138Part011

theorem surrogateDiagonalTailChunk001Sub000Block138Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block138Part011CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block138Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block138Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block138Part011CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block138Part011SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block138Part011] using hcert

def TailChunk001Sub000Block138Part012SupportExplicit : Finset ℕ :=
  ([22191] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block138Part012 : ℚ :=
  (6355197725 : ℚ) / 168653441452621824

def SurrogateDiagonalTailChunk001Sub000Block138Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22191
    = surrogateDiagTailX0RatChunk001Sub000Block138Part012

theorem surrogateDiagonalTailChunk001Sub000Block138Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block138Part012CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block138Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block138Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block138Part012CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block138Part012SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block138Part012] using hcert

def TailChunk001Sub000Block138Part013SupportExplicit : Finset ℕ :=
  ([22193] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block138Part013 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block138Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22193
    = surrogateDiagTailX0RatChunk001Sub000Block138Part013

theorem surrogateDiagonalTailChunk001Sub000Block138Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block138Part013CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block138Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block138Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block138Part013CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block138Part013SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block138Part013] using hcert

def TailChunk001Sub000Block138Part014SupportExplicit : Finset ℕ :=
  ([22195] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block138Part014 : ℚ :=
  (457755757825 : ℚ) / 67926808120289918976

def SurrogateDiagonalTailChunk001Sub000Block138Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22195
    = surrogateDiagTailX0RatChunk001Sub000Block138Part014

theorem surrogateDiagonalTailChunk001Sub000Block138Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block138Part014CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block138Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block138Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block138Part014CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block138Part014SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block138Part014] using hcert

def TailChunk001Sub000Block138Part015SupportExplicit : Finset ℕ :=
  ([22198] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block138Part015 : ℚ :=
  (106797679 : ℚ) / 8604937744220160

def SurrogateDiagonalTailChunk001Sub000Block138Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22198
    = surrogateDiagTailX0RatChunk001Sub000Block138Part015

theorem surrogateDiagonalTailChunk001Sub000Block138Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block138Part015CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block138Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block138Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block138Part015CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block138Part015SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block138Part015] using hcert

def TailChunk001Sub000Block138Part016SupportExplicit : Finset ℕ :=
  ([22199] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block138Part016 : ℚ :=
  (6924011 : ℚ) / 35117402108006400

def SurrogateDiagonalTailChunk001Sub000Block138Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22199
    = surrogateDiagTailX0RatChunk001Sub000Block138Part016

theorem surrogateDiagonalTailChunk001Sub000Block138Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block138Part016CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block138Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block138Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block138Part016CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block138Part016SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block138Part016] using hcert

def TailChunk001Sub000Block138Part017SupportExplicit : Finset ℕ :=
  ([22202] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block138Part017 : ℚ :=
  (217252461925 : ℚ) / 29614006845139058688

def SurrogateDiagonalTailChunk001Sub000Block138Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22202
    = surrogateDiagTailX0RatChunk001Sub000Block138Part017

theorem surrogateDiagonalTailChunk001Sub000Block138Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block138Part017CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block138Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block138Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block138Part017CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block138Part017SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block138Part017] using hcert

def TailChunk001Sub000Block138Part018SupportExplicit : Finset ℕ :=
  ([22205] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block138Part018 : ℚ :=
  (266670407 : ℚ) / 53788194617425920

def SurrogateDiagonalTailChunk001Sub000Block138Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22205
    = surrogateDiagTailX0RatChunk001Sub000Block138Part018

theorem surrogateDiagonalTailChunk001Sub000Block138Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block138Part018CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block138Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block138Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block138Part018CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block138Part018SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block138Part018] using hcert

def TailChunk001Sub000Block138Part019SupportExplicit : Finset ℕ :=
  ([22206] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block138Part019 : ℚ :=
  (171250019 : ℚ) / 1499628665760000

def SurrogateDiagonalTailChunk001Sub000Block138Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22206
    = surrogateDiagTailX0RatChunk001Sub000Block138Part019

theorem surrogateDiagonalTailChunk001Sub000Block138Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block138Part019CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block138Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block138Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block138Part019CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block138Part019SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block138Part019] using hcert

def TailChunk001Sub000Block138Part020SupportExplicit : Finset ℕ :=
  ([22207] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block138Part020 : ℚ :=
  (147113057725 : ℚ) / 558142843407583070208

def SurrogateDiagonalTailChunk001Sub000Block138Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22207
    = surrogateDiagTailX0RatChunk001Sub000Block138Part020

theorem surrogateDiagonalTailChunk001Sub000Block138Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block138Part020CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block138Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block138Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block138Part020CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block138Part020SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block138Part020] using hcert

def TailChunk001Sub000Block138Part021SupportExplicit : Finset ℕ :=
  ([22209] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block138Part021 : ℚ :=
  (5248123585 : ℚ) / 130540092593799168

def SurrogateDiagonalTailChunk001Sub000Block138Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22209
    = surrogateDiagTailX0RatChunk001Sub000Block138Part021

theorem surrogateDiagonalTailChunk001Sub000Block138Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block138Part021CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block138Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block138Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block138Part021CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block138Part021SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block138Part021] using hcert

def TailChunk001Sub000Block138Part022SupportExplicit : Finset ℕ :=
  ([22210] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block138Part022 : ℚ :=
  (8229029983 : ℚ) / 207308666754662400

def SurrogateDiagonalTailChunk001Sub000Block138Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22210
    = surrogateDiagTailX0RatChunk001Sub000Block138Part022

theorem surrogateDiagonalTailChunk001Sub000Block138Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block138Part022CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block138Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block138Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block138Part022CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block138Part022SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block138Part022] using hcert

def TailChunk001Sub000Block138Part023SupportExplicit : Finset ℕ :=
  ([22211] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block138Part023 : ℚ :=
  (1436730716425 : ℚ) / 258317740339969148928

def SurrogateDiagonalTailChunk001Sub000Block138Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22211
    = surrogateDiagTailX0RatChunk001Sub000Block138Part023

theorem surrogateDiagonalTailChunk001Sub000Block138Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block138Part023CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block138Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block138Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block138Part023CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block138Part023SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block138Part023] using hcert

def TailChunk001Sub000Block138Part024SupportExplicit : Finset ℕ :=
  ([22213] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block138Part024 : ℚ :=
  (101435578075 : ℚ) / 573919761749369683968

def SurrogateDiagonalTailChunk001Sub000Block138Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22213
    = surrogateDiagTailX0RatChunk001Sub000Block138Part024

theorem surrogateDiagonalTailChunk001Sub000Block138Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block138Part024CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block138Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block138Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block138Part024CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block138Part024SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block138Part024] using hcert

def surrogateDiagonalTailChunk001Sub000Block138HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block138Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block138Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block138Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block138Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block138Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block138Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block138Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block138Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block138Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block138Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block138Head : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block138Part000
    + surrogateDiagTailX0RatChunk001Sub000Block138Part001
    + surrogateDiagTailX0RatChunk001Sub000Block138Part002
    + surrogateDiagTailX0RatChunk001Sub000Block138Part003
    + surrogateDiagTailX0RatChunk001Sub000Block138Part004
    + surrogateDiagTailX0RatChunk001Sub000Block138Part005
    + surrogateDiagTailX0RatChunk001Sub000Block138Part006
    + surrogateDiagTailX0RatChunk001Sub000Block138Part007
    + surrogateDiagTailX0RatChunk001Sub000Block138Part008
    + surrogateDiagTailX0RatChunk001Sub000Block138Part009

def surrogateDiagonalTailChunk001Sub000Block138MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block138Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block138Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block138Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block138Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block138Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block138Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block138Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block138Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block138Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block138Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block138Mid : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block138Part010
    + surrogateDiagTailX0RatChunk001Sub000Block138Part011
    + surrogateDiagTailX0RatChunk001Sub000Block138Part012
    + surrogateDiagTailX0RatChunk001Sub000Block138Part013
    + surrogateDiagTailX0RatChunk001Sub000Block138Part014
    + surrogateDiagTailX0RatChunk001Sub000Block138Part015
    + surrogateDiagTailX0RatChunk001Sub000Block138Part016
    + surrogateDiagTailX0RatChunk001Sub000Block138Part017
    + surrogateDiagTailX0RatChunk001Sub000Block138Part018
    + surrogateDiagTailX0RatChunk001Sub000Block138Part019

def surrogateDiagonalTailChunk001Sub000Block138TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block138Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block138Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block138Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block138Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block138Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block138Tail : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block138Part020
    + surrogateDiagTailX0RatChunk001Sub000Block138Part021
    + surrogateDiagTailX0RatChunk001Sub000Block138Part022
    + surrogateDiagTailX0RatChunk001Sub000Block138Part023
    + surrogateDiagTailX0RatChunk001Sub000Block138Part024

def surrogateDiagonalTailChunk001Sub000Block138Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk001Sub000Block138HeadSum X0
    + surrogateDiagonalTailChunk001Sub000Block138MidSum X0
    + surrogateDiagonalTailChunk001Sub000Block138TailSum X0

def surrogateDiagTailX0RatChunk001Sub000Block138 : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block138Part000
    + surrogateDiagTailX0RatChunk001Sub000Block138Part001
    + surrogateDiagTailX0RatChunk001Sub000Block138Part002
    + surrogateDiagTailX0RatChunk001Sub000Block138Part003
    + surrogateDiagTailX0RatChunk001Sub000Block138Part004
    + surrogateDiagTailX0RatChunk001Sub000Block138Part005
    + surrogateDiagTailX0RatChunk001Sub000Block138Part006
    + surrogateDiagTailX0RatChunk001Sub000Block138Part007
    + surrogateDiagTailX0RatChunk001Sub000Block138Part008
    + surrogateDiagTailX0RatChunk001Sub000Block138Part009
    + surrogateDiagTailX0RatChunk001Sub000Block138Part010
    + surrogateDiagTailX0RatChunk001Sub000Block138Part011
    + surrogateDiagTailX0RatChunk001Sub000Block138Part012
    + surrogateDiagTailX0RatChunk001Sub000Block138Part013
    + surrogateDiagTailX0RatChunk001Sub000Block138Part014
    + surrogateDiagTailX0RatChunk001Sub000Block138Part015
    + surrogateDiagTailX0RatChunk001Sub000Block138Part016
    + surrogateDiagTailX0RatChunk001Sub000Block138Part017
    + surrogateDiagTailX0RatChunk001Sub000Block138Part018
    + surrogateDiagTailX0RatChunk001Sub000Block138Part019
    + surrogateDiagTailX0RatChunk001Sub000Block138Part020
    + surrogateDiagTailX0RatChunk001Sub000Block138Part021
    + surrogateDiagTailX0RatChunk001Sub000Block138Part022
    + surrogateDiagTailX0RatChunk001Sub000Block138Part023
    + surrogateDiagTailX0RatChunk001Sub000Block138Part024

theorem surrogateDiagTailX0RatChunk001Sub000Block138_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk001Sub000Block138Head + surrogateDiagTailX0RatChunk001Sub000Block138Mid + surrogateDiagTailX0RatChunk001Sub000Block138Tail =
      surrogateDiagTailX0RatChunk001Sub000Block138 := by
  unfold surrogateDiagTailX0RatChunk001Sub000Block138Head surrogateDiagTailX0RatChunk001Sub000Block138Mid surrogateDiagTailX0RatChunk001Sub000Block138Tail surrogateDiagTailX0RatChunk001Sub000Block138
  ring

def SurrogateDiagonalTailChunk001Sub000Block138HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block138HeadSum X0 = surrogateDiagTailX0RatChunk001Sub000Block138Head

def SurrogateDiagonalTailChunk001Sub000Block138MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block138MidSum X0 = surrogateDiagTailX0RatChunk001Sub000Block138Mid

def SurrogateDiagonalTailChunk001Sub000Block138TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block138TailSum X0 = surrogateDiagTailX0RatChunk001Sub000Block138Tail

theorem surrogateDiagonalTailChunk001Sub000Block138_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk001Sub000Block138HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk001Sub000Block138MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk001Sub000Block138TailCertificateAt X0) :
    surrogateDiagonalTailChunk001Sub000Block138Sum X0 = surrogateDiagTailX0RatChunk001Sub000Block138 := by
  unfold SurrogateDiagonalTailChunk001Sub000Block138HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk001Sub000Block138MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk001Sub000Block138TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk001Sub000Block138Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk001Sub000Block138_eq_head_add_mid_add_tail

/-- Block 139 covers tail-support indices [13475,13500) and q from 22214 to 22258. -/

def TailChunk001Sub000Block139Part000SupportExplicit : Finset ℕ :=
  ([22214] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block139Part000 : ℚ :=
  (3969045125 : ℚ) / 1022733443311024704

def SurrogateDiagonalTailChunk001Sub000Block139Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22214
    = surrogateDiagTailX0RatChunk001Sub000Block139Part000

theorem surrogateDiagonalTailChunk001Sub000Block139Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block139Part000CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block139Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block139Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block139Part000CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block139Part000SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block139Part000] using hcert

def TailChunk001Sub000Block139Part001SupportExplicit : Finset ℕ :=
  ([22215] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block139Part001 : ℚ :=
  (19181938113 : ℚ) / 327598880797491200

def SurrogateDiagonalTailChunk001Sub000Block139Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22215
    = surrogateDiagTailX0RatChunk001Sub000Block139Part001

theorem surrogateDiagonalTailChunk001Sub000Block139Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block139Part001CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block139Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block139Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block139Part001CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block139Part001SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block139Part001] using hcert

def TailChunk001Sub000Block139Part002SupportExplicit : Finset ℕ :=
  ([22217] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block139Part002 : ℚ :=
  (39322955075 : ℚ) / 31519206301950001152

def SurrogateDiagonalTailChunk001Sub000Block139Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22217
    = surrogateDiagTailX0RatChunk001Sub000Block139Part002

theorem surrogateDiagonalTailChunk001Sub000Block139Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block139Part002CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block139Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block139Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block139Part002CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block139Part002SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block139Part002] using hcert

def TailChunk001Sub000Block139Part003SupportExplicit : Finset ℕ :=
  ([22219] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block139Part003 : ℚ :=
  (431151961075 : ℚ) / 476737700385406844928

def SurrogateDiagonalTailChunk001Sub000Block139Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22219
    = surrogateDiagTailX0RatChunk001Sub000Block139Part003

theorem surrogateDiagonalTailChunk001Sub000Block139Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block139Part003CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block139Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block139Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block139Part003CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block139Part003SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block139Part003] using hcert

def TailChunk001Sub000Block139Part004SupportExplicit : Finset ℕ :=
  ([22222] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block139Part004 : ℚ :=
  (376950631 : ℚ) / 136076105779200000

def SurrogateDiagonalTailChunk001Sub000Block139Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22222
    = surrogateDiagTailX0RatChunk001Sub000Block139Part004

theorem surrogateDiagonalTailChunk001Sub000Block139Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block139Part004CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block139Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block139Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block139Part004CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block139Part004SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block139Part004] using hcert

def TailChunk001Sub000Block139Part005SupportExplicit : Finset ℕ :=
  ([22223] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block139Part005 : ℚ :=
  (316807663 : ℚ) / 1517071771065876480

def SurrogateDiagonalTailChunk001Sub000Block139Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22223
    = surrogateDiagTailX0RatChunk001Sub000Block139Part005

theorem surrogateDiagonalTailChunk001Sub000Block139Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block139Part005CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block139Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block139Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block139Part005CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block139Part005SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block139Part005] using hcert

def TailChunk001Sub000Block139Part006SupportExplicit : Finset ℕ :=
  ([22226] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block139Part006 : ℚ :=
  (1929668265625 : ℚ) / 9530941380979732992

def SurrogateDiagonalTailChunk001Sub000Block139Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22226
    = surrogateDiagTailX0RatChunk001Sub000Block139Part006

theorem surrogateDiagonalTailChunk001Sub000Block139Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block139Part006CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block139Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block139Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block139Part006CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block139Part006SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block139Part006] using hcert

def TailChunk001Sub000Block139Part007SupportExplicit : Finset ℕ :=
  ([22227] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block139Part007 : ℚ :=
  (2731822171 : ℚ) / 84879653880268800

def SurrogateDiagonalTailChunk001Sub000Block139Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22227
    = surrogateDiagTailX0RatChunk001Sub000Block139Part007

theorem surrogateDiagonalTailChunk001Sub000Block139Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block139Part007CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block139Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block139Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block139Part007CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block139Part007SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block139Part007] using hcert

def TailChunk001Sub000Block139Part008SupportExplicit : Finset ℕ :=
  ([22229] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block139Part008 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block139Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22229
    = surrogateDiagTailX0RatChunk001Sub000Block139Part008

theorem surrogateDiagonalTailChunk001Sub000Block139Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block139Part008CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block139Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block139Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block139Part008CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block139Part008SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block139Part008] using hcert

def TailChunk001Sub000Block139Part009SupportExplicit : Finset ℕ :=
  ([22231] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block139Part009 : ℚ :=
  (89257891 : ℚ) / 43010087721484800

def SurrogateDiagonalTailChunk001Sub000Block139Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22231
    = surrogateDiagTailX0RatChunk001Sub000Block139Part009

theorem surrogateDiagonalTailChunk001Sub000Block139Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block139Part009CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block139Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block139Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block139Part009CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block139Part009SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block139Part009] using hcert

def TailChunk001Sub000Block139Part010SupportExplicit : Finset ℕ :=
  ([22233] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block139Part010 : ℚ :=
  (13729525009 : ℚ) / 482480388079859520

def SurrogateDiagonalTailChunk001Sub000Block139Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22233
    = surrogateDiagTailX0RatChunk001Sub000Block139Part010

theorem surrogateDiagonalTailChunk001Sub000Block139Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block139Part010CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block139Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block139Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block139Part010CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block139Part010SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block139Part010] using hcert

def TailChunk001Sub000Block139Part011SupportExplicit : Finset ℕ :=
  ([22234] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block139Part011 : ℚ :=
  (1931057640625 : ℚ) / 9544672250544520992

def SurrogateDiagonalTailChunk001Sub000Block139Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22234
    = surrogateDiagTailX0RatChunk001Sub000Block139Part011

theorem surrogateDiagonalTailChunk001Sub000Block139Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block139Part011CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block139Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block139Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block139Part011CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block139Part011SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block139Part011] using hcert

def TailChunk001Sub000Block139Part012SupportExplicit : Finset ℕ :=
  ([22235] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block139Part012 : ℚ :=
  (1236682881625 : ℚ) / 250117833180599175168

def SurrogateDiagonalTailChunk001Sub000Block139Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22235
    = surrogateDiagTailX0RatChunk001Sub000Block139Part012

theorem surrogateDiagonalTailChunk001Sub000Block139Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block139Part012CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block139Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block139Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block139Part012CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block139Part012SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block139Part012] using hcert

def TailChunk001Sub000Block139Part013SupportExplicit : Finset ℕ :=
  ([22237] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block139Part013 : ℚ :=
  (79043113 : ℚ) / 201594230784000000

def SurrogateDiagonalTailChunk001Sub000Block139Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22237
    = surrogateDiagTailX0RatChunk001Sub000Block139Part013

theorem surrogateDiagonalTailChunk001Sub000Block139Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block139Part013CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block139Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block139Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block139Part013CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block139Part013SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block139Part013] using hcert

def TailChunk001Sub000Block139Part014SupportExplicit : Finset ℕ :=
  ([22238] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block139Part014 : ℚ :=
  (1931752515625 : ℚ) / 9551543246217520722

def SurrogateDiagonalTailChunk001Sub000Block139Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22238
    = surrogateDiagTailX0RatChunk001Sub000Block139Part014

theorem surrogateDiagonalTailChunk001Sub000Block139Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block139Part014CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block139Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block139Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block139Part014CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block139Part014SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block139Part014] using hcert

def TailChunk001Sub000Block139Part015SupportExplicit : Finset ℕ :=
  ([22241] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block139Part015 : ℚ :=
  (298242874525 : ℚ) / 510065662407509755008

def SurrogateDiagonalTailChunk001Sub000Block139Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22241
    = surrogateDiagTailX0RatChunk001Sub000Block139Part015

theorem surrogateDiagonalTailChunk001Sub000Block139Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block139Part015CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block139Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block139Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block139Part015CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block139Part015SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block139Part015] using hcert

def TailChunk001Sub000Block139Part016SupportExplicit : Finset ℕ :=
  ([22242] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block139Part016 : ℚ :=
  (13464673 : ℚ) / 18500580016128

def SurrogateDiagonalTailChunk001Sub000Block139Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22242
    = surrogateDiagTailX0RatChunk001Sub000Block139Part016

theorem surrogateDiagonalTailChunk001Sub000Block139Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block139Part016CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block139Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block139Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block139Part016CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block139Part016SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block139Part016] using hcert

def TailChunk001Sub000Block139Part017SupportExplicit : Finset ℕ :=
  ([22243] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block139Part017 : ℚ :=
  (824940692725 : ℚ) / 360658309491542458368

def SurrogateDiagonalTailChunk001Sub000Block139Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22243
    = surrogateDiagTailX0RatChunk001Sub000Block139Part017

theorem surrogateDiagonalTailChunk001Sub000Block139Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block139Part017CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block139Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block139Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block139Part017CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block139Part017SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block139Part017] using hcert

def TailChunk001Sub000Block139Part018SupportExplicit : Finset ℕ :=
  ([22245] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block139Part018 : ℚ :=
  (45079151125 : ℚ) / 771968620927775232

def SurrogateDiagonalTailChunk001Sub000Block139Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22245
    = surrogateDiagTailX0RatChunk001Sub000Block139Part018

theorem surrogateDiagonalTailChunk001Sub000Block139Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block139Part018CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block139Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block139Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block139Part018CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block139Part018SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block139Part018] using hcert

def TailChunk001Sub000Block139Part019SupportExplicit : Finset ℕ :=
  ([22247] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block139Part019 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block139Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22247
    = surrogateDiagTailX0RatChunk001Sub000Block139Part019

theorem surrogateDiagonalTailChunk001Sub000Block139Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block139Part019CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block139Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block139Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block139Part019CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block139Part019SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block139Part019] using hcert

def TailChunk001Sub000Block139Part020SupportExplicit : Finset ℕ :=
  ([22249] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block139Part020 : ℚ :=
  (8661231311 : ℚ) / 9837626319685569600

def SurrogateDiagonalTailChunk001Sub000Block139Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22249
    = surrogateDiagTailX0RatChunk001Sub000Block139Part020

theorem surrogateDiagonalTailChunk001Sub000Block139Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block139Part020CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block139Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block139Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block139Part020CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block139Part020SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block139Part020] using hcert

def TailChunk001Sub000Block139Part021SupportExplicit : Finset ℕ :=
  ([22251] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block139Part021 : ℚ :=
  (859485250525 : ℚ) / 30252811039008694272

def SurrogateDiagonalTailChunk001Sub000Block139Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22251
    = surrogateDiagTailX0RatChunk001Sub000Block139Part021

theorem surrogateDiagonalTailChunk001Sub000Block139Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block139Part021CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block139Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block139Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block139Part021CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block139Part021SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block139Part021] using hcert

def TailChunk001Sub000Block139Part022SupportExplicit : Finset ℕ :=
  ([22254] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block139Part022 : ℚ :=
  (2148978653975 : ℚ) / 3781601379876086784

def SurrogateDiagonalTailChunk001Sub000Block139Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22254
    = surrogateDiagTailX0RatChunk001Sub000Block139Part022

theorem surrogateDiagonalTailChunk001Sub000Block139Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block139Part022CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block139Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block139Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block139Part022CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block139Part022SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block139Part022] using hcert

def TailChunk001Sub000Block139Part023SupportExplicit : Finset ℕ :=
  ([22255] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block139Part023 : ℚ :=
  (3303751683 : ℚ) / 669384420780800000

def SurrogateDiagonalTailChunk001Sub000Block139Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22255
    = surrogateDiagTailX0RatChunk001Sub000Block139Part023

theorem surrogateDiagonalTailChunk001Sub000Block139Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block139Part023CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block139Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block139Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block139Part023CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block139Part023SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block139Part023] using hcert

def TailChunk001Sub000Block139Part024SupportExplicit : Finset ℕ :=
  ([22258] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block139Part024 : ℚ :=
  (58589258879 : ℚ) / 266154596790503040

def SurrogateDiagonalTailChunk001Sub000Block139Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22258
    = surrogateDiagTailX0RatChunk001Sub000Block139Part024

theorem surrogateDiagonalTailChunk001Sub000Block139Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block139Part024CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block139Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block139Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block139Part024CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block139Part024SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block139Part024] using hcert

def surrogateDiagonalTailChunk001Sub000Block139HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block139Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block139Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block139Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block139Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block139Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block139Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block139Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block139Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block139Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block139Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block139Head : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block139Part000
    + surrogateDiagTailX0RatChunk001Sub000Block139Part001
    + surrogateDiagTailX0RatChunk001Sub000Block139Part002
    + surrogateDiagTailX0RatChunk001Sub000Block139Part003
    + surrogateDiagTailX0RatChunk001Sub000Block139Part004
    + surrogateDiagTailX0RatChunk001Sub000Block139Part005
    + surrogateDiagTailX0RatChunk001Sub000Block139Part006
    + surrogateDiagTailX0RatChunk001Sub000Block139Part007
    + surrogateDiagTailX0RatChunk001Sub000Block139Part008
    + surrogateDiagTailX0RatChunk001Sub000Block139Part009

def surrogateDiagonalTailChunk001Sub000Block139MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block139Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block139Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block139Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block139Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block139Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block139Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block139Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block139Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block139Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block139Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block139Mid : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block139Part010
    + surrogateDiagTailX0RatChunk001Sub000Block139Part011
    + surrogateDiagTailX0RatChunk001Sub000Block139Part012
    + surrogateDiagTailX0RatChunk001Sub000Block139Part013
    + surrogateDiagTailX0RatChunk001Sub000Block139Part014
    + surrogateDiagTailX0RatChunk001Sub000Block139Part015
    + surrogateDiagTailX0RatChunk001Sub000Block139Part016
    + surrogateDiagTailX0RatChunk001Sub000Block139Part017
    + surrogateDiagTailX0RatChunk001Sub000Block139Part018
    + surrogateDiagTailX0RatChunk001Sub000Block139Part019

def surrogateDiagonalTailChunk001Sub000Block139TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block139Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block139Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block139Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block139Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block139Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block139Tail : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block139Part020
    + surrogateDiagTailX0RatChunk001Sub000Block139Part021
    + surrogateDiagTailX0RatChunk001Sub000Block139Part022
    + surrogateDiagTailX0RatChunk001Sub000Block139Part023
    + surrogateDiagTailX0RatChunk001Sub000Block139Part024

def surrogateDiagonalTailChunk001Sub000Block139Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk001Sub000Block139HeadSum X0
    + surrogateDiagonalTailChunk001Sub000Block139MidSum X0
    + surrogateDiagonalTailChunk001Sub000Block139TailSum X0

def surrogateDiagTailX0RatChunk001Sub000Block139 : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block139Part000
    + surrogateDiagTailX0RatChunk001Sub000Block139Part001
    + surrogateDiagTailX0RatChunk001Sub000Block139Part002
    + surrogateDiagTailX0RatChunk001Sub000Block139Part003
    + surrogateDiagTailX0RatChunk001Sub000Block139Part004
    + surrogateDiagTailX0RatChunk001Sub000Block139Part005
    + surrogateDiagTailX0RatChunk001Sub000Block139Part006
    + surrogateDiagTailX0RatChunk001Sub000Block139Part007
    + surrogateDiagTailX0RatChunk001Sub000Block139Part008
    + surrogateDiagTailX0RatChunk001Sub000Block139Part009
    + surrogateDiagTailX0RatChunk001Sub000Block139Part010
    + surrogateDiagTailX0RatChunk001Sub000Block139Part011
    + surrogateDiagTailX0RatChunk001Sub000Block139Part012
    + surrogateDiagTailX0RatChunk001Sub000Block139Part013
    + surrogateDiagTailX0RatChunk001Sub000Block139Part014
    + surrogateDiagTailX0RatChunk001Sub000Block139Part015
    + surrogateDiagTailX0RatChunk001Sub000Block139Part016
    + surrogateDiagTailX0RatChunk001Sub000Block139Part017
    + surrogateDiagTailX0RatChunk001Sub000Block139Part018
    + surrogateDiagTailX0RatChunk001Sub000Block139Part019
    + surrogateDiagTailX0RatChunk001Sub000Block139Part020
    + surrogateDiagTailX0RatChunk001Sub000Block139Part021
    + surrogateDiagTailX0RatChunk001Sub000Block139Part022
    + surrogateDiagTailX0RatChunk001Sub000Block139Part023
    + surrogateDiagTailX0RatChunk001Sub000Block139Part024

theorem surrogateDiagTailX0RatChunk001Sub000Block139_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk001Sub000Block139Head + surrogateDiagTailX0RatChunk001Sub000Block139Mid + surrogateDiagTailX0RatChunk001Sub000Block139Tail =
      surrogateDiagTailX0RatChunk001Sub000Block139 := by
  unfold surrogateDiagTailX0RatChunk001Sub000Block139Head surrogateDiagTailX0RatChunk001Sub000Block139Mid surrogateDiagTailX0RatChunk001Sub000Block139Tail surrogateDiagTailX0RatChunk001Sub000Block139
  ring

def SurrogateDiagonalTailChunk001Sub000Block139HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block139HeadSum X0 = surrogateDiagTailX0RatChunk001Sub000Block139Head

def SurrogateDiagonalTailChunk001Sub000Block139MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block139MidSum X0 = surrogateDiagTailX0RatChunk001Sub000Block139Mid

def SurrogateDiagonalTailChunk001Sub000Block139TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block139TailSum X0 = surrogateDiagTailX0RatChunk001Sub000Block139Tail

theorem surrogateDiagonalTailChunk001Sub000Block139_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk001Sub000Block139HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk001Sub000Block139MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk001Sub000Block139TailCertificateAt X0) :
    surrogateDiagonalTailChunk001Sub000Block139Sum X0 = surrogateDiagTailX0RatChunk001Sub000Block139 := by
  unfold SurrogateDiagonalTailChunk001Sub000Block139HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk001Sub000Block139MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk001Sub000Block139TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk001Sub000Block139Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk001Sub000Block139_eq_head_add_mid_add_tail

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

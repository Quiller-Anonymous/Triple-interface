import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0TailPilot25

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

open scoped BigOperators

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

/- Generated direct-term certificate blocks for tail chunk 000, subchunk 000, blocks [93,94). -/

/- Block 093 covers tail-support indices [2325,2350) and q from 3877 to 3914. -/

def TailChunk000Sub000Block093Part000SupportExplicit : Finset ℕ :=
  ([3877] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block093Part000 : ℚ :=
  (1878515346775 : ℚ) / 564367417006658688

def SurrogateDiagonalTailChunk000Sub000Block093Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3877
    = surrogateDiagTailX0RatChunk000Sub000Block093Part000

theorem surrogateDiagonalTailChunk000Sub000Block093Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block093Part000CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block093Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block093Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block093Part000CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block093Part000SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block093Part000] using hcert

def TailChunk000Sub000Block093Part001SupportExplicit : Finset ℕ :=
  ([3878] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block093Part001 : ℚ :=
  (5440542125 : ℚ) / 174118305977856

def SurrogateDiagonalTailChunk000Sub000Block093Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3878
    = surrogateDiagTailX0RatChunk000Sub000Block093Part001

theorem surrogateDiagonalTailChunk000Sub000Block093Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block093Part001CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block093Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block093Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block093Part001CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block093Part001SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block093Part001] using hcert

def TailChunk000Sub000Block093Part002SupportExplicit : Finset ℕ :=
  ([3881] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block093Part002 : ℚ :=
  (75295742839 : ℚ) / 22668028635187200

def SurrogateDiagonalTailChunk000Sub000Block093Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3881
    = surrogateDiagTailX0RatChunk000Sub000Block093Part002

theorem surrogateDiagonalTailChunk000Sub000Block093Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block093Part002CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block093Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block093Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block093Part002CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block093Part002SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block093Part002] using hcert

def TailChunk000Sub000Block093Part003SupportExplicit : Finset ℕ :=
  ([3882] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block093Part003 : ℚ :=
  (13061937775 : ℚ) / 204926440452672

def SurrogateDiagonalTailChunk000Sub000Block093Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3882
    = surrogateDiagTailX0RatChunk000Sub000Block093Part003

theorem surrogateDiagonalTailChunk000Sub000Block093Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block093Part003CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block093Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block093Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block093Part003CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block093Part003SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block093Part003] using hcert

def TailChunk000Sub000Block093Part004SupportExplicit : Finset ℕ :=
  ([3883] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block093Part004 : ℚ :=
  (21934295847 : ℚ) / 5118423885414400

def SurrogateDiagonalTailChunk000Sub000Block093Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3883
    = surrogateDiagTailX0RatChunk000Sub000Block093Part004

theorem surrogateDiagonalTailChunk000Sub000Block093Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block093Part004CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block093Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block093Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block093Part004CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block093Part004SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block093Part004] using hcert

def TailChunk000Sub000Block093Part005SupportExplicit : Finset ℕ :=
  ([3885] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block093Part005 : ℚ :=
  (115578155425 : ℚ) / 5573677292716032

def SurrogateDiagonalTailChunk000Sub000Block093Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3885
    = surrogateDiagTailX0RatChunk000Sub000Block093Part005

theorem surrogateDiagonalTailChunk000Sub000Block093Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block093Part005CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block093Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block093Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block093Part005CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block093Part005SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block093Part005] using hcert

def TailChunk000Sub000Block093Part006SupportExplicit : Finset ℕ :=
  ([3886] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block093Part006 : ℚ :=
  (227732364725 : ℚ) / 14581584897352704

def SurrogateDiagonalTailChunk000Sub000Block093Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3886
    = surrogateDiagTailX0RatChunk000Sub000Block093Part006

theorem surrogateDiagonalTailChunk000Sub000Block093Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block093Part006CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block093Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block093Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block093Part006CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block093Part006SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block093Part006] using hcert

def TailChunk000Sub000Block093Part007SupportExplicit : Finset ℕ :=
  ([3889] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block093Part007 : ℚ :=
  (236317515625 : ℚ) / 142847252802772992

def SurrogateDiagonalTailChunk000Sub000Block093Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3889
    = surrogateDiagTailX0RatChunk000Sub000Block093Part007

theorem surrogateDiagonalTailChunk000Sub000Block093Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block093Part007CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block093Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block093Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block093Part007CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block093Part007SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block093Part007] using hcert

def TailChunk000Sub000Block093Part008SupportExplicit : Finset ℕ :=
  ([3890] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block093Part008 : ℚ :=
  (202949669525 : ℚ) / 7253769163259904

def SurrogateDiagonalTailChunk000Sub000Block093Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3890
    = surrogateDiagTailX0RatChunk000Sub000Block093Part008

theorem surrogateDiagonalTailChunk000Sub000Block093Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block093Part008CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block093Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block093Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block093Part008CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block093Part008SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block093Part008] using hcert

def TailChunk000Sub000Block093Part009SupportExplicit : Finset ℕ :=
  ([3891] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block093Part009 : ℚ :=
  (735582751225 : ℚ) / 112866965177499648

def SurrogateDiagonalTailChunk000Sub000Block093Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3891
    = surrogateDiagTailX0RatChunk000Sub000Block093Part009

theorem surrogateDiagonalTailChunk000Sub000Block093Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block093Part009CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block093Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block093Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block093Part009CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block093Part009SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block093Part009] using hcert

def TailChunk000Sub000Block093Part010SupportExplicit : Finset ℕ :=
  ([3893] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block093Part010 : ℚ :=
  (905118563725 : ℚ) / 442839322337476608

def SurrogateDiagonalTailChunk000Sub000Block093Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3893
    = surrogateDiagTailX0RatChunk000Sub000Block093Part010

theorem surrogateDiagonalTailChunk000Sub000Block093Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block093Part010CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block093Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block093Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block093Part010CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block093Part010SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block093Part010] using hcert

def TailChunk000Sub000Block093Part011SupportExplicit : Finset ℕ :=
  ([3894] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block093Part011 : ℚ :=
  (7924712039 : ℚ) / 90550074393600

def SurrogateDiagonalTailChunk000Sub000Block093Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3894
    = surrogateDiagTailX0RatChunk000Sub000Block093Part011

theorem surrogateDiagonalTailChunk000Sub000Block093Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block093Part011CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block093Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block093Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block093Part011CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block093Part011SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block093Part011] using hcert

def TailChunk000Sub000Block093Part012SupportExplicit : Finset ℕ :=
  ([3895] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block093Part012 : ℚ :=
  (15615268223 : ℚ) / 3440541538713600

def SurrogateDiagonalTailChunk000Sub000Block093Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3895
    = surrogateDiagTailX0RatChunk000Sub000Block093Part012

theorem surrogateDiagonalTailChunk000Sub000Block093Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block093Part012CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block093Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block093Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block093Part012CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block093Part012SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block093Part012] using hcert

def TailChunk000Sub000Block093Part013SupportExplicit : Finset ℕ :=
  ([3898] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block093Part013 : ℚ :=
  (237317597475 : ℚ) / 12002215336087936

def SurrogateDiagonalTailChunk000Sub000Block093Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3898
    = surrogateDiagTailX0RatChunk000Sub000Block093Part013

theorem surrogateDiagonalTailChunk000Sub000Block093Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block093Part013CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block093Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block093Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block093Part013CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block093Part013SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block093Part013] using hcert

def TailChunk000Sub000Block093Part014SupportExplicit : Finset ℕ :=
  ([3899] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block093Part014 : ℚ :=
  (852150657625 : ℚ) / 309692741610129408

def SurrogateDiagonalTailChunk000Sub000Block093Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3899
    = surrogateDiagTailX0RatChunk000Sub000Block093Part014

theorem surrogateDiagonalTailChunk000Sub000Block093Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block093Part014CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block093Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block093Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block093Part014CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block093Part014SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block093Part014] using hcert

def TailChunk000Sub000Block093Part015SupportExplicit : Finset ℕ :=
  ([3901] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block093Part015 : ℚ :=
  (464201925725 : ℚ) / 253095019762496064

def SurrogateDiagonalTailChunk000Sub000Block093Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3901
    = surrogateDiagTailX0RatChunk000Sub000Block093Part015

theorem surrogateDiagonalTailChunk000Sub000Block093Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block093Part015CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block093Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block093Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block093Part015CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block093Part015SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block093Part015] using hcert

def TailChunk000Sub000Block093Part016SupportExplicit : Finset ℕ :=
  ([3902] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block093Part016 : ℚ :=
  (19028198599 : ℚ) / 1446189805125000

def SurrogateDiagonalTailChunk000Sub000Block093Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3902
    = surrogateDiagTailX0RatChunk000Sub000Block093Part016

theorem surrogateDiagonalTailChunk000Sub000Block093Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block093Part016CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block093Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block093Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block093Part016CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block093Part016SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block093Part016] using hcert

def TailChunk000Sub000Block093Part017SupportExplicit : Finset ℕ :=
  ([3903] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block093Part017 : ℚ :=
  (29605061197 : ℚ) / 4570673952000000

def SurrogateDiagonalTailChunk000Sub000Block093Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3903
    = surrogateDiagTailX0RatChunk000Sub000Block093Part017

theorem surrogateDiagonalTailChunk000Sub000Block093Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block093Part017CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block093Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block093Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block093Part017CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block093Part017SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block093Part017] using hcert

def TailChunk000Sub000Block093Part018SupportExplicit : Finset ℕ :=
  ([3905] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block093Part018 : ℚ :=
  (76557081 : ℚ) / 16009868000000

def SurrogateDiagonalTailChunk000Sub000Block093Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3905
    = surrogateDiagTailX0RatChunk000Sub000Block093Part018

theorem surrogateDiagonalTailChunk000Sub000Block093Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block093Part018CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block093Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block093Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block093Part018CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block093Part018SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block093Part018] using hcert

def TailChunk000Sub000Block093Part019SupportExplicit : Finset ℕ :=
  ([3907] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block093Part019 : ℚ :=
  (1907699508775 : ℚ) / 582043997349605448

def SurrogateDiagonalTailChunk000Sub000Block093Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3907
    = surrogateDiagTailX0RatChunk000Sub000Block093Part019

theorem surrogateDiagonalTailChunk000Sub000Block093Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block093Part019CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block093Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block093Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block093Part019CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block093Part019SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block093Part019] using hcert

def TailChunk000Sub000Block093Part020SupportExplicit : Finset ℕ :=
  ([3909] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block093Part020 : ℚ :=
  (530127067475 : ℚ) / 57485826898726464

def SurrogateDiagonalTailChunk000Sub000Block093Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3909
    = surrogateDiagTailX0RatChunk000Sub000Block093Part020

theorem surrogateDiagonalTailChunk000Sub000Block093Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block093Part020CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block093Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block093Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block093Part020CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block093Part020SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block093Part020] using hcert

def TailChunk000Sub000Block093Part021SupportExplicit : Finset ℕ :=
  ([3910] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block093Part021 : ℚ :=
  (493081347775 : ℚ) / 9827373859995648

def SurrogateDiagonalTailChunk000Sub000Block093Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3910
    = surrogateDiagTailX0RatChunk000Sub000Block093Part021

theorem surrogateDiagonalTailChunk000Sub000Block093Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block093Part021CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block093Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block093Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block093Part021CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block093Part021SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block093Part021] using hcert

def TailChunk000Sub000Block093Part022SupportExplicit : Finset ℕ :=
  ([3911] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block093Part022 : ℚ :=
  (76464309079 : ℚ) / 23377274681032200

def SurrogateDiagonalTailChunk000Sub000Block093Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3911
    = surrogateDiagTailX0RatChunk000Sub000Block093Part022

theorem surrogateDiagonalTailChunk000Sub000Block093Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block093Part022CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block093Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block093Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block093Part022CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block093Part022SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block093Part022] using hcert

def TailChunk000Sub000Block093Part023SupportExplicit : Finset ℕ :=
  ([3913] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block093Part023 : ℚ :=
  (1342060542925 : ℚ) / 209099987184549888

def SurrogateDiagonalTailChunk000Sub000Block093Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3913
    = surrogateDiagTailX0RatChunk000Sub000Block093Part023

theorem surrogateDiagonalTailChunk000Sub000Block093Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block093Part023CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block093Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block093Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block093Part023CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block093Part023SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block093Part023] using hcert

def TailChunk000Sub000Block093Part024SupportExplicit : Finset ℕ :=
  ([3914] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block093Part024 : ℚ :=
  (166746275125 : ℚ) / 7103257769240352

def SurrogateDiagonalTailChunk000Sub000Block093Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3914
    = surrogateDiagTailX0RatChunk000Sub000Block093Part024

theorem surrogateDiagonalTailChunk000Sub000Block093Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block093Part024CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block093Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block093Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block093Part024CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block093Part024SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block093Part024] using hcert

def surrogateDiagonalTailChunk000Sub000Block093HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block093Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block093Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block093Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block093Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block093Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block093Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block093Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block093Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block093Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block093Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block093Head : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block093Part000
    + surrogateDiagTailX0RatChunk000Sub000Block093Part001
    + surrogateDiagTailX0RatChunk000Sub000Block093Part002
    + surrogateDiagTailX0RatChunk000Sub000Block093Part003
    + surrogateDiagTailX0RatChunk000Sub000Block093Part004
    + surrogateDiagTailX0RatChunk000Sub000Block093Part005
    + surrogateDiagTailX0RatChunk000Sub000Block093Part006
    + surrogateDiagTailX0RatChunk000Sub000Block093Part007
    + surrogateDiagTailX0RatChunk000Sub000Block093Part008
    + surrogateDiagTailX0RatChunk000Sub000Block093Part009

def surrogateDiagonalTailChunk000Sub000Block093MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block093Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block093Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block093Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block093Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block093Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block093Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block093Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block093Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block093Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block093Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block093Mid : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block093Part010
    + surrogateDiagTailX0RatChunk000Sub000Block093Part011
    + surrogateDiagTailX0RatChunk000Sub000Block093Part012
    + surrogateDiagTailX0RatChunk000Sub000Block093Part013
    + surrogateDiagTailX0RatChunk000Sub000Block093Part014
    + surrogateDiagTailX0RatChunk000Sub000Block093Part015
    + surrogateDiagTailX0RatChunk000Sub000Block093Part016
    + surrogateDiagTailX0RatChunk000Sub000Block093Part017
    + surrogateDiagTailX0RatChunk000Sub000Block093Part018
    + surrogateDiagTailX0RatChunk000Sub000Block093Part019

def surrogateDiagonalTailChunk000Sub000Block093TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block093Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block093Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block093Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block093Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block093Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block093Tail : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block093Part020
    + surrogateDiagTailX0RatChunk000Sub000Block093Part021
    + surrogateDiagTailX0RatChunk000Sub000Block093Part022
    + surrogateDiagTailX0RatChunk000Sub000Block093Part023
    + surrogateDiagTailX0RatChunk000Sub000Block093Part024

def surrogateDiagonalTailChunk000Sub000Block093Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub000Block093HeadSum X0
    + surrogateDiagonalTailChunk000Sub000Block093MidSum X0
    + surrogateDiagonalTailChunk000Sub000Block093TailSum X0

def surrogateDiagTailX0RatChunk000Sub000Block093 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block093Part000
    + surrogateDiagTailX0RatChunk000Sub000Block093Part001
    + surrogateDiagTailX0RatChunk000Sub000Block093Part002
    + surrogateDiagTailX0RatChunk000Sub000Block093Part003
    + surrogateDiagTailX0RatChunk000Sub000Block093Part004
    + surrogateDiagTailX0RatChunk000Sub000Block093Part005
    + surrogateDiagTailX0RatChunk000Sub000Block093Part006
    + surrogateDiagTailX0RatChunk000Sub000Block093Part007
    + surrogateDiagTailX0RatChunk000Sub000Block093Part008
    + surrogateDiagTailX0RatChunk000Sub000Block093Part009
    + surrogateDiagTailX0RatChunk000Sub000Block093Part010
    + surrogateDiagTailX0RatChunk000Sub000Block093Part011
    + surrogateDiagTailX0RatChunk000Sub000Block093Part012
    + surrogateDiagTailX0RatChunk000Sub000Block093Part013
    + surrogateDiagTailX0RatChunk000Sub000Block093Part014
    + surrogateDiagTailX0RatChunk000Sub000Block093Part015
    + surrogateDiagTailX0RatChunk000Sub000Block093Part016
    + surrogateDiagTailX0RatChunk000Sub000Block093Part017
    + surrogateDiagTailX0RatChunk000Sub000Block093Part018
    + surrogateDiagTailX0RatChunk000Sub000Block093Part019
    + surrogateDiagTailX0RatChunk000Sub000Block093Part020
    + surrogateDiagTailX0RatChunk000Sub000Block093Part021
    + surrogateDiagTailX0RatChunk000Sub000Block093Part022
    + surrogateDiagTailX0RatChunk000Sub000Block093Part023
    + surrogateDiagTailX0RatChunk000Sub000Block093Part024

theorem surrogateDiagTailX0RatChunk000Sub000Block093_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk000Sub000Block093Head + surrogateDiagTailX0RatChunk000Sub000Block093Mid + surrogateDiagTailX0RatChunk000Sub000Block093Tail =
      surrogateDiagTailX0RatChunk000Sub000Block093 := by
  unfold surrogateDiagTailX0RatChunk000Sub000Block093Head surrogateDiagTailX0RatChunk000Sub000Block093Mid surrogateDiagTailX0RatChunk000Sub000Block093Tail surrogateDiagTailX0RatChunk000Sub000Block093
  ring

def SurrogateDiagonalTailChunk000Sub000Block093HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block093HeadSum X0 = surrogateDiagTailX0RatChunk000Sub000Block093Head

def SurrogateDiagonalTailChunk000Sub000Block093MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block093MidSum X0 = surrogateDiagTailX0RatChunk000Sub000Block093Mid

def SurrogateDiagonalTailChunk000Sub000Block093TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block093TailSum X0 = surrogateDiagTailX0RatChunk000Sub000Block093Tail

theorem surrogateDiagonalTailChunk000Sub000Block093_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk000Sub000Block093HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk000Sub000Block093MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk000Sub000Block093TailCertificateAt X0) :
    surrogateDiagonalTailChunk000Sub000Block093Sum X0 = surrogateDiagTailX0RatChunk000Sub000Block093 := by
  unfold SurrogateDiagonalTailChunk000Sub000Block093HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk000Sub000Block093MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk000Sub000Block093TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk000Sub000Block093Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk000Sub000Block093_eq_head_add_mid_add_tail

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

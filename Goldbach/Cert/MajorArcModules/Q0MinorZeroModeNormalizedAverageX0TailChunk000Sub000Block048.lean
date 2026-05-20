import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0TailPilot25

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

open scoped BigOperators

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

/- Generated direct-term certificate blocks for tail chunk 000, subchunk 000, blocks [48,49). -/

/- Block 048 covers tail-support indices [1200,1225) and q from 2027 to 2067. -/

def TailChunk000Sub000Block048Part000SupportExplicit : Finset ℕ :=
  ([2027] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block048Part000 : ℚ :=
  (256692844275 : ℚ) / 14043112281657496

def SurrogateDiagonalTailChunk000Sub000Block048Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2027
    = surrogateDiagTailX0RatChunk000Sub000Block048Part000

theorem surrogateDiagonalTailChunk000Sub000Block048Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block048Part000CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block048Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block048Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block048Part000CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block048Part000SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block048Part000] using hcert

def TailChunk000Sub000Block048Part001SupportExplicit : Finset ℕ :=
  ([2029] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block048Part001 : ℚ :=
  (514502203975 : ℚ) / 42295938072755328

def SurrogateDiagonalTailChunk000Sub000Block048Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2029
    = surrogateDiagTailX0RatChunk000Sub000Block048Part001

theorem surrogateDiagonalTailChunk000Sub000Block048Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block048Part001CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block048Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block048Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block048Part001CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block048Part001SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block048Part001] using hcert

def TailChunk000Sub000Block048Part002SupportExplicit : Finset ℕ :=
  ([2030] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block048Part002 : ℚ :=
  (23387792525 : ℚ) / 56658026299392

def SurrogateDiagonalTailChunk000Sub000Block048Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2030
    = surrogateDiagTailX0RatChunk000Sub000Block048Part002

theorem surrogateDiagonalTailChunk000Sub000Block048Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block048Part002CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block048Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block048Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block048Part002CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block048Part002SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block048Part002] using hcert

def TailChunk000Sub000Block048Part003SupportExplicit : Finset ℕ :=
  ([2031] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block048Part003 : ℚ :=
  (185992983425 : ℚ) / 4177376599778304

def SurrogateDiagonalTailChunk000Sub000Block048Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2031
    = surrogateDiagTailX0RatChunk000Sub000Block048Part003

theorem surrogateDiagonalTailChunk000Sub000Block048Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block048Part003CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block048Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block048Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block048Part003CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block048Part003SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block048Part003] using hcert

def TailChunk000Sub000Block048Part004SupportExplicit : Finset ℕ :=
  ([2033] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block048Part004 : ℚ :=
  (239724588475 : ℚ) / 11046357275769216

def SurrogateDiagonalTailChunk000Sub000Block048Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2033
    = surrogateDiagTailX0RatChunk000Sub000Block048Part004

theorem surrogateDiagonalTailChunk000Sub000Block048Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block048Part004CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block048Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block048Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block048Part004CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block048Part004SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block048Part004] using hcert

def TailChunk000Sub000Block048Part005SupportExplicit : Finset ℕ :=
  ([2035] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block048Part005 : ℚ :=
  (10260652889 : ℚ) / 215033846169600

def SurrogateDiagonalTailChunk000Sub000Block048Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2035
    = surrogateDiagTailX0RatChunk000Sub000Block048Part005

theorem surrogateDiagonalTailChunk000Sub000Block048Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block048Part005CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block048Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block048Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block048Part005CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block048Part005SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block048Part005] using hcert

def TailChunk000Sub000Block048Part006SupportExplicit : Finset ℕ :=
  ([2037] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block048Part006 : ℚ :=
  (2007301175 : ℚ) / 27184525737984

def SurrogateDiagonalTailChunk000Sub000Block048Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2037
    = surrogateDiagTailX0RatChunk000Sub000Block048Part006

theorem surrogateDiagonalTailChunk000Sub000Block048Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block048Part006CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block048Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block048Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block048Part006CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block048Part006SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block048Part006] using hcert

def TailChunk000Sub000Block048Part007SupportExplicit : Finset ℕ :=
  ([2038] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block048Part007 : ℚ :=
  (162114111125 : ℚ) / 1342727783078244

def SurrogateDiagonalTailChunk000Sub000Block048Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2038
    = surrogateDiagTailX0RatChunk000Sub000Block048Part007

theorem surrogateDiagonalTailChunk000Sub000Block048Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block048Part007CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block048Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block048Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block048Part007CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block048Part007SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block048Part007] using hcert

def TailChunk000Sub000Block048Part008SupportExplicit : Finset ℕ :=
  ([2039] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block048Part008 : ℚ :=
  (519586186975 : ℚ) / 43136368201370568

def SurrogateDiagonalTailChunk000Sub000Block048Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2039
    = surrogateDiagTailX0RatChunk000Sub000Block048Part008

theorem surrogateDiagonalTailChunk000Sub000Block048Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block048Part008CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block048Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block048Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block048Part008CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block048Part008SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block048Part008] using hcert

def TailChunk000Sub000Block048Part009SupportExplicit : Finset ℕ :=
  ([2041] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block048Part009 : ℚ :=
  (8704094825 : ℚ) / 379109980274688

def SurrogateDiagonalTailChunk000Sub000Block048Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2041
    = surrogateDiagTailX0RatChunk000Sub000Block048Part009

theorem surrogateDiagonalTailChunk000Sub000Block048Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block048Part009CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block048Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block048Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block048Part009CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block048Part009SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block048Part009] using hcert

def TailChunk000Sub000Block048Part010SupportExplicit : Finset ℕ :=
  ([2042] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block048Part010 : ℚ :=
  (1302008809 : ℚ) / 10826486464320

def SurrogateDiagonalTailChunk000Sub000Block048Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2042
    = surrogateDiagTailX0RatChunk000Sub000Block048Part010

theorem surrogateDiagonalTailChunk000Sub000Block048Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block048Part010CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block048Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block048Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block048Part010CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block048Part010SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block048Part010] using hcert

def TailChunk000Sub000Block048Part011SupportExplicit : Finset ℕ :=
  ([2045] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block048Part011 : ℚ :=
  (48699508025 : ℚ) / 1970901713682432

def SurrogateDiagonalTailChunk000Sub000Block048Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2045
    = surrogateDiagTailX0RatChunk000Sub000Block048Part011

theorem surrogateDiagonalTailChunk000Sub000Block048Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block048Part011CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block048Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block048Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block048Part011CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block048Part011SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block048Part011] using hcert

def TailChunk000Sub000Block048Part012SupportExplicit : Finset ℕ :=
  ([2046] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block048Part012 : ℚ :=
  (3715216799 : ℚ) / 6481296000000

def SurrogateDiagonalTailChunk000Sub000Block048Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2046
    = surrogateDiagTailX0RatChunk000Sub000Block048Part012

theorem surrogateDiagonalTailChunk000Sub000Block048Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block048Part012CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block048Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block048Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block048Part012CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block048Part012SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block048Part012] using hcert

def TailChunk000Sub000Block048Part013SupportExplicit : Finset ℕ :=
  ([2047] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block048Part013 : ℚ :=
  (83669993625 : ℚ) / 5854597195808768

def SurrogateDiagonalTailChunk000Sub000Block048Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2047
    = surrogateDiagTailX0RatChunk000Sub000Block048Part013

theorem surrogateDiagonalTailChunk000Sub000Block048Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block048Part013CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block048Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block048Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block048Part013CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block048Part013SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block048Part013] using hcert

def TailChunk000Sub000Block048Part014SupportExplicit : Finset ℕ :=
  ([2049] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block048Part014 : ℚ :=
  (94651859725 : ℚ) / 2163836034430752

def SurrogateDiagonalTailChunk000Sub000Block048Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2049
    = surrogateDiagTailX0RatChunk000Sub000Block048Part014

theorem surrogateDiagonalTailChunk000Sub000Block048Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block048Part014CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block048Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block048Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block048Part014CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block048Part014SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block048Part014] using hcert

def TailChunk000Sub000Block048Part015SupportExplicit : Finset ℕ :=
  ([2051] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block048Part015 : ℚ :=
  (326058977825 : ℚ) / 11779673971221504

def SurrogateDiagonalTailChunk000Sub000Block048Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2051
    = surrogateDiagTailX0RatChunk000Sub000Block048Part015

theorem surrogateDiagonalTailChunk000Sub000Block048Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block048Part015CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block048Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block048Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block048Part015CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block048Part015SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block048Part015] using hcert

def TailChunk000Sub000Block048Part016SupportExplicit : Finset ℕ :=
  ([2053] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block048Part016 : ℚ :=
  (526745754775 : ℚ) / 44333935453127808

def SurrogateDiagonalTailChunk000Sub000Block048Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2053
    = surrogateDiagTailX0RatChunk000Sub000Block048Part016

theorem surrogateDiagonalTailChunk000Sub000Block048Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block048Part016CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block048Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block048Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block048Part016CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block048Part016SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block048Part016] using hcert

def TailChunk000Sub000Block048Part017SupportExplicit : Finset ℕ :=
  ([2054] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block048Part017 : ℚ :=
  (299598986425 : ℚ) / 1919244275140608

def SurrogateDiagonalTailChunk000Sub000Block048Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2054
    = surrogateDiagTailX0RatChunk000Sub000Block048Part017

theorem surrogateDiagonalTailChunk000Sub000Block048Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block048Part017CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block048Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block048Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block048Part017CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block048Part017SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block048Part017] using hcert

def TailChunk000Sub000Block048Part018SupportExplicit : Finset ℕ :=
  ([2055] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block048Part018 : ℚ :=
  (329677666975 : ℚ) / 3503825268768768

def SurrogateDiagonalTailChunk000Sub000Block048Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2055
    = surrogateDiagTailX0RatChunk000Sub000Block048Part018

theorem surrogateDiagonalTailChunk000Sub000Block048Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block048Part018CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block048Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block048Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block048Part018CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block048Part018SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block048Part018] using hcert

def TailChunk000Sub000Block048Part019SupportExplicit : Finset ℕ :=
  ([2059] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block048Part019 : ℚ :=
  (29981145979 : ℚ) / 1476084213811200

def SurrogateDiagonalTailChunk000Sub000Block048Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2059
    = surrogateDiagTailX0RatChunk000Sub000Block048Part019

theorem surrogateDiagonalTailChunk000Sub000Block048Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block048Part019CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block048Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block048Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block048Part019CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block048Part019SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block048Part019] using hcert

def TailChunk000Sub000Block048Part020SupportExplicit : Finset ℕ :=
  ([2062] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block048Part020 : ℚ :=
  (1327638289 : ℚ) / 11257339117620

def SurrogateDiagonalTailChunk000Sub000Block048Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2062
    = surrogateDiagTailX0RatChunk000Sub000Block048Part020

theorem surrogateDiagonalTailChunk000Sub000Block048Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block048Part020CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block048Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block048Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block048Part020CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block048Part020SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block048Part020] using hcert

def TailChunk000Sub000Block048Part021SupportExplicit : Finset ℕ :=
  ([2063] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block048Part021 : ℚ :=
  (531889725775 : ℚ) / 45204482589540168

def SurrogateDiagonalTailChunk000Sub000Block048Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2063
    = surrogateDiagTailX0RatChunk000Sub000Block048Part021

theorem surrogateDiagonalTailChunk000Sub000Block048Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block048Part021CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block048Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block048Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block048Part021CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block048Part021SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block048Part021] using hcert

def TailChunk000Sub000Block048Part022SupportExplicit : Finset ℕ :=
  ([2065] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block048Part022 : ℚ :=
  (388013435875 : ℚ) / 9388231713128448

def SurrogateDiagonalTailChunk000Sub000Block048Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2065
    = surrogateDiagTailX0RatChunk000Sub000Block048Part022

theorem surrogateDiagonalTailChunk000Sub000Block048Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block048Part022CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block048Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block048Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block048Part022CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block048Part022SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block048Part022] using hcert

def TailChunk000Sub000Block048Part023SupportExplicit : Finset ℕ :=
  ([2066] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block048Part023 : ℚ :=
  (133306093325 : ℚ) / 1418128719750144

def SurrogateDiagonalTailChunk000Sub000Block048Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2066
    = surrogateDiagTailX0RatChunk000Sub000Block048Part023

theorem surrogateDiagonalTailChunk000Sub000Block048Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block048Part023CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block048Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block048Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block048Part023CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block048Part023SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block048Part023] using hcert

def TailChunk000Sub000Block048Part024SupportExplicit : Finset ℕ :=
  ([2067] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block048Part024 : ℚ :=
  (142119001925 : ℚ) / 2021919894798336

def SurrogateDiagonalTailChunk000Sub000Block048Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2067
    = surrogateDiagTailX0RatChunk000Sub000Block048Part024

theorem surrogateDiagonalTailChunk000Sub000Block048Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block048Part024CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block048Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block048Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block048Part024CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block048Part024SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block048Part024] using hcert

def surrogateDiagonalTailChunk000Sub000Block048HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block048Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block048Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block048Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block048Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block048Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block048Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block048Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block048Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block048Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block048Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block048Head : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block048Part000
    + surrogateDiagTailX0RatChunk000Sub000Block048Part001
    + surrogateDiagTailX0RatChunk000Sub000Block048Part002
    + surrogateDiagTailX0RatChunk000Sub000Block048Part003
    + surrogateDiagTailX0RatChunk000Sub000Block048Part004
    + surrogateDiagTailX0RatChunk000Sub000Block048Part005
    + surrogateDiagTailX0RatChunk000Sub000Block048Part006
    + surrogateDiagTailX0RatChunk000Sub000Block048Part007
    + surrogateDiagTailX0RatChunk000Sub000Block048Part008
    + surrogateDiagTailX0RatChunk000Sub000Block048Part009

def surrogateDiagonalTailChunk000Sub000Block048MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block048Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block048Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block048Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block048Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block048Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block048Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block048Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block048Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block048Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block048Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block048Mid : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block048Part010
    + surrogateDiagTailX0RatChunk000Sub000Block048Part011
    + surrogateDiagTailX0RatChunk000Sub000Block048Part012
    + surrogateDiagTailX0RatChunk000Sub000Block048Part013
    + surrogateDiagTailX0RatChunk000Sub000Block048Part014
    + surrogateDiagTailX0RatChunk000Sub000Block048Part015
    + surrogateDiagTailX0RatChunk000Sub000Block048Part016
    + surrogateDiagTailX0RatChunk000Sub000Block048Part017
    + surrogateDiagTailX0RatChunk000Sub000Block048Part018
    + surrogateDiagTailX0RatChunk000Sub000Block048Part019

def surrogateDiagonalTailChunk000Sub000Block048TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block048Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block048Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block048Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block048Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block048Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block048Tail : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block048Part020
    + surrogateDiagTailX0RatChunk000Sub000Block048Part021
    + surrogateDiagTailX0RatChunk000Sub000Block048Part022
    + surrogateDiagTailX0RatChunk000Sub000Block048Part023
    + surrogateDiagTailX0RatChunk000Sub000Block048Part024

def surrogateDiagonalTailChunk000Sub000Block048Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub000Block048HeadSum X0
    + surrogateDiagonalTailChunk000Sub000Block048MidSum X0
    + surrogateDiagonalTailChunk000Sub000Block048TailSum X0

def surrogateDiagTailX0RatChunk000Sub000Block048 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block048Part000
    + surrogateDiagTailX0RatChunk000Sub000Block048Part001
    + surrogateDiagTailX0RatChunk000Sub000Block048Part002
    + surrogateDiagTailX0RatChunk000Sub000Block048Part003
    + surrogateDiagTailX0RatChunk000Sub000Block048Part004
    + surrogateDiagTailX0RatChunk000Sub000Block048Part005
    + surrogateDiagTailX0RatChunk000Sub000Block048Part006
    + surrogateDiagTailX0RatChunk000Sub000Block048Part007
    + surrogateDiagTailX0RatChunk000Sub000Block048Part008
    + surrogateDiagTailX0RatChunk000Sub000Block048Part009
    + surrogateDiagTailX0RatChunk000Sub000Block048Part010
    + surrogateDiagTailX0RatChunk000Sub000Block048Part011
    + surrogateDiagTailX0RatChunk000Sub000Block048Part012
    + surrogateDiagTailX0RatChunk000Sub000Block048Part013
    + surrogateDiagTailX0RatChunk000Sub000Block048Part014
    + surrogateDiagTailX0RatChunk000Sub000Block048Part015
    + surrogateDiagTailX0RatChunk000Sub000Block048Part016
    + surrogateDiagTailX0RatChunk000Sub000Block048Part017
    + surrogateDiagTailX0RatChunk000Sub000Block048Part018
    + surrogateDiagTailX0RatChunk000Sub000Block048Part019
    + surrogateDiagTailX0RatChunk000Sub000Block048Part020
    + surrogateDiagTailX0RatChunk000Sub000Block048Part021
    + surrogateDiagTailX0RatChunk000Sub000Block048Part022
    + surrogateDiagTailX0RatChunk000Sub000Block048Part023
    + surrogateDiagTailX0RatChunk000Sub000Block048Part024

theorem surrogateDiagTailX0RatChunk000Sub000Block048_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk000Sub000Block048Head + surrogateDiagTailX0RatChunk000Sub000Block048Mid + surrogateDiagTailX0RatChunk000Sub000Block048Tail =
      surrogateDiagTailX0RatChunk000Sub000Block048 := by
  unfold surrogateDiagTailX0RatChunk000Sub000Block048Head surrogateDiagTailX0RatChunk000Sub000Block048Mid surrogateDiagTailX0RatChunk000Sub000Block048Tail surrogateDiagTailX0RatChunk000Sub000Block048
  ring

def SurrogateDiagonalTailChunk000Sub000Block048HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block048HeadSum X0 = surrogateDiagTailX0RatChunk000Sub000Block048Head

def SurrogateDiagonalTailChunk000Sub000Block048MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block048MidSum X0 = surrogateDiagTailX0RatChunk000Sub000Block048Mid

def SurrogateDiagonalTailChunk000Sub000Block048TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block048TailSum X0 = surrogateDiagTailX0RatChunk000Sub000Block048Tail

theorem surrogateDiagonalTailChunk000Sub000Block048_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk000Sub000Block048HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk000Sub000Block048MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk000Sub000Block048TailCertificateAt X0) :
    surrogateDiagonalTailChunk000Sub000Block048Sum X0 = surrogateDiagTailX0RatChunk000Sub000Block048 := by
  unfold SurrogateDiagonalTailChunk000Sub000Block048HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk000Sub000Block048MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk000Sub000Block048TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk000Sub000Block048Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk000Sub000Block048_eq_head_add_mid_add_tail

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

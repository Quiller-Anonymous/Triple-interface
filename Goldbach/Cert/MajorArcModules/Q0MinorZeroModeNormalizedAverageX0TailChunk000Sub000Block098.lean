import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0TailPilot25

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

open scoped BigOperators

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

/- Generated direct-term certificate blocks for tail chunk 000, subchunk 000, blocks [98,99). -/

/- Block 098 covers tail-support indices [2450,2475) and q from 4081 to 4119. -/

def TailChunk000Sub000Block098Part000SupportExplicit : Finset ℕ :=
  ([4081] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block098Part000 : ℚ :=
  (26265697 : ℚ) / 7290576543744

def SurrogateDiagonalTailChunk000Sub000Block098Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4081
    = surrogateDiagTailX0RatChunk000Sub000Block098Part000

theorem surrogateDiagonalTailChunk000Sub000Block098Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block098Part000CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block098Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block098Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block098Part000CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block098Part000SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block098Part000] using hcert

def TailChunk000Sub000Block098Part001SupportExplicit : Finset ℕ :=
  ([4082] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block098Part001 : ℚ :=
  (8704094825 : ℚ) / 379109980274688

def SurrogateDiagonalTailChunk000Sub000Block098Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4082
    = surrogateDiagTailX0RatChunk000Sub000Block098Part001

theorem surrogateDiagonalTailChunk000Sub000Block098Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block098Part001CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block098Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block098Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block098Part001CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block098Part001SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block098Part001] using hcert

def TailChunk000Sub000Block098Part002SupportExplicit : Finset ℕ :=
  ([4083] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block098Part002 : ℚ :=
  (32398539937 : ℚ) / 5474726982451200

def SurrogateDiagonalTailChunk000Sub000Block098Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4083
    = surrogateDiagTailX0RatChunk000Sub000Block098Part002

theorem surrogateDiagonalTailChunk000Sub000Block098Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block098Part002CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block098Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block098Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block098Part002CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block098Part002SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block098Part002] using hcert

def TailChunk000Sub000Block098Part003SupportExplicit : Finset ℕ :=
  ([4085] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block098Part003 : ℚ :=
  (26760911375 : ℚ) / 6534374599517184

def SurrogateDiagonalTailChunk000Sub000Block098Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4085
    = surrogateDiagTailX0RatChunk000Sub000Block098Part003

theorem surrogateDiagonalTailChunk000Sub000Block098Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block098Part003CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block098Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block098Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block098Part003CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block098Part003SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block098Part003] using hcert

def TailChunk000Sub000Block098Part004SupportExplicit : Finset ℕ :=
  ([4087] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block098Part004 : ℚ :=
  (2264371213 : ℚ) / 1366454228198400

def SurrogateDiagonalTailChunk000Sub000Block098Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4087
    = surrogateDiagTailX0RatChunk000Sub000Block098Part004

theorem surrogateDiagonalTailChunk000Sub000Block098Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block098Part004CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block098Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block098Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block098Part004CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block098Part004SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block098Part004] using hcert

def TailChunk000Sub000Block098Part005SupportExplicit : Finset ℕ :=
  ([4089] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block098Part005 : ℚ :=
  (11158770975 : ℚ) / 1595736587927552

def SurrogateDiagonalTailChunk000Sub000Block098Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4089
    = surrogateDiagTailX0RatChunk000Sub000Block098Part005

theorem surrogateDiagonalTailChunk000Sub000Block098Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block098Part005CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block098Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block098Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block098Part005CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block098Part005SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block098Part005] using hcert

def TailChunk000Sub000Block098Part006SupportExplicit : Finset ℕ :=
  ([4090] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block098Part006 : ℚ :=
  (48699508025 : ℚ) / 1970901713682432

def SurrogateDiagonalTailChunk000Sub000Block098Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4090
    = surrogateDiagTailX0RatChunk000Sub000Block098Part006

theorem surrogateDiagonalTailChunk000Sub000Block098Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block098Part006CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block098Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block098Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block098Part006CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block098Part006SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block098Part006] using hcert

def TailChunk000Sub000Block098Part007SupportExplicit : Finset ℕ :=
  ([4091] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block098Part007 : ℚ :=
  (418407025 : ℚ) / 279885295475922

def SurrogateDiagonalTailChunk000Sub000Block098Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4091
    = surrogateDiagTailX0RatChunk000Sub000Block098Part007

theorem surrogateDiagonalTailChunk000Sub000Block098Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block098Part007CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block098Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block098Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block098Part007CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block098Part007SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block098Part007] using hcert

def TailChunk000Sub000Block098Part008SupportExplicit : Finset ℕ :=
  ([4093] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block098Part008 : ℚ :=
  (261760140625 : ℚ) / 175270718788890912

def SurrogateDiagonalTailChunk000Sub000Block098Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4093
    = surrogateDiagTailX0RatChunk000Sub000Block098Part008

theorem surrogateDiagonalTailChunk000Sub000Block098Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block098Part008CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block098Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block098Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block098Part008CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block098Part008SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block098Part008] using hcert

def TailChunk000Sub000Block098Part009SupportExplicit : Finset ℕ :=
  ([4094] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block098Part009 : ℚ :=
  (83669993625 : ℚ) / 5854597195808768

def SurrogateDiagonalTailChunk000Sub000Block098Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4094
    = surrogateDiagTailX0RatChunk000Sub000Block098Part009

theorem surrogateDiagonalTailChunk000Sub000Block098Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block098Part009CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block098Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block098Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block098Part009CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block098Part009SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block098Part009] using hcert

def TailChunk000Sub000Block098Part010SupportExplicit : Finset ℕ :=
  ([4097] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block098Part010 : ℚ :=
  (39950764387 : ℚ) / 21747620590387200

def SurrogateDiagonalTailChunk000Sub000Block098Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4097
    = surrogateDiagTailX0RatChunk000Sub000Block098Part010

theorem surrogateDiagonalTailChunk000Sub000Block098Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block098Part010CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block098Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block098Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block098Part010CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block098Part010SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block098Part010] using hcert

def TailChunk000Sub000Block098Part011SupportExplicit : Finset ℕ :=
  ([4098] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block098Part011 : ℚ :=
  (94651859725 : ℚ) / 2163836034430752

def SurrogateDiagonalTailChunk000Sub000Block098Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4098
    = surrogateDiagTailX0RatChunk000Sub000Block098Part011

theorem surrogateDiagonalTailChunk000Sub000Block098Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block098Part011CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block098Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block098Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block098Part011CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block098Part011SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block098Part011] using hcert

def TailChunk000Sub000Block098Part012SupportExplicit : Finset ℕ :=
  ([4099] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block098Part012 : ℚ :=
  (2099805079975 : ℚ) / 705203850839694408

def SurrogateDiagonalTailChunk000Sub000Block098Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4099
    = surrogateDiagTailX0RatChunk000Sub000Block098Part012

theorem surrogateDiagonalTailChunk000Sub000Block098Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block098Part012CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block098Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block098Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block098Part012CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block098Part012SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block098Part012] using hcert

def TailChunk000Sub000Block098Part013SupportExplicit : Finset ℕ :=
  ([4101] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block098Part013 : ℚ :=
  (583493467475 : ℚ) / 69649763045895744

def SurrogateDiagonalTailChunk000Sub000Block098Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4101
    = surrogateDiagTailX0RatChunk000Sub000Block098Part013

theorem surrogateDiagonalTailChunk000Sub000Block098Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block098Part013CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block098Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block098Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block098Part013CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block098Part013SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block098Part013] using hcert

def TailChunk000Sub000Block098Part014SupportExplicit : Finset ℕ :=
  ([4102] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block098Part014 : ℚ :=
  (326058977825 : ℚ) / 11779673971221504

def SurrogateDiagonalTailChunk000Sub000Block098Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4102
    = surrogateDiagTailX0RatChunk000Sub000Block098Part014

theorem surrogateDiagonalTailChunk000Sub000Block098Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block098Part014CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block098Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block098Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block098Part014CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block098Part014SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block098Part014] using hcert

def TailChunk000Sub000Block098Part015SupportExplicit : Finset ℕ :=
  ([4103] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block098Part015 : ℚ :=
  (94362775 : ℚ) / 24714789009408

def SurrogateDiagonalTailChunk000Sub000Block098Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4103
    = surrogateDiagTailX0RatChunk000Sub000Block098Part015

theorem surrogateDiagonalTailChunk000Sub000Block098Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block098Part015CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block098Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block098Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block098Part015CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block098Part015SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block098Part015] using hcert

def TailChunk000Sub000Block098Part016SupportExplicit : Finset ℕ :=
  ([4105] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block098Part016 : ℚ :=
  (6057268399 : ℚ) / 1157663191941120

def SurrogateDiagonalTailChunk000Sub000Block098Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4105
    = surrogateDiagTailX0RatChunk000Sub000Block098Part016

theorem surrogateDiagonalTailChunk000Sub000Block098Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block098Part016CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block098Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block098Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block098Part016CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block098Part016SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block098Part016] using hcert

def TailChunk000Sub000Block098Part017SupportExplicit : Finset ℕ :=
  ([4106] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block098Part017 : ℚ :=
  (526745754775 : ℚ) / 44333935453127808

def SurrogateDiagonalTailChunk000Sub000Block098Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4106
    = surrogateDiagTailX0RatChunk000Sub000Block098Part017

theorem surrogateDiagonalTailChunk000Sub000Block098Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block098Part017CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block098Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block098Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block098Part017CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block098Part017SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block098Part017] using hcert

def TailChunk000Sub000Block098Part018SupportExplicit : Finset ℕ :=
  ([4109] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block098Part018 : ℚ :=
  (946382789125 : ℚ) / 382139846210544768

def SurrogateDiagonalTailChunk000Sub000Block098Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4109
    = surrogateDiagTailX0RatChunk000Sub000Block098Part018

theorem surrogateDiagonalTailChunk000Sub000Block098Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block098Part018CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block098Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block098Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block098Part018CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block098Part018SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block098Part018] using hcert

def TailChunk000Sub000Block098Part019SupportExplicit : Finset ℕ :=
  ([4110] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block098Part019 : ℚ :=
  (329677666975 : ℚ) / 3503825268768768

def SurrogateDiagonalTailChunk000Sub000Block098Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4110
    = surrogateDiagTailX0RatChunk000Sub000Block098Part019

theorem surrogateDiagonalTailChunk000Sub000Block098Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block098Part019CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block098Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block098Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block098Part019CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block098Part019SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block098Part019] using hcert

def TailChunk000Sub000Block098Part020SupportExplicit : Finset ℕ :=
  ([4111] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block098Part020 : ℚ :=
  (422508025 : ℚ) / 285400111018482

def SurrogateDiagonalTailChunk000Sub000Block098Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4111
    = surrogateDiagTailX0RatChunk000Sub000Block098Part020

theorem surrogateDiagonalTailChunk000Sub000Block098Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block098Part020CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block098Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block098Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block098Part020CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block098Part020SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block098Part020] using hcert

def TailChunk000Sub000Block098Part021SupportExplicit : Finset ℕ :=
  ([4115] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block098Part021 : ℚ :=
  (888254005375 : ℚ) / 292249713682925568

def SurrogateDiagonalTailChunk000Sub000Block098Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4115
    = surrogateDiagTailX0RatChunk000Sub000Block098Part021

theorem surrogateDiagonalTailChunk000Sub000Block098Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block098Part021CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block098Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block098Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block098Part021CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block098Part021SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block098Part021] using hcert

def TailChunk000Sub000Block098Part022SupportExplicit : Finset ℕ :=
  ([4117] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block098Part022 : ℚ :=
  (10613885625 : ℚ) / 6125285815407308

def SurrogateDiagonalTailChunk000Sub000Block098Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4117
    = surrogateDiagTailX0RatChunk000Sub000Block098Part022

theorem surrogateDiagonalTailChunk000Sub000Block098Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block098Part022CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block098Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block098Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block098Part022CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block098Part022SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block098Part022] using hcert

def TailChunk000Sub000Block098Part023SupportExplicit : Finset ℕ :=
  ([4118] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block098Part023 : ℚ :=
  (29981145979 : ℚ) / 1476084213811200

def SurrogateDiagonalTailChunk000Sub000Block098Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4118
    = surrogateDiagTailX0RatChunk000Sub000Block098Part023

theorem surrogateDiagonalTailChunk000Sub000Block098Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block098Part023CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block098Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block098Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block098Part023CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block098Part023SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block098Part023] using hcert

def TailChunk000Sub000Block098Part024SupportExplicit : Finset ℕ :=
  ([4119] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block098Part024 : ℚ :=
  (1441875 : ℚ) / 289254654976

def SurrogateDiagonalTailChunk000Sub000Block098Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4119
    = surrogateDiagTailX0RatChunk000Sub000Block098Part024

theorem surrogateDiagonalTailChunk000Sub000Block098Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block098Part024CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block098Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block098Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block098Part024CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block098Part024SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block098Part024] using hcert

def surrogateDiagonalTailChunk000Sub000Block098HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block098Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block098Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block098Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block098Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block098Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block098Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block098Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block098Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block098Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block098Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block098Head : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block098Part000
    + surrogateDiagTailX0RatChunk000Sub000Block098Part001
    + surrogateDiagTailX0RatChunk000Sub000Block098Part002
    + surrogateDiagTailX0RatChunk000Sub000Block098Part003
    + surrogateDiagTailX0RatChunk000Sub000Block098Part004
    + surrogateDiagTailX0RatChunk000Sub000Block098Part005
    + surrogateDiagTailX0RatChunk000Sub000Block098Part006
    + surrogateDiagTailX0RatChunk000Sub000Block098Part007
    + surrogateDiagTailX0RatChunk000Sub000Block098Part008
    + surrogateDiagTailX0RatChunk000Sub000Block098Part009

def surrogateDiagonalTailChunk000Sub000Block098MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block098Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block098Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block098Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block098Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block098Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block098Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block098Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block098Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block098Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block098Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block098Mid : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block098Part010
    + surrogateDiagTailX0RatChunk000Sub000Block098Part011
    + surrogateDiagTailX0RatChunk000Sub000Block098Part012
    + surrogateDiagTailX0RatChunk000Sub000Block098Part013
    + surrogateDiagTailX0RatChunk000Sub000Block098Part014
    + surrogateDiagTailX0RatChunk000Sub000Block098Part015
    + surrogateDiagTailX0RatChunk000Sub000Block098Part016
    + surrogateDiagTailX0RatChunk000Sub000Block098Part017
    + surrogateDiagTailX0RatChunk000Sub000Block098Part018
    + surrogateDiagTailX0RatChunk000Sub000Block098Part019

def surrogateDiagonalTailChunk000Sub000Block098TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block098Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block098Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block098Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block098Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block098Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block098Tail : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block098Part020
    + surrogateDiagTailX0RatChunk000Sub000Block098Part021
    + surrogateDiagTailX0RatChunk000Sub000Block098Part022
    + surrogateDiagTailX0RatChunk000Sub000Block098Part023
    + surrogateDiagTailX0RatChunk000Sub000Block098Part024

def surrogateDiagonalTailChunk000Sub000Block098Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub000Block098HeadSum X0
    + surrogateDiagonalTailChunk000Sub000Block098MidSum X0
    + surrogateDiagonalTailChunk000Sub000Block098TailSum X0

def surrogateDiagTailX0RatChunk000Sub000Block098 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block098Part000
    + surrogateDiagTailX0RatChunk000Sub000Block098Part001
    + surrogateDiagTailX0RatChunk000Sub000Block098Part002
    + surrogateDiagTailX0RatChunk000Sub000Block098Part003
    + surrogateDiagTailX0RatChunk000Sub000Block098Part004
    + surrogateDiagTailX0RatChunk000Sub000Block098Part005
    + surrogateDiagTailX0RatChunk000Sub000Block098Part006
    + surrogateDiagTailX0RatChunk000Sub000Block098Part007
    + surrogateDiagTailX0RatChunk000Sub000Block098Part008
    + surrogateDiagTailX0RatChunk000Sub000Block098Part009
    + surrogateDiagTailX0RatChunk000Sub000Block098Part010
    + surrogateDiagTailX0RatChunk000Sub000Block098Part011
    + surrogateDiagTailX0RatChunk000Sub000Block098Part012
    + surrogateDiagTailX0RatChunk000Sub000Block098Part013
    + surrogateDiagTailX0RatChunk000Sub000Block098Part014
    + surrogateDiagTailX0RatChunk000Sub000Block098Part015
    + surrogateDiagTailX0RatChunk000Sub000Block098Part016
    + surrogateDiagTailX0RatChunk000Sub000Block098Part017
    + surrogateDiagTailX0RatChunk000Sub000Block098Part018
    + surrogateDiagTailX0RatChunk000Sub000Block098Part019
    + surrogateDiagTailX0RatChunk000Sub000Block098Part020
    + surrogateDiagTailX0RatChunk000Sub000Block098Part021
    + surrogateDiagTailX0RatChunk000Sub000Block098Part022
    + surrogateDiagTailX0RatChunk000Sub000Block098Part023
    + surrogateDiagTailX0RatChunk000Sub000Block098Part024

theorem surrogateDiagTailX0RatChunk000Sub000Block098_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk000Sub000Block098Head + surrogateDiagTailX0RatChunk000Sub000Block098Mid + surrogateDiagTailX0RatChunk000Sub000Block098Tail =
      surrogateDiagTailX0RatChunk000Sub000Block098 := by
  unfold surrogateDiagTailX0RatChunk000Sub000Block098Head surrogateDiagTailX0RatChunk000Sub000Block098Mid surrogateDiagTailX0RatChunk000Sub000Block098Tail surrogateDiagTailX0RatChunk000Sub000Block098
  ring

def SurrogateDiagonalTailChunk000Sub000Block098HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block098HeadSum X0 = surrogateDiagTailX0RatChunk000Sub000Block098Head

def SurrogateDiagonalTailChunk000Sub000Block098MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block098MidSum X0 = surrogateDiagTailX0RatChunk000Sub000Block098Mid

def SurrogateDiagonalTailChunk000Sub000Block098TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block098TailSum X0 = surrogateDiagTailX0RatChunk000Sub000Block098Tail

theorem surrogateDiagonalTailChunk000Sub000Block098_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk000Sub000Block098HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk000Sub000Block098MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk000Sub000Block098TailCertificateAt X0) :
    surrogateDiagonalTailChunk000Sub000Block098Sum X0 = surrogateDiagTailX0RatChunk000Sub000Block098 := by
  unfold SurrogateDiagonalTailChunk000Sub000Block098HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk000Sub000Block098MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk000Sub000Block098TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk000Sub000Block098Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk000Sub000Block098_eq_head_add_mid_add_tail

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

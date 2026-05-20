import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0TailPilot25

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

open scoped BigOperators

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

/- Generated direct-term certificate blocks for tail chunk 000, subchunk 000, blocks [69,70). -/

/- Block 069 covers tail-support indices [1725,1750) and q from 2894 to 2930. -/

def TailChunk000Sub000Block069Part000SupportExplicit : Finset ℕ :=
  ([2894] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block069Part000 : ℚ :=
  (43603572425 : ℚ) / 1214667806944392

def SurrogateDiagonalTailChunk000Sub000Block069Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2894
    = surrogateDiagTailX0RatChunk000Sub000Block069Part000

theorem surrogateDiagonalTailChunk000Sub000Block069Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block069Part000CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block069Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block069Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block069Part000CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block069Part000SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block069Part000] using hcert

def TailChunk000Sub000Block069Part001SupportExplicit : Finset ℕ :=
  ([2895] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block069Part001 : ℚ :=
  (252425903825 : ℚ) / 6959238588923904

def SurrogateDiagonalTailChunk000Sub000Block069Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2895
    = surrogateDiagTailX0RatChunk000Sub000Block069Part001

theorem surrogateDiagonalTailChunk000Sub000Block069Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block069Part001CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block069Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block069Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block069Part001CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block069Part001SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block069Part001] using hcert

def TailChunk000Sub000Block069Part002SupportExplicit : Finset ℕ :=
  ([2897] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block069Part002 : ℚ :=
  (1048866309775 : ℚ) / 175881875885948928

def SurrogateDiagonalTailChunk000Sub000Block069Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2897
    = surrogateDiagTailX0RatChunk000Sub000Block069Part002

theorem surrogateDiagonalTailChunk000Sub000Block069Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block069Part002CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block069Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block069Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block069Part002CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block069Part002SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block069Part002] using hcert

def TailChunk000Sub000Block069Part003SupportExplicit : Finset ℕ :=
  ([2899] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block069Part003 : ℚ :=
  (5880443725 : ℚ) / 777407500329984

def SurrogateDiagonalTailChunk000Sub000Block069Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2899
    = surrogateDiagTailX0RatChunk000Sub000Block069Part003

theorem surrogateDiagonalTailChunk000Sub000Block069Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block069Part003CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block069Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block069Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block069Part003CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block069Part003SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block069Part003] using hcert

def TailChunk000Sub000Block069Part004SupportExplicit : Finset ℕ :=
  ([2901] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block069Part004 : ℚ :=
  (642285932725 : ℚ) / 34838171054402688

def SurrogateDiagonalTailChunk000Sub000Block069Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2901
    = surrogateDiagTailX0RatChunk000Sub000Block069Part004

theorem surrogateDiagonalTailChunk000Sub000Block069Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block069Part004CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block069Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block069Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block069Part004CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block069Part004SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block069Part004] using hcert

def TailChunk000Sub000Block069Part005SupportExplicit : Finset ℕ :=
  ([2902] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block069Part005 : ℚ :=
  (10520688797 : ℚ) / 221069517562500

def SurrogateDiagonalTailChunk000Sub000Block069Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2902
    = surrogateDiagTailX0RatChunk000Sub000Block069Part005

theorem surrogateDiagonalTailChunk000Sub000Block069Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block069Part005CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block069Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block069Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block069Part005CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block069Part005SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block069Part005] using hcert

def TailChunk000Sub000Block069Part006SupportExplicit : Finset ℕ :=
  ([2903] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block069Part006 : ℚ :=
  (131678265625 : ℚ) / 44335999134751602

def SurrogateDiagonalTailChunk000Sub000Block069Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2903
    = surrogateDiagTailX0RatChunk000Sub000Block069Part006

theorem surrogateDiagonalTailChunk000Sub000Block069Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block069Part006CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block069Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block069Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block069Part006CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block069Part006SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block069Part006] using hcert

def TailChunk000Sub000Block069Part007SupportExplicit : Finset ℕ :=
  ([2905] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block069Part007 : ℚ :=
  (57666517175 : ℚ) / 4688535927361536

def SurrogateDiagonalTailChunk000Sub000Block069Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2905
    = surrogateDiagTailX0RatChunk000Sub000Block069Part007

theorem surrogateDiagonalTailChunk000Sub000Block069Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block069Part007CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block069Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block069Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block069Part007CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block069Part007SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block069Part007] using hcert

def TailChunk000Sub000Block069Part008SupportExplicit : Finset ℕ :=
  ([2906] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block069Part008 : ℚ :=
  (43965927425 : ℚ) / 1234954095990912

def SurrogateDiagonalTailChunk000Sub000Block069Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2906
    = surrogateDiagTailX0RatChunk000Sub000Block069Part008

theorem surrogateDiagonalTailChunk000Sub000Block069Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block069Part008CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block069Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block069Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block069Part008CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block069Part008SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block069Part008] using hcert

def TailChunk000Sub000Block069Part009SupportExplicit : Finset ℕ :=
  ([2909] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block069Part009 : ℚ :=
  (1057573567975 : ℚ) / 178815214349931648

def SurrogateDiagonalTailChunk000Sub000Block069Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2909
    = surrogateDiagTailX0RatChunk000Sub000Block069Part009

theorem surrogateDiagonalTailChunk000Sub000Block069Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block069Part009CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block069Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block069Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block069Part009CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block069Part009SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block069Part009] using hcert

def TailChunk000Sub000Block069Part010SupportExplicit : Finset ℕ :=
  ([2910] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block069Part010 : ℚ :=
  (260567848225 : ℚ) / 869904823615488

def SurrogateDiagonalTailChunk000Sub000Block069Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2910
    = surrogateDiagTailX0RatChunk000Sub000Block069Part010

theorem surrogateDiagonalTailChunk000Sub000Block069Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block069Part010CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block069Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block069Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block069Part010CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block069Part010SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block069Part010] using hcert

def TailChunk000Sub000Block069Part011SupportExplicit : Finset ℕ :=
  ([2911] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block069Part011 : ℚ :=
  (8106554081 : ℚ) / 1229557862400000

def SurrogateDiagonalTailChunk000Sub000Block069Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2911
    = surrogateDiagTailX0RatChunk000Sub000Block069Part011

theorem surrogateDiagonalTailChunk000Sub000Block069Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block069Part011CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block069Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block069Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block069Part011CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block069Part011SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block069Part011] using hcert

def TailChunk000Sub000Block069Part012SupportExplicit : Finset ℕ :=
  ([2913] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block069Part012 : ℚ :=
  (1130079 : ℚ) / 56658739840

def SurrogateDiagonalTailChunk000Sub000Block069Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2913
    = surrogateDiagTailX0RatChunk000Sub000Block069Part012

theorem surrogateDiagonalTailChunk000Sub000Block069Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block069Part012CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block069Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block069Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block069Part012CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block069Part012SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block069Part012] using hcert

def TailChunk000Sub000Block069Part013SupportExplicit : Finset ℕ :=
  ([2914] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block069Part013 : ℚ :=
  (7599035471 : ℚ) / 181373235393600

def SurrogateDiagonalTailChunk000Sub000Block069Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2914
    = surrogateDiagTailX0RatChunk000Sub000Block069Part013

theorem surrogateDiagonalTailChunk000Sub000Block069Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block069Part013CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block069Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block069Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block069Part013CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block069Part013SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block069Part013] using hcert

def TailChunk000Sub000Block069Part014SupportExplicit : Finset ℕ :=
  ([2915] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block069Part014 : ℚ :=
  (1166588281 : ℚ) / 74885922029568

def SurrogateDiagonalTailChunk000Sub000Block069Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2915
    = surrogateDiagTailX0RatChunk000Sub000Block069Part014

theorem surrogateDiagonalTailChunk000Sub000Block069Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block069Part014CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block069Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block069Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block069Part014CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block069Part014SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block069Part014] using hcert

def TailChunk000Sub000Block069Part015SupportExplicit : Finset ℕ :=
  ([2917] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block069Part015 : ℚ :=
  (1063398402775 : ℚ) / 180791054328509568

def SurrogateDiagonalTailChunk000Sub000Block069Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2917
    = surrogateDiagTailX0RatChunk000Sub000Block069Part015

theorem surrogateDiagonalTailChunk000Sub000Block069Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block069Part015CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block069Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block069Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block069Part015CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block069Part015SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block069Part015] using hcert

def TailChunk000Sub000Block069Part016SupportExplicit : Finset ℕ :=
  ([2918] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block069Part016 : ℚ :=
  (265925473925 : ℚ) / 5649720447765924

def SurrogateDiagonalTailChunk000Sub000Block069Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2918
    = surrogateDiagTailX0RatChunk000Sub000Block069Part016

theorem surrogateDiagonalTailChunk000Sub000Block069Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block069Part016CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block069Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block069Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block069Part016CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block069Part016SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block069Part016] using hcert

def TailChunk000Sub000Block069Part017SupportExplicit : Finset ℕ :=
  ([2919] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block069Part017 : ℚ :=
  (13096025 : ℚ) / 417800374272

def SurrogateDiagonalTailChunk000Sub000Block069Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2919
    = surrogateDiagTailX0RatChunk000Sub000Block069Part017

theorem surrogateDiagonalTailChunk000Sub000Block069Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block069Part017CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block069Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block069Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block069Part017CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block069Part017SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block069Part017] using hcert

def TailChunk000Sub000Block069Part018SupportExplicit : Finset ℕ :=
  ([2921] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block069Part018 : ℚ :=
  (58315441775 : ℚ) / 16404283009521792

def SurrogateDiagonalTailChunk000Sub000Block069Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2921
    = surrogateDiagTailX0RatChunk000Sub000Block069Part018

theorem surrogateDiagonalTailChunk000Sub000Block069Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block069Part018CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block069Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block069Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block069Part018CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block069Part018SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block069Part018] using hcert

def TailChunk000Sub000Block069Part019SupportExplicit : Finset ℕ :=
  ([2922] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block069Part019 : ℚ :=
  (281159944225 : ℚ) / 2231988325043328

def SurrogateDiagonalTailChunk000Sub000Block069Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2922
    = surrogateDiagTailX0RatChunk000Sub000Block069Part019

theorem surrogateDiagonalTailChunk000Sub000Block069Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block069Part019CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block069Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block069Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block069Part019CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block069Part019SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block069Part019] using hcert

def TailChunk000Sub000Block069Part020SupportExplicit : Finset ℕ :=
  ([2923] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block069Part020 : ℚ :=
  (1560907775 : ℚ) / 459937237533696

def SurrogateDiagonalTailChunk000Sub000Block069Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2923
    = surrogateDiagTailX0RatChunk000Sub000Block069Part020

theorem surrogateDiagonalTailChunk000Sub000Block069Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block069Part020CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block069Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block069Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block069Part020CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block069Part020SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block069Part020] using hcert

def TailChunk000Sub000Block069Part021SupportExplicit : Finset ℕ :=
  ([2926] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block069Part021 : ℚ :=
  (5040639407 : ℚ) / 45358701926400

def SurrogateDiagonalTailChunk000Sub000Block069Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2926
    = surrogateDiagTailX0RatChunk000Sub000Block069Part021

theorem surrogateDiagonalTailChunk000Sub000Block069Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block069Part021CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block069Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block069Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block069Part021CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block069Part021SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block069Part021] using hcert

def TailChunk000Sub000Block069Part022SupportExplicit : Finset ℕ :=
  ([2927] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block069Part022 : ℚ :=
  (1070701941775 : ℚ) / 183283827682089288

def SurrogateDiagonalTailChunk000Sub000Block069Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2927
    = surrogateDiagTailX0RatChunk000Sub000Block069Part022

theorem surrogateDiagonalTailChunk000Sub000Block069Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block069Part022CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block069Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block069Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block069Part022CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block069Part022SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block069Part022] using hcert

def TailChunk000Sub000Block069Part023SupportExplicit : Finset ℕ :=
  ([2929] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block069Part023 : ℚ :=
  (4075296451 : ℚ) / 614778931200000

def SurrogateDiagonalTailChunk000Sub000Block069Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2929
    = surrogateDiagTailX0RatChunk000Sub000Block069Part023

theorem surrogateDiagonalTailChunk000Sub000Block069Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block069Part023CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block069Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block069Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block069Part023CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block069Part023SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block069Part023] using hcert

def TailChunk000Sub000Block069Part024SupportExplicit : Finset ℕ :=
  ([2930] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block069Part024 : ℚ :=
  (331707102775 : ℚ) / 4653698359001088

def SurrogateDiagonalTailChunk000Sub000Block069Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2930
    = surrogateDiagTailX0RatChunk000Sub000Block069Part024

theorem surrogateDiagonalTailChunk000Sub000Block069Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block069Part024CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block069Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block069Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block069Part024CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block069Part024SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block069Part024] using hcert

def surrogateDiagonalTailChunk000Sub000Block069HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block069Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block069Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block069Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block069Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block069Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block069Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block069Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block069Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block069Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block069Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block069Head : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block069Part000
    + surrogateDiagTailX0RatChunk000Sub000Block069Part001
    + surrogateDiagTailX0RatChunk000Sub000Block069Part002
    + surrogateDiagTailX0RatChunk000Sub000Block069Part003
    + surrogateDiagTailX0RatChunk000Sub000Block069Part004
    + surrogateDiagTailX0RatChunk000Sub000Block069Part005
    + surrogateDiagTailX0RatChunk000Sub000Block069Part006
    + surrogateDiagTailX0RatChunk000Sub000Block069Part007
    + surrogateDiagTailX0RatChunk000Sub000Block069Part008
    + surrogateDiagTailX0RatChunk000Sub000Block069Part009

def surrogateDiagonalTailChunk000Sub000Block069MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block069Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block069Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block069Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block069Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block069Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block069Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block069Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block069Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block069Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block069Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block069Mid : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block069Part010
    + surrogateDiagTailX0RatChunk000Sub000Block069Part011
    + surrogateDiagTailX0RatChunk000Sub000Block069Part012
    + surrogateDiagTailX0RatChunk000Sub000Block069Part013
    + surrogateDiagTailX0RatChunk000Sub000Block069Part014
    + surrogateDiagTailX0RatChunk000Sub000Block069Part015
    + surrogateDiagTailX0RatChunk000Sub000Block069Part016
    + surrogateDiagTailX0RatChunk000Sub000Block069Part017
    + surrogateDiagTailX0RatChunk000Sub000Block069Part018
    + surrogateDiagTailX0RatChunk000Sub000Block069Part019

def surrogateDiagonalTailChunk000Sub000Block069TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block069Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block069Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block069Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block069Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block069Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block069Tail : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block069Part020
    + surrogateDiagTailX0RatChunk000Sub000Block069Part021
    + surrogateDiagTailX0RatChunk000Sub000Block069Part022
    + surrogateDiagTailX0RatChunk000Sub000Block069Part023
    + surrogateDiagTailX0RatChunk000Sub000Block069Part024

def surrogateDiagonalTailChunk000Sub000Block069Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub000Block069HeadSum X0
    + surrogateDiagonalTailChunk000Sub000Block069MidSum X0
    + surrogateDiagonalTailChunk000Sub000Block069TailSum X0

def surrogateDiagTailX0RatChunk000Sub000Block069 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block069Part000
    + surrogateDiagTailX0RatChunk000Sub000Block069Part001
    + surrogateDiagTailX0RatChunk000Sub000Block069Part002
    + surrogateDiagTailX0RatChunk000Sub000Block069Part003
    + surrogateDiagTailX0RatChunk000Sub000Block069Part004
    + surrogateDiagTailX0RatChunk000Sub000Block069Part005
    + surrogateDiagTailX0RatChunk000Sub000Block069Part006
    + surrogateDiagTailX0RatChunk000Sub000Block069Part007
    + surrogateDiagTailX0RatChunk000Sub000Block069Part008
    + surrogateDiagTailX0RatChunk000Sub000Block069Part009
    + surrogateDiagTailX0RatChunk000Sub000Block069Part010
    + surrogateDiagTailX0RatChunk000Sub000Block069Part011
    + surrogateDiagTailX0RatChunk000Sub000Block069Part012
    + surrogateDiagTailX0RatChunk000Sub000Block069Part013
    + surrogateDiagTailX0RatChunk000Sub000Block069Part014
    + surrogateDiagTailX0RatChunk000Sub000Block069Part015
    + surrogateDiagTailX0RatChunk000Sub000Block069Part016
    + surrogateDiagTailX0RatChunk000Sub000Block069Part017
    + surrogateDiagTailX0RatChunk000Sub000Block069Part018
    + surrogateDiagTailX0RatChunk000Sub000Block069Part019
    + surrogateDiagTailX0RatChunk000Sub000Block069Part020
    + surrogateDiagTailX0RatChunk000Sub000Block069Part021
    + surrogateDiagTailX0RatChunk000Sub000Block069Part022
    + surrogateDiagTailX0RatChunk000Sub000Block069Part023
    + surrogateDiagTailX0RatChunk000Sub000Block069Part024

theorem surrogateDiagTailX0RatChunk000Sub000Block069_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk000Sub000Block069Head + surrogateDiagTailX0RatChunk000Sub000Block069Mid + surrogateDiagTailX0RatChunk000Sub000Block069Tail =
      surrogateDiagTailX0RatChunk000Sub000Block069 := by
  unfold surrogateDiagTailX0RatChunk000Sub000Block069Head surrogateDiagTailX0RatChunk000Sub000Block069Mid surrogateDiagTailX0RatChunk000Sub000Block069Tail surrogateDiagTailX0RatChunk000Sub000Block069
  ring

def SurrogateDiagonalTailChunk000Sub000Block069HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block069HeadSum X0 = surrogateDiagTailX0RatChunk000Sub000Block069Head

def SurrogateDiagonalTailChunk000Sub000Block069MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block069MidSum X0 = surrogateDiagTailX0RatChunk000Sub000Block069Mid

def SurrogateDiagonalTailChunk000Sub000Block069TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block069TailSum X0 = surrogateDiagTailX0RatChunk000Sub000Block069Tail

theorem surrogateDiagonalTailChunk000Sub000Block069_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk000Sub000Block069HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk000Sub000Block069MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk000Sub000Block069TailCertificateAt X0) :
    surrogateDiagonalTailChunk000Sub000Block069Sum X0 = surrogateDiagTailX0RatChunk000Sub000Block069 := by
  unfold SurrogateDiagonalTailChunk000Sub000Block069HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk000Sub000Block069MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk000Sub000Block069TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk000Sub000Block069Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk000Sub000Block069_eq_head_add_mid_add_tail

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

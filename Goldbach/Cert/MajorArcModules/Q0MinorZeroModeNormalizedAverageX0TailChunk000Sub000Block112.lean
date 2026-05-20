import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0TailPilot25

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

open scoped BigOperators

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

/- Generated direct-term certificate blocks for tail chunk 000, subchunk 000, blocks [112,113). -/

/- Block 112 covers tail-support indices [2800,2825) and q from 4657 to 4695. -/

def TailChunk000Sub000Block112Part000SupportExplicit : Finset ℕ :=
  ([4657] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block112Part000 : ℚ :=
  (338869515625 : ℚ) / 293777651112026112

def SurrogateDiagonalTailChunk000Sub000Block112Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4657
    = surrogateDiagTailX0RatChunk000Sub000Block112Part000

theorem surrogateDiagonalTailChunk000Sub000Block112Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block112Part000CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block112Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block112Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block112Part000CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block112Part000SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block112Part000] using hcert

def TailChunk000Sub000Block112Part001SupportExplicit : Finset ℕ :=
  ([4658] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block112Part001 : ℚ :=
  (390576825 : ℚ) / 34351228125184

def SurrogateDiagonalTailChunk000Sub000Block112Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4658
    = surrogateDiagTailX0RatChunk000Sub000Block112Part001

theorem surrogateDiagonalTailChunk000Sub000Block112Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block112Part001CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block112Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block112Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block112Part001CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block112Part001SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block112Part001] using hcert

def TailChunk000Sub000Block112Part002SupportExplicit : Finset ℕ :=
  ([4659] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block112Part002 : ℚ :=
  (1054613426425 : ℚ) / 232120613224316928

def SurrogateDiagonalTailChunk000Sub000Block112Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4659
    = surrogateDiagTailX0RatChunk000Sub000Block112Part002

theorem surrogateDiagonalTailChunk000Sub000Block112Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block112Part002CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block112Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block112Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block112Part002CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block112Part002SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block112Part002] using hcert

def TailChunk000Sub000Block112Part003SupportExplicit : Finset ℕ :=
  ([4661] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block112Part003 : ℚ :=
  (1687054475 : ℚ) / 1337690004183936

def SurrogateDiagonalTailChunk000Sub000Block112Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4661
    = surrogateDiagTailX0RatChunk000Sub000Block112Part003

theorem surrogateDiagonalTailChunk000Sub000Block112Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block112Part003CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block112Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block112Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block112Part003CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block112Part003SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block112Part003] using hcert

def TailChunk000Sub000Block112Part004SupportExplicit : Finset ℕ :=
  ([4663] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block112Part004 : ℚ :=
  (339743265625 : ℚ) / 295294898577491442

def SurrogateDiagonalTailChunk000Sub000Block112Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4663
    = surrogateDiagTailX0RatChunk000Sub000Block112Part004

theorem surrogateDiagonalTailChunk000Sub000Block112Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block112Part004CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block112Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block112Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block112Part004CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block112Part004SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block112Part004] using hcert

def TailChunk000Sub000Block112Part005SupportExplicit : Finset ℕ :=
  ([4665] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block112Part005 : ℚ :=
  (9965495289 : ℚ) / 1261166188134400

def SurrogateDiagonalTailChunk000Sub000Block112Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4665
    = surrogateDiagTailX0RatChunk000Sub000Block112Part005

theorem surrogateDiagonalTailChunk000Sub000Block112Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block112Part005CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block112Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block112Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block112Part005CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block112Part005SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block112Part005] using hcert

def TailChunk000Sub000Block112Part006SupportExplicit : Finset ℕ :=
  ([4666] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block112Part006 : ℚ :=
  (680225052775 : ℚ) / 73950487825577088

def SurrogateDiagonalTailChunk000Sub000Block112Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4666
    = surrogateDiagTailX0RatChunk000Sub000Block112Part006

theorem surrogateDiagonalTailChunk000Sub000Block112Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block112Part006CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block112Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block112Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block112Part006CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block112Part006SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block112Part006] using hcert

def TailChunk000Sub000Block112Part007SupportExplicit : Finset ℕ :=
  ([4667] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block112Part007 : ℚ :=
  (420534520325 : ℚ) / 283898236576536576

def SurrogateDiagonalTailChunk000Sub000Block112Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4667
    = surrogateDiagTailX0RatChunk000Sub000Block112Part007

theorem surrogateDiagonalTailChunk000Sub000Block112Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block112Part007CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block112Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block112Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block112Part007CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block112Part007SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block112Part007] using hcert

def TailChunk000Sub000Block112Part008SupportExplicit : Finset ℕ :=
  ([4669] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block112Part008 : ℚ :=
  (69206489425 : ℚ) / 29163169794705408

def SurrogateDiagonalTailChunk000Sub000Block112Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4669
    = surrogateDiagTailX0RatChunk000Sub000Block112Part008

theorem surrogateDiagonalTailChunk000Sub000Block112Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block112Part008CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block112Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block112Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block112Part008CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block112Part008SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block112Part008] using hcert

def TailChunk000Sub000Block112Part009SupportExplicit : Finset ℕ :=
  ([4670] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block112Part009 : ℚ :=
  (185939818875 : ℚ) / 10062114065422336

def SurrogateDiagonalTailChunk000Sub000Block112Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4670
    = surrogateDiagTailX0RatChunk000Sub000Block112Part009

theorem surrogateDiagonalTailChunk000Sub000Block112Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block112Part009CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block112Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block112Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block112Part009CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block112Part009SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block112Part009] using hcert

def TailChunk000Sub000Block112Part010SupportExplicit : Finset ℕ :=
  ([4673] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block112Part010 : ℚ :=
  (2729070201775 : ℚ) / 1191346779904278528

def SurrogateDiagonalTailChunk000Sub000Block112Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4673
    = surrogateDiagTailX0RatChunk000Sub000Block112Part010

theorem surrogateDiagonalTailChunk000Sub000Block112Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block112Part010CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block112Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block112Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block112Part010CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block112Part010SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block112Part010] using hcert

def TailChunk000Sub000Block112Part011SupportExplicit : Finset ℕ :=
  ([4674] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block112Part011 : ℚ :=
  (11040067043 : ℚ) / 215033846169600

def SurrogateDiagonalTailChunk000Sub000Block112Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4674
    = surrogateDiagTailX0RatChunk000Sub000Block112Part011

theorem surrogateDiagonalTailChunk000Sub000Block112Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block112Part011CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block112Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block112Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block112Part011CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block112Part011SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block112Part011] using hcert

def TailChunk000Sub000Block112Part012SupportExplicit : Finset ℕ :=
  ([4677] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block112Part012 : ℚ :=
  (91088625 : ℚ) / 23568383953984

def SurrogateDiagonalTailChunk000Sub000Block112Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4677
    = surrogateDiagTailX0RatChunk000Sub000Block112Part012

theorem surrogateDiagonalTailChunk000Sub000Block112Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block112Part012CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block112Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block112Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block112Part012CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block112Part012SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block112Part012] using hcert

def TailChunk000Sub000Block112Part013SupportExplicit : Finset ℕ :=
  ([4678] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block112Part013 : ℚ :=
  (683728351975 : ℚ) / 74714498580573768

def SurrogateDiagonalTailChunk000Sub000Block112Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4678
    = surrogateDiagTailX0RatChunk000Sub000Block112Part013

theorem surrogateDiagonalTailChunk000Sub000Block112Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block112Part013CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block112Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block112Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block112Part013CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block112Part013SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block112Part013] using hcert

def TailChunk000Sub000Block112Part014SupportExplicit : Finset ℕ :=
  ([4679] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block112Part014 : ℚ :=
  (342078765625 : ℚ) / 299369627835586482

def SurrogateDiagonalTailChunk000Sub000Block112Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4679
    = surrogateDiagTailX0RatChunk000Sub000Block112Part014

theorem surrogateDiagonalTailChunk000Sub000Block112Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block112Part014CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block112Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block112Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block112Part014CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block112Part014SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block112Part014] using hcert

def TailChunk000Sub000Block112Part015SupportExplicit : Finset ℕ :=
  ([4681] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block112Part015 : ℚ :=
  (13201884193 : ℚ) / 10253612812500000

def SurrogateDiagonalTailChunk000Sub000Block112Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4681
    = surrogateDiagTailX0RatChunk000Sub000Block112Part015

theorem surrogateDiagonalTailChunk000Sub000Block112Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block112Part015CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block112Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block112Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block112Part015CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block112Part015SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block112Part015] using hcert

def TailChunk000Sub000Block112Part016SupportExplicit : Finset ℕ :=
  ([4682] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block112Part016 : ℚ :=
  (27395924719 : ℚ) / 2998819179907200

def SurrogateDiagonalTailChunk000Sub000Block112Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4682
    = surrogateDiagTailX0RatChunk000Sub000Block112Part016

theorem surrogateDiagonalTailChunk000Sub000Block112Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block112Part016CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block112Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block112Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block112Part016CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block112Part016SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block112Part016] using hcert

def TailChunk000Sub000Block112Part017SupportExplicit : Finset ℕ :=
  ([4683] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block112Part017 : ℚ :=
  (391596149075 : ℚ) / 62970007526728704

def SurrogateDiagonalTailChunk000Sub000Block112Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4683
    = surrogateDiagTailX0RatChunk000Sub000Block112Part017

theorem surrogateDiagonalTailChunk000Sub000Block112Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block112Part017CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block112Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block112Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block112Part017CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block112Part017SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block112Part017] using hcert

def TailChunk000Sub000Block112Part018SupportExplicit : Finset ℕ :=
  ([4685] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block112Part018 : ℚ :=
  (548294511875 : ℚ) / 245663267217997824

def SurrogateDiagonalTailChunk000Sub000Block112Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4685
    = surrogateDiagTailX0RatChunk000Sub000Block112Part018

theorem surrogateDiagonalTailChunk000Sub000Block112Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block112Part018CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block112Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block112Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block112Part018CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block112Part018SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block112Part018] using hcert

def TailChunk000Sub000Block112Part019SupportExplicit : Finset ℕ :=
  ([4686] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block112Part019 : ℚ :=
  (393004971 : ℚ) / 9148496000000

def SurrogateDiagonalTailChunk000Sub000Block112Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4686
    = surrogateDiagTailX0RatChunk000Sub000Block112Part019

theorem surrogateDiagonalTailChunk000Sub000Block112Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block112Part019CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block112Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block112Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block112Part019CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block112Part019SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block112Part019] using hcert

def TailChunk000Sub000Block112Part020SupportExplicit : Finset ℕ :=
  ([4687] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block112Part020 : ℚ :=
  (49337674625 : ℚ) / 39206247597103104

def SurrogateDiagonalTailChunk000Sub000Block112Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4687
    = surrogateDiagTailX0RatChunk000Sub000Block112Part020

theorem surrogateDiagonalTailChunk000Sub000Block112Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block112Part020CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block112Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block112Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block112Part020CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block112Part020SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block112Part020] using hcert

def TailChunk000Sub000Block112Part021SupportExplicit : Finset ℕ :=
  ([4690] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block112Part021 : ℚ :=
  (78386309525 : ℚ) / 2623592118140928

def SurrogateDiagonalTailChunk000Sub000Block112Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4690
    = surrogateDiagTailX0RatChunk000Sub000Block112Part021

theorem surrogateDiagonalTailChunk000Sub000Block112Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block112Part021CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block112Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block112Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block112Part021CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block112Part021SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block112Part021] using hcert

def TailChunk000Sub000Block112Part022SupportExplicit : Finset ℕ :=
  ([4691] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block112Part022 : ℚ :=
  (550137025 : ℚ) / 483925180893042

def SurrogateDiagonalTailChunk000Sub000Block112Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4691
    = surrogateDiagTailX0RatChunk000Sub000Block112Part022

theorem surrogateDiagonalTailChunk000Sub000Block112Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block112Part022CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block112Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block112Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block112Part022CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block112Part022SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block112Part022] using hcert

def TailChunk000Sub000Block112Part023SupportExplicit : Finset ℕ :=
  ([4694] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block112Part023 : ℚ :=
  (688413414775 : ℚ) / 75742369966544328

def SurrogateDiagonalTailChunk000Sub000Block112Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4694
    = surrogateDiagTailX0RatChunk000Sub000Block112Part023

theorem surrogateDiagonalTailChunk000Sub000Block112Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block112Part023CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block112Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block112Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block112Part023CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block112Part023SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block112Part023] using hcert

def TailChunk000Sub000Block112Part024SupportExplicit : Finset ℕ :=
  ([4695] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block112Part024 : ℚ :=
  (184700747425 : ℚ) / 24263038737580032

def SurrogateDiagonalTailChunk000Sub000Block112Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4695
    = surrogateDiagTailX0RatChunk000Sub000Block112Part024

theorem surrogateDiagonalTailChunk000Sub000Block112Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block112Part024CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block112Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block112Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block112Part024CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block112Part024SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block112Part024] using hcert

def surrogateDiagonalTailChunk000Sub000Block112HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block112Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block112Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block112Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block112Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block112Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block112Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block112Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block112Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block112Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block112Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block112Head : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block112Part000
    + surrogateDiagTailX0RatChunk000Sub000Block112Part001
    + surrogateDiagTailX0RatChunk000Sub000Block112Part002
    + surrogateDiagTailX0RatChunk000Sub000Block112Part003
    + surrogateDiagTailX0RatChunk000Sub000Block112Part004
    + surrogateDiagTailX0RatChunk000Sub000Block112Part005
    + surrogateDiagTailX0RatChunk000Sub000Block112Part006
    + surrogateDiagTailX0RatChunk000Sub000Block112Part007
    + surrogateDiagTailX0RatChunk000Sub000Block112Part008
    + surrogateDiagTailX0RatChunk000Sub000Block112Part009

def surrogateDiagonalTailChunk000Sub000Block112MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block112Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block112Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block112Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block112Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block112Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block112Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block112Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block112Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block112Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block112Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block112Mid : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block112Part010
    + surrogateDiagTailX0RatChunk000Sub000Block112Part011
    + surrogateDiagTailX0RatChunk000Sub000Block112Part012
    + surrogateDiagTailX0RatChunk000Sub000Block112Part013
    + surrogateDiagTailX0RatChunk000Sub000Block112Part014
    + surrogateDiagTailX0RatChunk000Sub000Block112Part015
    + surrogateDiagTailX0RatChunk000Sub000Block112Part016
    + surrogateDiagTailX0RatChunk000Sub000Block112Part017
    + surrogateDiagTailX0RatChunk000Sub000Block112Part018
    + surrogateDiagTailX0RatChunk000Sub000Block112Part019

def surrogateDiagonalTailChunk000Sub000Block112TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block112Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block112Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block112Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block112Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block112Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block112Tail : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block112Part020
    + surrogateDiagTailX0RatChunk000Sub000Block112Part021
    + surrogateDiagTailX0RatChunk000Sub000Block112Part022
    + surrogateDiagTailX0RatChunk000Sub000Block112Part023
    + surrogateDiagTailX0RatChunk000Sub000Block112Part024

def surrogateDiagonalTailChunk000Sub000Block112Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub000Block112HeadSum X0
    + surrogateDiagonalTailChunk000Sub000Block112MidSum X0
    + surrogateDiagonalTailChunk000Sub000Block112TailSum X0

def surrogateDiagTailX0RatChunk000Sub000Block112 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block112Part000
    + surrogateDiagTailX0RatChunk000Sub000Block112Part001
    + surrogateDiagTailX0RatChunk000Sub000Block112Part002
    + surrogateDiagTailX0RatChunk000Sub000Block112Part003
    + surrogateDiagTailX0RatChunk000Sub000Block112Part004
    + surrogateDiagTailX0RatChunk000Sub000Block112Part005
    + surrogateDiagTailX0RatChunk000Sub000Block112Part006
    + surrogateDiagTailX0RatChunk000Sub000Block112Part007
    + surrogateDiagTailX0RatChunk000Sub000Block112Part008
    + surrogateDiagTailX0RatChunk000Sub000Block112Part009
    + surrogateDiagTailX0RatChunk000Sub000Block112Part010
    + surrogateDiagTailX0RatChunk000Sub000Block112Part011
    + surrogateDiagTailX0RatChunk000Sub000Block112Part012
    + surrogateDiagTailX0RatChunk000Sub000Block112Part013
    + surrogateDiagTailX0RatChunk000Sub000Block112Part014
    + surrogateDiagTailX0RatChunk000Sub000Block112Part015
    + surrogateDiagTailX0RatChunk000Sub000Block112Part016
    + surrogateDiagTailX0RatChunk000Sub000Block112Part017
    + surrogateDiagTailX0RatChunk000Sub000Block112Part018
    + surrogateDiagTailX0RatChunk000Sub000Block112Part019
    + surrogateDiagTailX0RatChunk000Sub000Block112Part020
    + surrogateDiagTailX0RatChunk000Sub000Block112Part021
    + surrogateDiagTailX0RatChunk000Sub000Block112Part022
    + surrogateDiagTailX0RatChunk000Sub000Block112Part023
    + surrogateDiagTailX0RatChunk000Sub000Block112Part024

theorem surrogateDiagTailX0RatChunk000Sub000Block112_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk000Sub000Block112Head + surrogateDiagTailX0RatChunk000Sub000Block112Mid + surrogateDiagTailX0RatChunk000Sub000Block112Tail =
      surrogateDiagTailX0RatChunk000Sub000Block112 := by
  unfold surrogateDiagTailX0RatChunk000Sub000Block112Head surrogateDiagTailX0RatChunk000Sub000Block112Mid surrogateDiagTailX0RatChunk000Sub000Block112Tail surrogateDiagTailX0RatChunk000Sub000Block112
  ring

def SurrogateDiagonalTailChunk000Sub000Block112HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block112HeadSum X0 = surrogateDiagTailX0RatChunk000Sub000Block112Head

def SurrogateDiagonalTailChunk000Sub000Block112MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block112MidSum X0 = surrogateDiagTailX0RatChunk000Sub000Block112Mid

def SurrogateDiagonalTailChunk000Sub000Block112TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block112TailSum X0 = surrogateDiagTailX0RatChunk000Sub000Block112Tail

theorem surrogateDiagonalTailChunk000Sub000Block112_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk000Sub000Block112HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk000Sub000Block112MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk000Sub000Block112TailCertificateAt X0) :
    surrogateDiagonalTailChunk000Sub000Block112Sum X0 = surrogateDiagTailX0RatChunk000Sub000Block112 := by
  unfold SurrogateDiagonalTailChunk000Sub000Block112HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk000Sub000Block112MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk000Sub000Block112TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk000Sub000Block112Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk000Sub000Block112_eq_head_add_mid_add_tail

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

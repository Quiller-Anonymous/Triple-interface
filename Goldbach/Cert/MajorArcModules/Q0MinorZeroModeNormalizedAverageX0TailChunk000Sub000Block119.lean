import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0TailPilot25

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

open scoped BigOperators

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

/- Generated direct-term certificate blocks for tail chunk 000, subchunk 000, blocks [119,120). -/

/- Block 119 covers tail-support indices [2975,3000) and q from 4939 to 4981. -/

def TailChunk000Sub000Block119Part000SupportExplicit : Finset ℕ :=
  ([4939] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block119Part000 : ℚ :=
  (172904699 : ℚ) / 125906725109760

def SurrogateDiagonalTailChunk000Sub000Block119Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4939
    = surrogateDiagTailX0RatChunk000Sub000Block119Part000

theorem surrogateDiagonalTailChunk000Sub000Block119Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block119Part000CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block119Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block119Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block119Part000CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block119Part000SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block119Part000] using hcert

def TailChunk000Sub000Block119Part001SupportExplicit : Finset ℕ :=
  ([4942] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block119Part001 : ℚ :=
  (72499517825 : ℚ) / 5527897796247552

def SurrogateDiagonalTailChunk000Sub000Block119Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4942
    = surrogateDiagTailX0RatChunk000Sub000Block119Part001

theorem surrogateDiagonalTailChunk000Sub000Block119Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block119Part001CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block119Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block119Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block119Part001CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block119Part001SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block119Part001] using hcert

def TailChunk000Sub000Block119Part002SupportExplicit : Finset ℕ :=
  ([4943] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block119Part002 : ℚ :=
  (381769515625 : ℚ) / 372887505761444562

def SurrogateDiagonalTailChunk000Sub000Block119Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4943
    = surrogateDiagTailX0RatChunk000Sub000Block119Part002

theorem surrogateDiagonalTailChunk000Sub000Block119Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block119Part002CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block119Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block119Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block119Part002CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block119Part002SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block119Part002] using hcert

def TailChunk000Sub000Block119Part003SupportExplicit : Finset ℕ :=
  ([4945] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block119Part003 : ℚ :=
  (63515106425 : ℚ) / 25922817595293696

def SurrogateDiagonalTailChunk000Sub000Block119Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4945
    = surrogateDiagTailX0RatChunk000Sub000Block119Part003

theorem surrogateDiagonalTailChunk000Sub000Block119Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block119Part003CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block119Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block119Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block119Part003CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block119Part003SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block119Part003] using hcert

def TailChunk000Sub000Block119Part004SupportExplicit : Finset ℕ :=
  ([4946] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block119Part004 : ℚ :=
  (764313231775 : ℚ) / 93372873577187328

def SurrogateDiagonalTailChunk000Sub000Block119Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4946
    = surrogateDiagTailX0RatChunk000Sub000Block119Part004

theorem surrogateDiagonalTailChunk000Sub000Block119Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block119Part004CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block119Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block119Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block119Part004CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block119Part004SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block119Part004] using hcert

def TailChunk000Sub000Block119Part005SupportExplicit : Finset ℕ :=
  ([4947] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block119Part005 : ℚ :=
  (475346147675 : ℚ) / 111347817422782464

def SurrogateDiagonalTailChunk000Sub000Block119Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4947
    = surrogateDiagTailX0RatChunk000Sub000Block119Part005

theorem surrogateDiagonalTailChunk000Sub000Block119Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block119Part005CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block119Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block119Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block119Part005CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block119Part005SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block119Part005] using hcert

def TailChunk000Sub000Block119Part006SupportExplicit : Finset ℕ :=
  ([4951] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block119Part006 : ℚ :=
  (24512401 : ℚ) / 24019703230050

def SurrogateDiagonalTailChunk000Sub000Block119Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4951
    = surrogateDiagTailX0RatChunk000Sub000Block119Part006

theorem surrogateDiagonalTailChunk000Sub000Block119Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block119Part006CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block119Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block119Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block119Part006CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block119Part006SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block119Part006] using hcert

def TailChunk000Sub000Block119Part007SupportExplicit : Finset ℕ :=
  ([4953] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block119Part007 : ℚ :=
  (33441885625 : ℚ) / 7467856685162496

def SurrogateDiagonalTailChunk000Sub000Block119Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4953
    = surrogateDiagTailX0RatChunk000Sub000Block119Part007

theorem surrogateDiagonalTailChunk000Sub000Block119Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block119Part007CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block119Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block119Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block119Part007CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block119Part007SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block119Part007] using hcert

def TailChunk000Sub000Block119Part008SupportExplicit : Finset ℕ :=
  ([4954] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block119Part008 : ℚ :=
  (766787736775 : ℚ) / 93978697210485888

def SurrogateDiagonalTailChunk000Sub000Block119Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4954
    = surrogateDiagTailX0RatChunk000Sub000Block119Part008

theorem surrogateDiagonalTailChunk000Sub000Block119Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block119Part008CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block119Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block119Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block119Part008CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block119Part008SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block119Part008] using hcert

def TailChunk000Sub000Block119Part009SupportExplicit : Finset ℕ :=
  ([4955] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block119Part009 : ℚ :=
  (4906480099 : ℚ) / 2459617610757120

def SurrogateDiagonalTailChunk000Sub000Block119Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4955
    = surrogateDiagTailX0RatChunk000Sub000Block119Part009

theorem surrogateDiagonalTailChunk000Sub000Block119Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block119Part009CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block119Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block119Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block119Part009CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block119Part009SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block119Part009] using hcert

def TailChunk000Sub000Block119Part010SupportExplicit : Finset ℕ :=
  ([4957] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block119Part010 : ℚ :=
  (383935140625 : ℚ) / 377130848630068512

def SurrogateDiagonalTailChunk000Sub000Block119Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4957
    = surrogateDiagTailX0RatChunk000Sub000Block119Part010

theorem surrogateDiagonalTailChunk000Sub000Block119Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block119Part010CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block119Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block119Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block119Part010CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block119Part010SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block119Part010] using hcert

def TailChunk000Sub000Block119Part011SupportExplicit : Finset ℕ :=
  ([4958] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block119Part011 : ℚ :=
  (368383044875 : ℚ) / 39845805294265344

def SurrogateDiagonalTailChunk000Sub000Block119Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4958
    = surrogateDiagTailX0RatChunk000Sub000Block119Part011

theorem surrogateDiagonalTailChunk000Sub000Block119Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block119Part011CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block119Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block119Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block119Part011CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block119Part011SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block119Part011] using hcert

def TailChunk000Sub000Block119Part012SupportExplicit : Finset ℕ :=
  ([4962] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block119Part012 : ℚ :=
  (102466275 : ℚ) / 3724004321408

def SurrogateDiagonalTailChunk000Sub000Block119Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4962
    = surrogateDiagTailX0RatChunk000Sub000Block119Part012

theorem surrogateDiagonalTailChunk000Sub000Block119Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block119Part012CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block119Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block119Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block119Part012CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block119Part012SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block119Part012] using hcert

def TailChunk000Sub000Block119Part013SupportExplicit : Finset ℕ :=
  ([4963] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block119Part013 : ℚ :=
  (24406543525 : ℚ) / 15078951048932352

def SurrogateDiagonalTailChunk000Sub000Block119Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4963
    = surrogateDiagTailX0RatChunk000Sub000Block119Part013

theorem surrogateDiagonalTailChunk000Sub000Block119Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block119Part013CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block119Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block119Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block119Part013CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block119Part013SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block119Part013] using hcert

def TailChunk000Sub000Block119Part014SupportExplicit : Finset ℕ :=
  ([4965] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block119Part014 : ℚ :=
  (32776258891 : ℚ) / 4858503922483200

def SurrogateDiagonalTailChunk000Sub000Block119Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4965
    = surrogateDiagTailX0RatChunk000Sub000Block119Part014

theorem surrogateDiagonalTailChunk000Sub000Block119Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block119Part014CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block119Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block119Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block119Part014CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block119Part014SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block119Part014] using hcert

def TailChunk000Sub000Block119Part015SupportExplicit : Finset ℕ :=
  ([4966] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block119Part015 : ℚ :=
  (3539127683 : ℚ) / 337859590406400

def SurrogateDiagonalTailChunk000Sub000Block119Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4966
    = surrogateDiagTailX0RatChunk000Sub000Block119Part015

theorem surrogateDiagonalTailChunk000Sub000Block119Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block119Part015CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block119Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block119Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block119Part015CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block119Part015SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block119Part015] using hcert

def TailChunk000Sub000Block119Part016SupportExplicit : Finset ℕ :=
  ([4967] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block119Part016 : ℚ :=
  (385485765625 : ℚ) / 380183906112117042

def SurrogateDiagonalTailChunk000Sub000Block119Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4967
    = surrogateDiagTailX0RatChunk000Sub000Block119Part016

theorem surrogateDiagonalTailChunk000Sub000Block119Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block119Part016CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block119Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block119Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block119Part016CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block119Part016SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block119Part016] using hcert

def TailChunk000Sub000Block119Part017SupportExplicit : Finset ℕ :=
  ([4969] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block119Part017 : ℚ :=
  (385796265625 : ℚ) / 380796735173571072

def SurrogateDiagonalTailChunk000Sub000Block119Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4969
    = surrogateDiagTailX0RatChunk000Sub000Block119Part017

theorem surrogateDiagonalTailChunk000Sub000Block119Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block119Part017CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block119Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block119Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block119Part017CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block119Part017SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block119Part017] using hcert

def TailChunk000Sub000Block119Part018SupportExplicit : Finset ℕ :=
  ([4970] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block119Part018 : ℚ :=
  (10357231 : ℚ) / 395215027200

def SurrogateDiagonalTailChunk000Sub000Block119Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4970
    = surrogateDiagTailX0RatChunk000Sub000Block119Part018

theorem surrogateDiagonalTailChunk000Sub000Block119Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block119Part018CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block119Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block119Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block119Part018CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block119Part018SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block119Part018] using hcert

def TailChunk000Sub000Block119Part019SupportExplicit : Finset ℕ :=
  ([4971] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block119Part019 : ℚ :=
  (34300025 : ℚ) / 10027208982528

def SurrogateDiagonalTailChunk000Sub000Block119Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4971
    = surrogateDiagTailX0RatChunk000Sub000Block119Part019

theorem surrogateDiagonalTailChunk000Sub000Block119Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block119Part019CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block119Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block119Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block119Part019CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block119Part019SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block119Part019] using hcert

def TailChunk000Sub000Block119Part020SupportExplicit : Finset ℕ :=
  ([4973] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block119Part020 : ℚ :=
  (386417640625 : ℚ) / 382024615629356832

def SurrogateDiagonalTailChunk000Sub000Block119Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4973
    = surrogateDiagTailX0RatChunk000Sub000Block119Part020

theorem surrogateDiagonalTailChunk000Sub000Block119Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block119Part020CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block119Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block119Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block119Part020CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block119Part020SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block119Part020] using hcert

def TailChunk000Sub000Block119Part021SupportExplicit : Finset ℕ :=
  ([4974] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block119Part021 : ℚ :=
  (3813425 : ℚ) / 139266791424

def SurrogateDiagonalTailChunk000Sub000Block119Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4974
    = surrogateDiagTailX0RatChunk000Sub000Block119Part021

theorem surrogateDiagonalTailChunk000Sub000Block119Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block119Part021CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block119Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block119Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block119Part021CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block119Part021SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block119Part021] using hcert

def TailChunk000Sub000Block119Part022SupportExplicit : Finset ℕ :=
  ([4978] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block119Part022 : ℚ :=
  (1165119577 : ℚ) / 119952767196288

def SurrogateDiagonalTailChunk000Sub000Block119Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4978
    = surrogateDiagTailX0RatChunk000Sub000Block119Part022

theorem surrogateDiagonalTailChunk000Sub000Block119Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block119Part022CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block119Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block119Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block119Part022CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block119Part022SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block119Part022] using hcert

def TailChunk000Sub000Block119Part023SupportExplicit : Finset ℕ :=
  ([4979] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block119Part023 : ℚ :=
  (713394025175 : ℚ) / 552046040204534784

def SurrogateDiagonalTailChunk000Sub000Block119Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4979
    = surrogateDiagTailX0RatChunk000Sub000Block119Part023

theorem surrogateDiagonalTailChunk000Sub000Block119Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block119Part023CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block119Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block119Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block119Part023CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block119Part023SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block119Part023] using hcert

def TailChunk000Sub000Block119Part024SupportExplicit : Finset ℕ :=
  ([4981] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block119Part024 : ℚ :=
  (484920027075 : ℚ) / 397115593301426176

def SurrogateDiagonalTailChunk000Sub000Block119Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4981
    = surrogateDiagTailX0RatChunk000Sub000Block119Part024

theorem surrogateDiagonalTailChunk000Sub000Block119Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block119Part024CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block119Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block119Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block119Part024CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block119Part024SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block119Part024] using hcert

def surrogateDiagonalTailChunk000Sub000Block119HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block119Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block119Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block119Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block119Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block119Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block119Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block119Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block119Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block119Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block119Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block119Head : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block119Part000
    + surrogateDiagTailX0RatChunk000Sub000Block119Part001
    + surrogateDiagTailX0RatChunk000Sub000Block119Part002
    + surrogateDiagTailX0RatChunk000Sub000Block119Part003
    + surrogateDiagTailX0RatChunk000Sub000Block119Part004
    + surrogateDiagTailX0RatChunk000Sub000Block119Part005
    + surrogateDiagTailX0RatChunk000Sub000Block119Part006
    + surrogateDiagTailX0RatChunk000Sub000Block119Part007
    + surrogateDiagTailX0RatChunk000Sub000Block119Part008
    + surrogateDiagTailX0RatChunk000Sub000Block119Part009

def surrogateDiagonalTailChunk000Sub000Block119MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block119Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block119Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block119Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block119Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block119Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block119Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block119Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block119Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block119Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block119Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block119Mid : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block119Part010
    + surrogateDiagTailX0RatChunk000Sub000Block119Part011
    + surrogateDiagTailX0RatChunk000Sub000Block119Part012
    + surrogateDiagTailX0RatChunk000Sub000Block119Part013
    + surrogateDiagTailX0RatChunk000Sub000Block119Part014
    + surrogateDiagTailX0RatChunk000Sub000Block119Part015
    + surrogateDiagTailX0RatChunk000Sub000Block119Part016
    + surrogateDiagTailX0RatChunk000Sub000Block119Part017
    + surrogateDiagTailX0RatChunk000Sub000Block119Part018
    + surrogateDiagTailX0RatChunk000Sub000Block119Part019

def surrogateDiagonalTailChunk000Sub000Block119TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block119Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block119Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block119Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block119Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block119Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block119Tail : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block119Part020
    + surrogateDiagTailX0RatChunk000Sub000Block119Part021
    + surrogateDiagTailX0RatChunk000Sub000Block119Part022
    + surrogateDiagTailX0RatChunk000Sub000Block119Part023
    + surrogateDiagTailX0RatChunk000Sub000Block119Part024

def surrogateDiagonalTailChunk000Sub000Block119Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub000Block119HeadSum X0
    + surrogateDiagonalTailChunk000Sub000Block119MidSum X0
    + surrogateDiagonalTailChunk000Sub000Block119TailSum X0

def surrogateDiagTailX0RatChunk000Sub000Block119 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block119Part000
    + surrogateDiagTailX0RatChunk000Sub000Block119Part001
    + surrogateDiagTailX0RatChunk000Sub000Block119Part002
    + surrogateDiagTailX0RatChunk000Sub000Block119Part003
    + surrogateDiagTailX0RatChunk000Sub000Block119Part004
    + surrogateDiagTailX0RatChunk000Sub000Block119Part005
    + surrogateDiagTailX0RatChunk000Sub000Block119Part006
    + surrogateDiagTailX0RatChunk000Sub000Block119Part007
    + surrogateDiagTailX0RatChunk000Sub000Block119Part008
    + surrogateDiagTailX0RatChunk000Sub000Block119Part009
    + surrogateDiagTailX0RatChunk000Sub000Block119Part010
    + surrogateDiagTailX0RatChunk000Sub000Block119Part011
    + surrogateDiagTailX0RatChunk000Sub000Block119Part012
    + surrogateDiagTailX0RatChunk000Sub000Block119Part013
    + surrogateDiagTailX0RatChunk000Sub000Block119Part014
    + surrogateDiagTailX0RatChunk000Sub000Block119Part015
    + surrogateDiagTailX0RatChunk000Sub000Block119Part016
    + surrogateDiagTailX0RatChunk000Sub000Block119Part017
    + surrogateDiagTailX0RatChunk000Sub000Block119Part018
    + surrogateDiagTailX0RatChunk000Sub000Block119Part019
    + surrogateDiagTailX0RatChunk000Sub000Block119Part020
    + surrogateDiagTailX0RatChunk000Sub000Block119Part021
    + surrogateDiagTailX0RatChunk000Sub000Block119Part022
    + surrogateDiagTailX0RatChunk000Sub000Block119Part023
    + surrogateDiagTailX0RatChunk000Sub000Block119Part024

theorem surrogateDiagTailX0RatChunk000Sub000Block119_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk000Sub000Block119Head + surrogateDiagTailX0RatChunk000Sub000Block119Mid + surrogateDiagTailX0RatChunk000Sub000Block119Tail =
      surrogateDiagTailX0RatChunk000Sub000Block119 := by
  unfold surrogateDiagTailX0RatChunk000Sub000Block119Head surrogateDiagTailX0RatChunk000Sub000Block119Mid surrogateDiagTailX0RatChunk000Sub000Block119Tail surrogateDiagTailX0RatChunk000Sub000Block119
  ring

def SurrogateDiagonalTailChunk000Sub000Block119HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block119HeadSum X0 = surrogateDiagTailX0RatChunk000Sub000Block119Head

def SurrogateDiagonalTailChunk000Sub000Block119MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block119MidSum X0 = surrogateDiagTailX0RatChunk000Sub000Block119Mid

def SurrogateDiagonalTailChunk000Sub000Block119TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block119TailSum X0 = surrogateDiagTailX0RatChunk000Sub000Block119Tail

theorem surrogateDiagonalTailChunk000Sub000Block119_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk000Sub000Block119HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk000Sub000Block119MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk000Sub000Block119TailCertificateAt X0) :
    surrogateDiagonalTailChunk000Sub000Block119Sum X0 = surrogateDiagTailX0RatChunk000Sub000Block119 := by
  unfold SurrogateDiagonalTailChunk000Sub000Block119HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk000Sub000Block119MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk000Sub000Block119TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk000Sub000Block119Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk000Sub000Block119_eq_head_add_mid_add_tail

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

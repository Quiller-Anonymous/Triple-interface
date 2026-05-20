import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0TailPilot25

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

open scoped BigOperators

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

/- Generated direct-term certificate blocks for tail chunk 000, subchunk 000, blocks [195,196). -/

/-- Block 195 covers tail-support indices [4875,4900) and q from 8066 to 8105. -/

def TailChunk000Sub000Block195Part000SupportExplicit : Finset ℕ :=
  ([8066] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block195Part000 : ℚ :=
  (1932988026625 : ℚ) / 571389011211091968

def SurrogateDiagonalTailChunk000Sub000Block195Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8066
    = surrogateDiagTailX0RatChunk000Sub000Block195Part000

theorem surrogateDiagonalTailChunk000Sub000Block195Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block195Part000CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block195Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block195Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block195Part000CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block195Part000SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block195Part000] using hcert

def TailChunk000Sub000Block195Part001SupportExplicit : Finset ℕ :=
  ([8067] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block195Part001 : ℚ :=
  (1129453068725 : ℚ) / 1044320740750393344

def SurrogateDiagonalTailChunk000Sub000Block195Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8067
    = surrogateDiagTailX0RatChunk000Sub000Block195Part001

theorem surrogateDiagonalTailChunk000Sub000Block195Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block195Part001CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block195Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block195Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block195Part001CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block195Part001SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block195Part001] using hcert

def TailChunk000Sub000Block195Part002SupportExplicit : Finset ℕ :=
  ([8069] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block195Part002 : ℚ :=
  (1017324390625 : ℚ) / 2648685693215760672

def SurrogateDiagonalTailChunk000Sub000Block195Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8069
    = surrogateDiagTailX0RatChunk000Sub000Block195Part002

theorem surrogateDiagonalTailChunk000Sub000Block195Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block195Part002CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block195Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block195Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block195Part002CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block195Part002SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block195Part002] using hcert

def TailChunk000Sub000Block195Part003SupportExplicit : Finset ℕ :=
  ([8070] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block195Part003 : ℚ :=
  (841989636775 : ℚ) / 52835519625166848

def SurrogateDiagonalTailChunk000Sub000Block195Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8070
    = surrogateDiagTailX0RatChunk000Sub000Block195Part003

theorem surrogateDiagonalTailChunk000Sub000Block195Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block195Part003CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block195Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block195Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block195Part003CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block195Part003SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block195Part003] using hcert

def TailChunk000Sub000Block195Part004SupportExplicit : Finset ℕ :=
  ([8071] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block195Part004 : ℚ :=
  (179843639975 : ℚ) / 317080308207845376

def SurrogateDiagonalTailChunk000Sub000Block195Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8071
    = surrogateDiagTailX0RatChunk000Sub000Block195Part004

theorem surrogateDiagonalTailChunk000Sub000Block195Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block195Part004CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block195Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block195Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block195Part004CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block195Part004SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block195Part004] using hcert

def TailChunk000Sub000Block195Part005SupportExplicit : Finset ℕ :=
  ([8074] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block195Part005 : ℚ :=
  (71131190941 : ℚ) / 17947798777987200

def SurrogateDiagonalTailChunk000Sub000Block195Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8074
    = surrogateDiagTailX0RatChunk000Sub000Block195Part005

theorem surrogateDiagonalTailChunk000Sub000Block195Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block195Part005CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block195Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block195Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block195Part005CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block195Part005SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block195Part005] using hcert

def TailChunk000Sub000Block195Part006SupportExplicit : Finset ℕ :=
  ([8077] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block195Part006 : ℚ :=
  (22355918017 : ℚ) / 53982508390809600

def SurrogateDiagonalTailChunk000Sub000Block195Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8077
    = surrogateDiagTailX0RatChunk000Sub000Block195Part006

theorem surrogateDiagonalTailChunk000Sub000Block195Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block195Part006CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block195Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block195Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block195Part006CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block195Part006SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block195Part006] using hcert

def TailChunk000Sub000Block195Part007SupportExplicit : Finset ℕ :=
  ([8078] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block195Part007 : ℚ :=
  (410059311475 : ℚ) / 89178836683456512

def SurrogateDiagonalTailChunk000Sub000Block195Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8078
    = surrogateDiagTailX0RatChunk000Sub000Block195Part007

theorem surrogateDiagonalTailChunk000Sub000Block195Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block195Part007CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block195Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block195Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block195Part007CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block195Part007SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block195Part007] using hcert

def TailChunk000Sub000Block195Part008SupportExplicit : Finset ℕ :=
  ([8079] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block195Part008 : ℚ :=
  (1132816106675 : ℚ) / 1050550824841257984

def SurrogateDiagonalTailChunk000Sub000Block195Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8079
    = surrogateDiagTailX0RatChunk000Sub000Block195Part008

theorem surrogateDiagonalTailChunk000Sub000Block195Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block195Part008CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block195Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block195Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block195Part008CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block195Part008SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block195Part008] using hcert

def TailChunk000Sub000Block195Part009SupportExplicit : Finset ℕ :=
  ([8081] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block195Part009 : ℚ :=
  (1632564025 : ℚ) / 4263166487764992

def SurrogateDiagonalTailChunk000Sub000Block195Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8081
    = surrogateDiagTailX0RatChunk000Sub000Block195Part009

theorem surrogateDiagonalTailChunk000Sub000Block195Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block195Part009CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block195Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block195Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block195Part009CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block195Part009SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block195Part009] using hcert

def TailChunk000Sub000Block195Part010SupportExplicit : Finset ℕ :=
  ([8083] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block195Part010 : ℚ :=
  (82271732775 : ℚ) / 201675540358076416

def SurrogateDiagonalTailChunk000Sub000Block195Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8083
    = surrogateDiagTailX0RatChunk000Sub000Block195Part010

theorem surrogateDiagonalTailChunk000Sub000Block195Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block195Part010CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block195Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block195Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block195Part010CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block195Part010SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block195Part010] using hcert

def TailChunk000Sub000Block195Part011SupportExplicit : Finset ℕ :=
  ([8086] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block195Part011 : ℚ :=
  (19178361707 : ℚ) / 9576980741145600

def SurrogateDiagonalTailChunk000Sub000Block195Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8086
    = surrogateDiagTailX0RatChunk000Sub000Block195Part011

theorem surrogateDiagonalTailChunk000Sub000Block195Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block195Part011CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block195Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block195Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block195Part011CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block195Part011SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block195Part011] using hcert

def TailChunk000Sub000Block195Part012SupportExplicit : Finset ℕ :=
  ([8087] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block195Part012 : ℚ :=
  (1021868265625 : ℚ) / 2672402168867071602

def SurrogateDiagonalTailChunk000Sub000Block195Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8087
    = surrogateDiagTailX0RatChunk000Sub000Block195Part012

theorem surrogateDiagonalTailChunk000Sub000Block195Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block195Part012CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block195Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block195Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block195Part012CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block195Part012SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block195Part012] using hcert

def TailChunk000Sub000Block195Part013SupportExplicit : Finset ℕ :=
  ([8089] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block195Part013 : ℚ :=
  (1022373765625 : ℚ) / 2675047129366344192

def SurrogateDiagonalTailChunk000Sub000Block195Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8089
    = surrogateDiagTailX0RatChunk000Sub000Block195Part013

theorem surrogateDiagonalTailChunk000Sub000Block195Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block195Part013CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block195Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block195Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block195Part013CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block195Part013SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block195Part013] using hcert

def TailChunk000Sub000Block195Part014SupportExplicit : Finset ℕ :=
  ([8090] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block195Part014 : ℚ :=
  (286099017375 : ℚ) / 90947551738986496

def SurrogateDiagonalTailChunk000Sub000Block195Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8090
    = surrogateDiagTailX0RatChunk000Sub000Block195Part014

theorem surrogateDiagonalTailChunk000Sub000Block195Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block195Part014CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block195Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block195Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block195Part014CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block195Part014SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block195Part014] using hcert

def TailChunk000Sub000Block195Part015SupportExplicit : Finset ℕ :=
  ([8093] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block195Part015 : ℚ :=
  (1023385140625 : ℚ) / 2680342939930266912

def SurrogateDiagonalTailChunk000Sub000Block195Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8093
    = surrogateDiagTailX0RatChunk000Sub000Block195Part015

theorem surrogateDiagonalTailChunk000Sub000Block195Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block195Part015CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block195Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block195Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block195Part015CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block195Part015SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block195Part015] using hcert

def TailChunk000Sub000Block195Part016SupportExplicit : Finset ℕ :=
  ([8094] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block195Part016 : ℚ :=
  (29849685307 : ℚ) / 4033564567603200

def SurrogateDiagonalTailChunk000Sub000Block195Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8094
    = surrogateDiagTailX0RatChunk000Sub000Block195Part016

theorem surrogateDiagonalTailChunk000Sub000Block195Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block195Part016CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block195Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block195Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block195Part016CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block195Part016SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block195Part016] using hcert

def TailChunk000Sub000Block195Part017SupportExplicit : Finset ℕ :=
  ([8095] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block195Part017 : ℚ :=
  (982290974475 : ℚ) / 1462377978664523776

def SurrogateDiagonalTailChunk000Sub000Block195Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8095
    = surrogateDiagTailX0RatChunk000Sub000Block195Part017

theorem surrogateDiagonalTailChunk000Sub000Block195Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block195Part017CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block195Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block195Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block195Part017CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block195Part017SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block195Part017] using hcert

def TailChunk000Sub000Block195Part018SupportExplicit : Finset ℕ :=
  ([8097] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block195Part018 : ℚ :=
  (284467510025 : ℚ) / 264987041178953616

def SurrogateDiagonalTailChunk000Sub000Block195Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8097
    = surrogateDiagTailX0RatChunk000Sub000Block195Part018

theorem surrogateDiagonalTailChunk000Sub000Block195Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block195Part018CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block195Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block195Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block195Part018CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block195Part018SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block195Part018] using hcert

def TailChunk000Sub000Block195Part019SupportExplicit : Finset ℕ :=
  ([8098] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block195Part019 : ℚ :=
  (256162515625 : ℚ) / 167852913107607552

def SurrogateDiagonalTailChunk000Sub000Block195Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8098
    = surrogateDiagTailX0RatChunk000Sub000Block195Part019

theorem surrogateDiagonalTailChunk000Sub000Block195Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block195Part019CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block195Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block195Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block195Part019CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block195Part019SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block195Part019] using hcert

def TailChunk000Sub000Block195Part020SupportExplicit : Finset ℕ :=
  ([8099] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block195Part020 : ℚ :=
  (2884945189675 : ℚ) / 4029837493464465408

def SurrogateDiagonalTailChunk000Sub000Block195Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8099
    = surrogateDiagTailX0RatChunk000Sub000Block195Part020

theorem surrogateDiagonalTailChunk000Sub000Block195Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block195Part020CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block195Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block195Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block195Part020CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block195Part020SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block195Part020] using hcert

def TailChunk000Sub000Block195Part021SupportExplicit : Finset ℕ :=
  ([8101] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block195Part021 : ℚ :=
  (65626201 : ℚ) / 172221321376800

def SurrogateDiagonalTailChunk000Sub000Block195Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8101
    = surrogateDiagTailX0RatChunk000Sub000Block195Part021

theorem surrogateDiagonalTailChunk000Sub000Block195Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block195Part021CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block195Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block195Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block195Part021CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block195Part021SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block195Part021] using hcert

def TailChunk000Sub000Block195Part022SupportExplicit : Finset ℕ :=
  ([8102] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block195Part022 : ℚ :=
  (16410601 : ℚ) / 10763832586050

def SurrogateDiagonalTailChunk000Sub000Block195Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8102
    = surrogateDiagTailX0RatChunk000Sub000Block195Part022

theorem surrogateDiagonalTailChunk000Sub000Block195Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block195Part022CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block195Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block195Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block195Part022CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block195Part022SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block195Part022] using hcert

def TailChunk000Sub000Block195Part023SupportExplicit : Finset ℕ :=
  ([8103] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block195Part023 : ℚ :=
  (1743846147625 : ℚ) / 1805871442839994368

def SurrogateDiagonalTailChunk000Sub000Block195Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8103
    = surrogateDiagTailX0RatChunk000Sub000Block195Part023

theorem surrogateDiagonalTailChunk000Sub000Block195Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block195Part023CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block195Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block195Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block195Part023CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block195Part023SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block195Part023] using hcert

def TailChunk000Sub000Block195Part024SupportExplicit : Finset ℕ :=
  ([8105] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block195Part024 : ℚ :=
  (118166382277 : ℚ) / 176354633089843200

def SurrogateDiagonalTailChunk000Sub000Block195Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8105
    = surrogateDiagTailX0RatChunk000Sub000Block195Part024

theorem surrogateDiagonalTailChunk000Sub000Block195Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block195Part024CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block195Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block195Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block195Part024CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block195Part024SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block195Part024] using hcert

def surrogateDiagonalTailChunk000Sub000Block195HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block195Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block195Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block195Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block195Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block195Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block195Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block195Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block195Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block195Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block195Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block195Head : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block195Part000
    + surrogateDiagTailX0RatChunk000Sub000Block195Part001
    + surrogateDiagTailX0RatChunk000Sub000Block195Part002
    + surrogateDiagTailX0RatChunk000Sub000Block195Part003
    + surrogateDiagTailX0RatChunk000Sub000Block195Part004
    + surrogateDiagTailX0RatChunk000Sub000Block195Part005
    + surrogateDiagTailX0RatChunk000Sub000Block195Part006
    + surrogateDiagTailX0RatChunk000Sub000Block195Part007
    + surrogateDiagTailX0RatChunk000Sub000Block195Part008
    + surrogateDiagTailX0RatChunk000Sub000Block195Part009

def surrogateDiagonalTailChunk000Sub000Block195MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block195Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block195Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block195Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block195Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block195Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block195Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block195Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block195Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block195Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block195Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block195Mid : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block195Part010
    + surrogateDiagTailX0RatChunk000Sub000Block195Part011
    + surrogateDiagTailX0RatChunk000Sub000Block195Part012
    + surrogateDiagTailX0RatChunk000Sub000Block195Part013
    + surrogateDiagTailX0RatChunk000Sub000Block195Part014
    + surrogateDiagTailX0RatChunk000Sub000Block195Part015
    + surrogateDiagTailX0RatChunk000Sub000Block195Part016
    + surrogateDiagTailX0RatChunk000Sub000Block195Part017
    + surrogateDiagTailX0RatChunk000Sub000Block195Part018
    + surrogateDiagTailX0RatChunk000Sub000Block195Part019

def surrogateDiagonalTailChunk000Sub000Block195TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block195Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block195Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block195Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block195Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block195Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block195Tail : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block195Part020
    + surrogateDiagTailX0RatChunk000Sub000Block195Part021
    + surrogateDiagTailX0RatChunk000Sub000Block195Part022
    + surrogateDiagTailX0RatChunk000Sub000Block195Part023
    + surrogateDiagTailX0RatChunk000Sub000Block195Part024

def surrogateDiagonalTailChunk000Sub000Block195Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub000Block195HeadSum X0
    + surrogateDiagonalTailChunk000Sub000Block195MidSum X0
    + surrogateDiagonalTailChunk000Sub000Block195TailSum X0

def surrogateDiagTailX0RatChunk000Sub000Block195 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block195Part000
    + surrogateDiagTailX0RatChunk000Sub000Block195Part001
    + surrogateDiagTailX0RatChunk000Sub000Block195Part002
    + surrogateDiagTailX0RatChunk000Sub000Block195Part003
    + surrogateDiagTailX0RatChunk000Sub000Block195Part004
    + surrogateDiagTailX0RatChunk000Sub000Block195Part005
    + surrogateDiagTailX0RatChunk000Sub000Block195Part006
    + surrogateDiagTailX0RatChunk000Sub000Block195Part007
    + surrogateDiagTailX0RatChunk000Sub000Block195Part008
    + surrogateDiagTailX0RatChunk000Sub000Block195Part009
    + surrogateDiagTailX0RatChunk000Sub000Block195Part010
    + surrogateDiagTailX0RatChunk000Sub000Block195Part011
    + surrogateDiagTailX0RatChunk000Sub000Block195Part012
    + surrogateDiagTailX0RatChunk000Sub000Block195Part013
    + surrogateDiagTailX0RatChunk000Sub000Block195Part014
    + surrogateDiagTailX0RatChunk000Sub000Block195Part015
    + surrogateDiagTailX0RatChunk000Sub000Block195Part016
    + surrogateDiagTailX0RatChunk000Sub000Block195Part017
    + surrogateDiagTailX0RatChunk000Sub000Block195Part018
    + surrogateDiagTailX0RatChunk000Sub000Block195Part019
    + surrogateDiagTailX0RatChunk000Sub000Block195Part020
    + surrogateDiagTailX0RatChunk000Sub000Block195Part021
    + surrogateDiagTailX0RatChunk000Sub000Block195Part022
    + surrogateDiagTailX0RatChunk000Sub000Block195Part023
    + surrogateDiagTailX0RatChunk000Sub000Block195Part024

theorem surrogateDiagTailX0RatChunk000Sub000Block195_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk000Sub000Block195Head + surrogateDiagTailX0RatChunk000Sub000Block195Mid + surrogateDiagTailX0RatChunk000Sub000Block195Tail =
      surrogateDiagTailX0RatChunk000Sub000Block195 := by
  unfold surrogateDiagTailX0RatChunk000Sub000Block195Head surrogateDiagTailX0RatChunk000Sub000Block195Mid surrogateDiagTailX0RatChunk000Sub000Block195Tail surrogateDiagTailX0RatChunk000Sub000Block195
  ring

def SurrogateDiagonalTailChunk000Sub000Block195HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block195HeadSum X0 = surrogateDiagTailX0RatChunk000Sub000Block195Head

def SurrogateDiagonalTailChunk000Sub000Block195MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block195MidSum X0 = surrogateDiagTailX0RatChunk000Sub000Block195Mid

def SurrogateDiagonalTailChunk000Sub000Block195TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block195TailSum X0 = surrogateDiagTailX0RatChunk000Sub000Block195Tail

theorem surrogateDiagonalTailChunk000Sub000Block195_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk000Sub000Block195HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk000Sub000Block195MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk000Sub000Block195TailCertificateAt X0) :
    surrogateDiagonalTailChunk000Sub000Block195Sum X0 = surrogateDiagTailX0RatChunk000Sub000Block195 := by
  unfold SurrogateDiagonalTailChunk000Sub000Block195HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk000Sub000Block195MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk000Sub000Block195TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk000Sub000Block195Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk000Sub000Block195_eq_head_add_mid_add_tail

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

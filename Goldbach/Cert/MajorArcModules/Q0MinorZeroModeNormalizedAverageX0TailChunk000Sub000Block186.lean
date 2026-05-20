import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0TailPilot25

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

open scoped BigOperators

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

/- Generated direct-term certificate blocks for tail chunk 000, subchunk 000, blocks [186,187). -/

/-- Block 186 covers tail-support indices [4650,4675) and q from 7698 to 7735. -/

def TailChunk000Sub000Block186Part000SupportExplicit : Finset ℕ :=
  ([7698] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block186Part000 : ℚ :=
  (513975130475 : ℚ) / 54034227456074304

def SurrogateDiagonalTailChunk000Sub000Block186Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7698
    = surrogateDiagTailX0RatChunk000Sub000Block186Part000

theorem surrogateDiagonalTailChunk000Sub000Block186Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block186Part000CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block186Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block186Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block186Part000CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block186Part000SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block186Part000] using hcert

def TailChunk000Sub000Block186Part001SupportExplicit : Finset ℕ :=
  ([7699] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block186Part001 : ℚ :=
  (926165640625 : ℚ) / 2195222243353349202

def SurrogateDiagonalTailChunk000Sub000Block186Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7699
    = surrogateDiagTailX0RatChunk000Sub000Block186Part001

theorem surrogateDiagonalTailChunk000Sub000Block186Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block186Part001CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block186Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block186Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block186Part001CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block186Part001SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block186Part001] using hcert

def TailChunk000Sub000Block186Part002SupportExplicit : Finset ℕ :=
  ([7701] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block186Part002 : ℚ :=
  (37919811653 : ℚ) / 26547388416000000

def SurrogateDiagonalTailChunk000Sub000Block186Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7701
    = surrogateDiagTailX0RatChunk000Sub000Block186Part002

theorem surrogateDiagonalTailChunk000Sub000Block186Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block186Part002CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block186Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block186Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block186Part002CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block186Part002SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block186Part002] using hcert

def TailChunk000Sub000Block186Part003SupportExplicit : Finset ℕ :=
  ([7702] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block186Part003 : ℚ :=
  (74136174799 : ℚ) / 21975044755125000

def SurrogateDiagonalTailChunk000Sub000Block186Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7702
    = surrogateDiagTailX0RatChunk000Sub000Block186Part003

theorem surrogateDiagonalTailChunk000Sub000Block186Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block186Part003CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block186Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block186Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block186Part003CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block186Part003SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block186Part003] using hcert

def TailChunk000Sub000Block186Part004SupportExplicit : Finset ℕ :=
  ([7703] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block186Part004 : ℚ :=
  (927128265625 : ℚ) / 2199788486727410802

def SurrogateDiagonalTailChunk000Sub000Block186Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7703
    = surrogateDiagTailX0RatChunk000Sub000Block186Part004

theorem surrogateDiagonalTailChunk000Sub000Block186Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block186Part004CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block186Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block186Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block186Part004CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block186Part004SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block186Part004] using hcert

def TailChunk000Sub000Block186Part005SupportExplicit : Finset ℕ :=
  ([7705] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block186Part005 : ℚ :=
  (1238080594925 : ℚ) / 1422667118581530624

def SurrogateDiagonalTailChunk000Sub000Block186Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7705
    = surrogateDiagTailX0RatChunk000Sub000Block186Part005

theorem surrogateDiagonalTailChunk000Sub000Block186Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block186Part005CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block186Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block186Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block186Part005CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block186Part005SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block186Part005] using hcert

def TailChunk000Sub000Block186Part006SupportExplicit : Finset ℕ :=
  ([7706] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block186Part006 : ℚ :=
  (1855329984775 : ℚ) / 550518569480596608

def SurrogateDiagonalTailChunk000Sub000Block186Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7706
    = surrogateDiagTailX0RatChunk000Sub000Block186Part006

theorem surrogateDiagonalTailChunk000Sub000Block186Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block186Part006CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block186Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block186Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block186Part006CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block186Part006SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block186Part006] using hcert

def TailChunk000Sub000Block186Part007SupportExplicit : Finset ℕ :=
  ([7707] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block186Part007 : ℚ :=
  (5856803825 : ℚ) / 3230603780037696

def SurrogateDiagonalTailChunk000Sub000Block186Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7707
    = surrogateDiagTailX0RatChunk000Sub000Block186Part007

theorem surrogateDiagonalTailChunk000Sub000Block186Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block186Part007CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block186Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block186Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block186Part007CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block186Part007SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block186Part007] using hcert

def TailChunk000Sub000Block186Part008SupportExplicit : Finset ℕ :=
  ([7709] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block186Part008 : ℚ :=
  (275983393175 : ℚ) / 530710186891935744

def SurrogateDiagonalTailChunk000Sub000Block186Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7709
    = surrogateDiagTailX0RatChunk000Sub000Block186Part008

theorem surrogateDiagonalTailChunk000Sub000Block186Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block186Part008CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block186Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block186Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block186Part008CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block186Part008SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block186Part008] using hcert

def TailChunk000Sub000Block186Part009SupportExplicit : Finset ℕ :=
  ([7710] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block186Part009 : ℚ :=
  (174262611075 : ℚ) / 14663087068020736

def SurrogateDiagonalTailChunk000Sub000Block186Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7710
    = surrogateDiagTailX0RatChunk000Sub000Block186Part009

theorem surrogateDiagonalTailChunk000Sub000Block186Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block186Part009CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block186Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block186Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block186Part009CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block186Part009SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block186Part009] using hcert

def TailChunk000Sub000Block186Part010SupportExplicit : Finset ℕ :=
  ([7711] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block186Part010 : ℚ :=
  (12999692497 : ℚ) / 24014802000000000

def SurrogateDiagonalTailChunk000Sub000Block186Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7711
    = surrogateDiagTailX0RatChunk000Sub000Block186Part010

theorem surrogateDiagonalTailChunk000Sub000Block186Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block186Part010CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block186Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block186Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block186Part010CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block186Part010SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block186Part010] using hcert

def TailChunk000Sub000Block186Part011SupportExplicit : Finset ℕ :=
  ([7714] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block186Part011 : ℚ :=
  (194624078275 : ℚ) / 52274996796137472

def SurrogateDiagonalTailChunk000Sub000Block186Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7714
    = surrogateDiagTailX0RatChunk000Sub000Block186Part011

theorem surrogateDiagonalTailChunk000Sub000Block186Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block186Part011CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block186Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block186Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block186Part011CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block186Part011SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block186Part011] using hcert

def TailChunk000Sub000Block186Part012SupportExplicit : Finset ℕ :=
  ([7715] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block186Part012 : ℚ :=
  (2676650887825 : ℚ) / 3619131130895321088

def SurrogateDiagonalTailChunk000Sub000Block186Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7715
    = surrogateDiagTailX0RatChunk000Sub000Block186Part012

theorem surrogateDiagonalTailChunk000Sub000Block186Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block186Part012CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block186Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block186Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block186Part012CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block186Part012SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block186Part012] using hcert

def TailChunk000Sub000Block186Part013SupportExplicit : Finset ℕ :=
  ([7717] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block186Part013 : ℚ :=
  (930501390625 : ℚ) / 2215826456464917792

def SurrogateDiagonalTailChunk000Sub000Block186Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7717
    = surrogateDiagTailX0RatChunk000Sub000Block186Part013

theorem surrogateDiagonalTailChunk000Sub000Block186Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block186Part013CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block186Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block186Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block186Part013CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block186Part013SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block186Part013] using hcert

def TailChunk000Sub000Block186Part014SupportExplicit : Finset ℕ :=
  ([7718] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block186Part014 : ℚ :=
  (889395954025 : ℚ) / 427504357794643968

def SurrogateDiagonalTailChunk000Sub000Block186Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7718
    = surrogateDiagTailX0RatChunk000Sub000Block186Part014

theorem surrogateDiagonalTailChunk000Sub000Block186Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block186Part014CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block186Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block186Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block186Part014CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block186Part014SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block186Part014] using hcert

def TailChunk000Sub000Block186Part015SupportExplicit : Finset ℕ :=
  ([7719] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block186Part015 : ℚ :=
  (7832999263 : ℚ) / 5860669909201920

def SurrogateDiagonalTailChunk000Sub000Block186Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7719
    = surrogateDiagTailX0RatChunk000Sub000Block186Part015

theorem surrogateDiagonalTailChunk000Sub000Block186Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block186Part015CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block186Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block186Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block186Part015CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block186Part015SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block186Part015] using hcert

def TailChunk000Sub000Block186Part016SupportExplicit : Finset ℕ :=
  ([7721] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block186Part016 : ℚ :=
  (164579834975 : ℚ) / 265512965513587776

def SurrogateDiagonalTailChunk000Sub000Block186Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7721
    = surrogateDiagTailX0RatChunk000Sub000Block186Part016

theorem surrogateDiagonalTailChunk000Sub000Block186Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block186Part016CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block186Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block186Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block186Part016CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block186Part016SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block186Part016] using hcert

def TailChunk000Sub000Block186Part017SupportExplicit : Finset ℕ :=
  ([7723] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block186Part017 : ℚ :=
  (931948890625 : ℚ) / 2222726650409204082

def SurrogateDiagonalTailChunk000Sub000Block186Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7723
    = surrogateDiagTailX0RatChunk000Sub000Block186Part017

theorem surrogateDiagonalTailChunk000Sub000Block186Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block186Part017CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block186Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block186Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block186Part017CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block186Part017SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block186Part017] using hcert

def TailChunk000Sub000Block186Part018SupportExplicit : Finset ℕ :=
  ([7726] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block186Part018 : ℚ :=
  (233168265625 : ℚ) / 139064393268400242

def SurrogateDiagonalTailChunk000Sub000Block186Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7726
    = surrogateDiagTailX0RatChunk000Sub000Block186Part018

theorem surrogateDiagonalTailChunk000Sub000Block186Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block186Part018CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block186Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block186Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block186Part018CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block186Part018SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block186Part018] using hcert

def TailChunk000Sub000Block186Part019SupportExplicit : Finset ℕ :=
  ([7727] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block186Part019 : ℚ :=
  (932914515625 : ℚ) / 2227335724342864722

def SurrogateDiagonalTailChunk000Sub000Block186Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7727
    = surrogateDiagTailX0RatChunk000Sub000Block186Part019

theorem surrogateDiagonalTailChunk000Sub000Block186Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block186Part019CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block186Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block186Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block186Part019CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block186Part019SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block186Part019] using hcert

def TailChunk000Sub000Block186Part020SupportExplicit : Finset ℕ :=
  ([7729] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block186Part020 : ℚ :=
  (144436024093 : ℚ) / 323275084344451200

def SurrogateDiagonalTailChunk000Sub000Block186Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7729
    = surrogateDiagTailX0RatChunk000Sub000Block186Part020

theorem surrogateDiagonalTailChunk000Sub000Block186Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block186Part020CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block186Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block186Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block186Part020CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block186Part020SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block186Part020] using hcert

def TailChunk000Sub000Block186Part021SupportExplicit : Finset ℕ :=
  ([7730] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block186Part021 : ℚ :=
  (820861739275 : ℚ) / 227371499290656768

def SurrogateDiagonalTailChunk000Sub000Block186Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7730
    = surrogateDiagTailX0RatChunk000Sub000Block186Part021

theorem surrogateDiagonalTailChunk000Sub000Block186Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block186Part021CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block186Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block186Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block186Part021CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block186Part021SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block186Part021] using hcert

def TailChunk000Sub000Block186Part022SupportExplicit : Finset ℕ :=
  ([7733] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block186Part022 : ℚ :=
  (117404093737 : ℚ) / 176354633089843200

def SurrogateDiagonalTailChunk000Sub000Block186Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7733
    = surrogateDiagTailX0RatChunk000Sub000Block186Part022

theorem surrogateDiagonalTailChunk000Sub000Block186Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block186Part022CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block186Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block186Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block186Part022CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block186Part022SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block186Part022] using hcert

def TailChunk000Sub000Block186Part023SupportExplicit : Finset ℕ :=
  ([7734] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block186Part023 : ℚ :=
  (726537201025 : ℚ) / 110105824567001088

def SurrogateDiagonalTailChunk000Sub000Block186Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7734
    = surrogateDiagTailX0RatChunk000Sub000Block186Part023

theorem surrogateDiagonalTailChunk000Sub000Block186Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block186Part023CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block186Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block186Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block186Part023CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block186Part023SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block186Part023] using hcert

def TailChunk000Sub000Block186Part024SupportExplicit : Finset ℕ :=
  ([7735] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block186Part024 : ℚ :=
  (103259268275 : ℚ) / 62633147300315136

def SurrogateDiagonalTailChunk000Sub000Block186Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7735
    = surrogateDiagTailX0RatChunk000Sub000Block186Part024

theorem surrogateDiagonalTailChunk000Sub000Block186Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block186Part024CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block186Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block186Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block186Part024CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block186Part024SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block186Part024] using hcert

def surrogateDiagonalTailChunk000Sub000Block186HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block186Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block186Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block186Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block186Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block186Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block186Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block186Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block186Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block186Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block186Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block186Head : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block186Part000
    + surrogateDiagTailX0RatChunk000Sub000Block186Part001
    + surrogateDiagTailX0RatChunk000Sub000Block186Part002
    + surrogateDiagTailX0RatChunk000Sub000Block186Part003
    + surrogateDiagTailX0RatChunk000Sub000Block186Part004
    + surrogateDiagTailX0RatChunk000Sub000Block186Part005
    + surrogateDiagTailX0RatChunk000Sub000Block186Part006
    + surrogateDiagTailX0RatChunk000Sub000Block186Part007
    + surrogateDiagTailX0RatChunk000Sub000Block186Part008
    + surrogateDiagTailX0RatChunk000Sub000Block186Part009

def surrogateDiagonalTailChunk000Sub000Block186MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block186Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block186Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block186Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block186Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block186Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block186Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block186Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block186Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block186Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block186Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block186Mid : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block186Part010
    + surrogateDiagTailX0RatChunk000Sub000Block186Part011
    + surrogateDiagTailX0RatChunk000Sub000Block186Part012
    + surrogateDiagTailX0RatChunk000Sub000Block186Part013
    + surrogateDiagTailX0RatChunk000Sub000Block186Part014
    + surrogateDiagTailX0RatChunk000Sub000Block186Part015
    + surrogateDiagTailX0RatChunk000Sub000Block186Part016
    + surrogateDiagTailX0RatChunk000Sub000Block186Part017
    + surrogateDiagTailX0RatChunk000Sub000Block186Part018
    + surrogateDiagTailX0RatChunk000Sub000Block186Part019

def surrogateDiagonalTailChunk000Sub000Block186TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block186Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block186Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block186Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block186Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block186Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block186Tail : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block186Part020
    + surrogateDiagTailX0RatChunk000Sub000Block186Part021
    + surrogateDiagTailX0RatChunk000Sub000Block186Part022
    + surrogateDiagTailX0RatChunk000Sub000Block186Part023
    + surrogateDiagTailX0RatChunk000Sub000Block186Part024

def surrogateDiagonalTailChunk000Sub000Block186Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub000Block186HeadSum X0
    + surrogateDiagonalTailChunk000Sub000Block186MidSum X0
    + surrogateDiagonalTailChunk000Sub000Block186TailSum X0

def surrogateDiagTailX0RatChunk000Sub000Block186 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block186Part000
    + surrogateDiagTailX0RatChunk000Sub000Block186Part001
    + surrogateDiagTailX0RatChunk000Sub000Block186Part002
    + surrogateDiagTailX0RatChunk000Sub000Block186Part003
    + surrogateDiagTailX0RatChunk000Sub000Block186Part004
    + surrogateDiagTailX0RatChunk000Sub000Block186Part005
    + surrogateDiagTailX0RatChunk000Sub000Block186Part006
    + surrogateDiagTailX0RatChunk000Sub000Block186Part007
    + surrogateDiagTailX0RatChunk000Sub000Block186Part008
    + surrogateDiagTailX0RatChunk000Sub000Block186Part009
    + surrogateDiagTailX0RatChunk000Sub000Block186Part010
    + surrogateDiagTailX0RatChunk000Sub000Block186Part011
    + surrogateDiagTailX0RatChunk000Sub000Block186Part012
    + surrogateDiagTailX0RatChunk000Sub000Block186Part013
    + surrogateDiagTailX0RatChunk000Sub000Block186Part014
    + surrogateDiagTailX0RatChunk000Sub000Block186Part015
    + surrogateDiagTailX0RatChunk000Sub000Block186Part016
    + surrogateDiagTailX0RatChunk000Sub000Block186Part017
    + surrogateDiagTailX0RatChunk000Sub000Block186Part018
    + surrogateDiagTailX0RatChunk000Sub000Block186Part019
    + surrogateDiagTailX0RatChunk000Sub000Block186Part020
    + surrogateDiagTailX0RatChunk000Sub000Block186Part021
    + surrogateDiagTailX0RatChunk000Sub000Block186Part022
    + surrogateDiagTailX0RatChunk000Sub000Block186Part023
    + surrogateDiagTailX0RatChunk000Sub000Block186Part024

theorem surrogateDiagTailX0RatChunk000Sub000Block186_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk000Sub000Block186Head + surrogateDiagTailX0RatChunk000Sub000Block186Mid + surrogateDiagTailX0RatChunk000Sub000Block186Tail =
      surrogateDiagTailX0RatChunk000Sub000Block186 := by
  unfold surrogateDiagTailX0RatChunk000Sub000Block186Head surrogateDiagTailX0RatChunk000Sub000Block186Mid surrogateDiagTailX0RatChunk000Sub000Block186Tail surrogateDiagTailX0RatChunk000Sub000Block186
  ring

def SurrogateDiagonalTailChunk000Sub000Block186HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block186HeadSum X0 = surrogateDiagTailX0RatChunk000Sub000Block186Head

def SurrogateDiagonalTailChunk000Sub000Block186MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block186MidSum X0 = surrogateDiagTailX0RatChunk000Sub000Block186Mid

def SurrogateDiagonalTailChunk000Sub000Block186TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block186TailSum X0 = surrogateDiagTailX0RatChunk000Sub000Block186Tail

theorem surrogateDiagonalTailChunk000Sub000Block186_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk000Sub000Block186HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk000Sub000Block186MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk000Sub000Block186TailCertificateAt X0) :
    surrogateDiagonalTailChunk000Sub000Block186Sum X0 = surrogateDiagTailX0RatChunk000Sub000Block186 := by
  unfold SurrogateDiagonalTailChunk000Sub000Block186HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk000Sub000Block186MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk000Sub000Block186TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk000Sub000Block186Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk000Sub000Block186_eq_head_add_mid_add_tail

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

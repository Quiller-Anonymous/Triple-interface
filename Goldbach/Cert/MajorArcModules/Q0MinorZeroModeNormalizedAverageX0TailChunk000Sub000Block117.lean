import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0TailPilot25

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

open scoped BigOperators

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

/- Generated direct-term certificate blocks for tail chunk 000, subchunk 000, blocks [117,118). -/

/- Block 117 covers tail-support indices [2925,2950) and q from 4859 to 4897. -/

def TailChunk000Sub000Block117Part000SupportExplicit : Finset ℕ :=
  ([4859] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block117Part000 : ℚ :=
  (51101742625 : ℚ) / 43725831796555776

def SurrogateDiagonalTailChunk000Sub000Block117Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4859
    = surrogateDiagTailX0RatChunk000Sub000Block117Part000

theorem surrogateDiagonalTailChunk000Sub000Block117Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block117Part000CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block117Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block117Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block117Part000CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block117Part000SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block117Part000] using hcert

def TailChunk000Sub000Block117Part001SupportExplicit : Finset ℕ :=
  ([4861] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block117Part001 : ℚ :=
  (590733025 : ℚ) / 557997081260832

def SurrogateDiagonalTailChunk000Sub000Block117Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4861
    = surrogateDiagTailX0RatChunk000Sub000Block117Part001

theorem surrogateDiagonalTailChunk000Sub000Block117Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block117Part001CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block117Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block117Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block117Part001CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block117Part001SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block117Part001] using hcert

def TailChunk000Sub000Block117Part002SupportExplicit : Finset ℕ :=
  ([4862] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block117Part002 : ℚ :=
  (23544537061 : ℚ) / 1359226286899200

def SurrogateDiagonalTailChunk000Sub000Block117Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4862
    = surrogateDiagTailX0RatChunk000Sub000Block117Part002

theorem surrogateDiagonalTailChunk000Sub000Block117Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block117Part002CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block117Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block117Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block117Part002CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block117Part002SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block117Part002] using hcert

def TailChunk000Sub000Block117Part003SupportExplicit : Finset ℕ :=
  ([4863] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block117Part003 : ℚ :=
  (1313033 : ℚ) / 367332019200

def SurrogateDiagonalTailChunk000Sub000Block117Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4863
    = surrogateDiagTailX0RatChunk000Sub000Block117Part003

theorem surrogateDiagonalTailChunk000Sub000Block117Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block117Part003CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block117Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block117Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block117Part003CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block117Part003SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block117Part003] using hcert

def TailChunk000Sub000Block117Part004SupportExplicit : Finset ℕ :=
  ([4865] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block117Part004 : ℚ :=
  (240125875 : ℚ) / 68787478904832

def SurrogateDiagonalTailChunk000Sub000Block117Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4865
    = surrogateDiagTailX0RatChunk000Sub000Block117Part004

theorem surrogateDiagonalTailChunk000Sub000Block117Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block117Part004CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block117Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block117Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block117Part004CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block117Part004SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block117Part004] using hcert

def TailChunk000Sub000Block117Part005SupportExplicit : Finset ℕ :=
  ([4866] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block117Part005 : ℚ :=
  (29197 : ℚ) / 1020366720

def SurrogateDiagonalTailChunk000Sub000Block117Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4866
    = surrogateDiagTailX0RatChunk000Sub000Block117Part005

theorem surrogateDiagonalTailChunk000Sub000Block117Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block117Part005CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block117Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block117Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block117Part005CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block117Part005SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block117Part005] using hcert

def TailChunk000Sub000Block117Part006SupportExplicit : Finset ℕ :=
  ([4867] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block117Part006 : ℚ :=
  (1584040403 : ℚ) / 1332808524403200

def SurrogateDiagonalTailChunk000Sub000Block117Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4867
    = surrogateDiagTailX0RatChunk000Sub000Block117Part006

theorem surrogateDiagonalTailChunk000Sub000Block117Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block117Part006CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block117Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block117Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block117Part006CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block117Part006SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block117Part006] using hcert

def TailChunk000Sub000Block117Part007SupportExplicit : Finset ℕ :=
  ([4870] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block117Part007 : ℚ :=
  (147964211875 : ℚ) / 8927953300173312

def SurrogateDiagonalTailChunk000Sub000Block117Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4870
    = surrogateDiagTailX0RatChunk000Sub000Block117Part007

theorem surrogateDiagonalTailChunk000Sub000Block117Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block117Part007CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block117Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block117Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block117Part007CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block117Part007SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block117Part007] using hcert

def TailChunk000Sub000Block117Part008SupportExplicit : Finset ℕ :=
  ([4871] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block117Part008 : ℚ :=
  (593166025 : ℚ) / 562603843879122

def SurrogateDiagonalTailChunk000Sub000Block117Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4871
    = surrogateDiagTailX0RatChunk000Sub000Block117Part008

theorem surrogateDiagonalTailChunk000Sub000Block117Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block117Part008CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block117Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block117Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block117Part008CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block117Part008SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block117Part008] using hcert

def TailChunk000Sub000Block117Part009SupportExplicit : Finset ℕ :=
  ([4873] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block117Part009 : ℚ :=
  (2693035499 : ℚ) / 1908736295724960

def SurrogateDiagonalTailChunk000Sub000Block117Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4873
    = surrogateDiagTailX0RatChunk000Sub000Block117Part009

theorem surrogateDiagonalTailChunk000Sub000Block117Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block117Part009CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block117Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block117Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block117Part009CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block117Part009SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block117Part009] using hcert

def TailChunk000Sub000Block117Part010SupportExplicit : Finset ℕ :=
  ([4874] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block117Part010 : ℚ :=
  (742222650775 : ℚ) / 88051345090708608

def SurrogateDiagonalTailChunk000Sub000Block117Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4874
    = surrogateDiagTailX0RatChunk000Sub000Block117Part010

theorem surrogateDiagonalTailChunk000Sub000Block117Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block117Part010CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block117Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block117Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block117Part010CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block117Part010SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block117Part010] using hcert

def TailChunk000Sub000Block117Part011SupportExplicit : Finset ℕ :=
  ([4877] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block117Part011 : ℚ :=
  (371642640625 : ℚ) / 353363473526352672

def SurrogateDiagonalTailChunk000Sub000Block117Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4877
    = surrogateDiagTailX0RatChunk000Sub000Block117Part011

theorem surrogateDiagonalTailChunk000Sub000Block117Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block117Part011CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block117Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block117Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block117Part011CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block117Part011SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block117Part011] using hcert

def TailChunk000Sub000Block117Part012SupportExplicit : Finset ℕ :=
  ([4879] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block117Part012 : ℚ :=
  (325613393 : ℚ) / 151025142988800

def SurrogateDiagonalTailChunk000Sub000Block117Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4879
    = surrogateDiagTailX0RatChunk000Sub000Block117Part012

theorem surrogateDiagonalTailChunk000Sub000Block117Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block117Part012CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block117Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block117Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block117Part012CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block117Part012SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block117Part012] using hcert

def TailChunk000Sub000Block117Part013SupportExplicit : Finset ℕ :=
  ([4881] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block117Part013 : ℚ :=
  (33069275 : ℚ) / 9320107071168

def SurrogateDiagonalTailChunk000Sub000Block117Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4881
    = surrogateDiagTailX0RatChunk000Sub000Block117Part013

theorem surrogateDiagonalTailChunk000Sub000Block117Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block117Part013CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block117Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block117Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block117Part013CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block117Part013SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block117Part013] using hcert

def TailChunk000Sub000Block117Part014SupportExplicit : Finset ℕ :=
  ([4882] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block117Part014 : ℚ :=
  (29786446519 : ℚ) / 3545244203059200

def SurrogateDiagonalTailChunk000Sub000Block117Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4882
    = surrogateDiagTailX0RatChunk000Sub000Block117Part014

theorem surrogateDiagonalTailChunk000Sub000Block117Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block117Part014CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block117Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block117Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block117Part014CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block117Part014SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block117Part014] using hcert

def TailChunk000Sub000Block117Part015SupportExplicit : Finset ℕ :=
  ([4883] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block117Part015 : ℚ :=
  (351678446575 : ℚ) / 281849162851418112

def SurrogateDiagonalTailChunk000Sub000Block117Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4883
    = surrogateDiagTailX0RatChunk000Sub000Block117Part015

theorem surrogateDiagonalTailChunk000Sub000Block117Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block117Part015CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block117Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block117Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block117Part015CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block117Part015SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block117Part015] using hcert

def TailChunk000Sub000Block117Part016SupportExplicit : Finset ℕ :=
  ([4885] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block117Part016 : ℚ :=
  (596104071875 : ℚ) / 290426405114609664

def SurrogateDiagonalTailChunk000Sub000Block117Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4885
    = surrogateDiagTailX0RatChunk000Sub000Block117Part016

theorem surrogateDiagonalTailChunk000Sub000Block117Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block117Part016CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block117Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block117Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block117Part016CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block117Part016SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block117Part016] using hcert

def TailChunk000Sub000Block117Part017SupportExplicit : Finset ℕ :=
  ([4886] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block117Part017 : ℚ :=
  (70865857825 : ℚ) / 5280880338634752

def SurrogateDiagonalTailChunk000Sub000Block117Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4886
    = surrogateDiagTailX0RatChunk000Sub000Block117Part017

theorem surrogateDiagonalTailChunk000Sub000Block117Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block117Part017CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block117Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block117Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block117Part017CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block117Part017SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block117Part017] using hcert

def TailChunk000Sub000Block117Part018SupportExplicit : Finset ℕ :=
  ([4889] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block117Part018 : ℚ :=
  (373473765625 : ℚ) / 356854893452308992

def SurrogateDiagonalTailChunk000Sub000Block117Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4889
    = surrogateDiagTailX0RatChunk000Sub000Block117Part018

theorem surrogateDiagonalTailChunk000Sub000Block117Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block117Part018CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block117Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block117Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block117Part018CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block117Part018SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block117Part018] using hcert

def TailChunk000Sub000Block117Part019SupportExplicit : Finset ℕ :=
  ([4890] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block117Part019 : ℚ :=
  (198932247725 : ℚ) / 3527092661796864

def SurrogateDiagonalTailChunk000Sub000Block117Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4890
    = surrogateDiagTailX0RatChunk000Sub000Block117Part019

theorem surrogateDiagonalTailChunk000Sub000Block117Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block117Part019CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block117Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block117Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block117Part019CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block117Part019SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block117Part019] using hcert

def TailChunk000Sub000Block117Part020SupportExplicit : Finset ℕ :=
  ([4891] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block117Part020 : ℚ :=
  (1453792770325 : ℚ) / 1275065769416491008

def SurrogateDiagonalTailChunk000Sub000Block117Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4891
    = surrogateDiagTailX0RatChunk000Sub000Block117Part020

theorem surrogateDiagonalTailChunk000Sub000Block117Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block117Part020CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block117Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block117Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block117Part020CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block117Part020SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block117Part020] using hcert

def TailChunk000Sub000Block117Part021SupportExplicit : Finset ℕ :=
  ([4893] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block117Part021 : ℚ :=
  (213748837225 : ℚ) / 37552926852513792

def SurrogateDiagonalTailChunk000Sub000Block117Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4893
    = surrogateDiagTailX0RatChunk000Sub000Block117Part021

theorem surrogateDiagonalTailChunk000Sub000Block117Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block117Part021CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block117Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block117Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block117Part021CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block117Part021SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block117Part021] using hcert

def TailChunk000Sub000Block117Part022SupportExplicit : Finset ℕ :=
  ([4894] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block117Part022 : ℚ :=
  (748326429775 : ℚ) / 89506107299571528

def SurrogateDiagonalTailChunk000Sub000Block117Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4894
    = surrogateDiagTailX0RatChunk000Sub000Block117Part022

theorem surrogateDiagonalTailChunk000Sub000Block117Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block117Part022CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block117Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block117Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block117Part022CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block117Part022SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block117Part022] using hcert

def TailChunk000Sub000Block117Part023SupportExplicit : Finset ℕ :=
  ([4895] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block117Part023 : ℚ :=
  (43134313579 : ℚ) / 15355271656243200

def SurrogateDiagonalTailChunk000Sub000Block117Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4895
    = surrogateDiagTailX0RatChunk000Sub000Block117Part023

theorem surrogateDiagonalTailChunk000Sub000Block117Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block117Part023CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block117Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block117Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block117Part023CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block117Part023SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block117Part023] using hcert

def TailChunk000Sub000Block117Part024SupportExplicit : Finset ℕ :=
  ([4897] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block117Part024 : ℚ :=
  (728385745475 : ℚ) / 639682171921333824

def SurrogateDiagonalTailChunk000Sub000Block117Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4897
    = surrogateDiagTailX0RatChunk000Sub000Block117Part024

theorem surrogateDiagonalTailChunk000Sub000Block117Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block117Part024CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block117Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block117Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block117Part024CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block117Part024SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block117Part024] using hcert

def surrogateDiagonalTailChunk000Sub000Block117HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block117Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block117Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block117Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block117Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block117Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block117Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block117Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block117Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block117Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block117Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block117Head : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block117Part000
    + surrogateDiagTailX0RatChunk000Sub000Block117Part001
    + surrogateDiagTailX0RatChunk000Sub000Block117Part002
    + surrogateDiagTailX0RatChunk000Sub000Block117Part003
    + surrogateDiagTailX0RatChunk000Sub000Block117Part004
    + surrogateDiagTailX0RatChunk000Sub000Block117Part005
    + surrogateDiagTailX0RatChunk000Sub000Block117Part006
    + surrogateDiagTailX0RatChunk000Sub000Block117Part007
    + surrogateDiagTailX0RatChunk000Sub000Block117Part008
    + surrogateDiagTailX0RatChunk000Sub000Block117Part009

def surrogateDiagonalTailChunk000Sub000Block117MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block117Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block117Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block117Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block117Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block117Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block117Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block117Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block117Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block117Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block117Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block117Mid : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block117Part010
    + surrogateDiagTailX0RatChunk000Sub000Block117Part011
    + surrogateDiagTailX0RatChunk000Sub000Block117Part012
    + surrogateDiagTailX0RatChunk000Sub000Block117Part013
    + surrogateDiagTailX0RatChunk000Sub000Block117Part014
    + surrogateDiagTailX0RatChunk000Sub000Block117Part015
    + surrogateDiagTailX0RatChunk000Sub000Block117Part016
    + surrogateDiagTailX0RatChunk000Sub000Block117Part017
    + surrogateDiagTailX0RatChunk000Sub000Block117Part018
    + surrogateDiagTailX0RatChunk000Sub000Block117Part019

def surrogateDiagonalTailChunk000Sub000Block117TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block117Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block117Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block117Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block117Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block117Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block117Tail : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block117Part020
    + surrogateDiagTailX0RatChunk000Sub000Block117Part021
    + surrogateDiagTailX0RatChunk000Sub000Block117Part022
    + surrogateDiagTailX0RatChunk000Sub000Block117Part023
    + surrogateDiagTailX0RatChunk000Sub000Block117Part024

def surrogateDiagonalTailChunk000Sub000Block117Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub000Block117HeadSum X0
    + surrogateDiagonalTailChunk000Sub000Block117MidSum X0
    + surrogateDiagonalTailChunk000Sub000Block117TailSum X0

def surrogateDiagTailX0RatChunk000Sub000Block117 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block117Part000
    + surrogateDiagTailX0RatChunk000Sub000Block117Part001
    + surrogateDiagTailX0RatChunk000Sub000Block117Part002
    + surrogateDiagTailX0RatChunk000Sub000Block117Part003
    + surrogateDiagTailX0RatChunk000Sub000Block117Part004
    + surrogateDiagTailX0RatChunk000Sub000Block117Part005
    + surrogateDiagTailX0RatChunk000Sub000Block117Part006
    + surrogateDiagTailX0RatChunk000Sub000Block117Part007
    + surrogateDiagTailX0RatChunk000Sub000Block117Part008
    + surrogateDiagTailX0RatChunk000Sub000Block117Part009
    + surrogateDiagTailX0RatChunk000Sub000Block117Part010
    + surrogateDiagTailX0RatChunk000Sub000Block117Part011
    + surrogateDiagTailX0RatChunk000Sub000Block117Part012
    + surrogateDiagTailX0RatChunk000Sub000Block117Part013
    + surrogateDiagTailX0RatChunk000Sub000Block117Part014
    + surrogateDiagTailX0RatChunk000Sub000Block117Part015
    + surrogateDiagTailX0RatChunk000Sub000Block117Part016
    + surrogateDiagTailX0RatChunk000Sub000Block117Part017
    + surrogateDiagTailX0RatChunk000Sub000Block117Part018
    + surrogateDiagTailX0RatChunk000Sub000Block117Part019
    + surrogateDiagTailX0RatChunk000Sub000Block117Part020
    + surrogateDiagTailX0RatChunk000Sub000Block117Part021
    + surrogateDiagTailX0RatChunk000Sub000Block117Part022
    + surrogateDiagTailX0RatChunk000Sub000Block117Part023
    + surrogateDiagTailX0RatChunk000Sub000Block117Part024

theorem surrogateDiagTailX0RatChunk000Sub000Block117_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk000Sub000Block117Head + surrogateDiagTailX0RatChunk000Sub000Block117Mid + surrogateDiagTailX0RatChunk000Sub000Block117Tail =
      surrogateDiagTailX0RatChunk000Sub000Block117 := by
  unfold surrogateDiagTailX0RatChunk000Sub000Block117Head surrogateDiagTailX0RatChunk000Sub000Block117Mid surrogateDiagTailX0RatChunk000Sub000Block117Tail surrogateDiagTailX0RatChunk000Sub000Block117
  ring

def SurrogateDiagonalTailChunk000Sub000Block117HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block117HeadSum X0 = surrogateDiagTailX0RatChunk000Sub000Block117Head

def SurrogateDiagonalTailChunk000Sub000Block117MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block117MidSum X0 = surrogateDiagTailX0RatChunk000Sub000Block117Mid

def SurrogateDiagonalTailChunk000Sub000Block117TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block117TailSum X0 = surrogateDiagTailX0RatChunk000Sub000Block117Tail

theorem surrogateDiagonalTailChunk000Sub000Block117_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk000Sub000Block117HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk000Sub000Block117MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk000Sub000Block117TailCertificateAt X0) :
    surrogateDiagonalTailChunk000Sub000Block117Sum X0 = surrogateDiagTailX0RatChunk000Sub000Block117 := by
  unfold SurrogateDiagonalTailChunk000Sub000Block117HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk000Sub000Block117MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk000Sub000Block117TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk000Sub000Block117Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk000Sub000Block117_eq_head_add_mid_add_tail

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

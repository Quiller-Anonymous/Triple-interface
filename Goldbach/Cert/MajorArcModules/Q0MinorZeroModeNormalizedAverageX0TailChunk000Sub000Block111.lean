import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0TailPilot25

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

open scoped BigOperators

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

/- Generated direct-term certificate blocks for tail chunk 000, subchunk 000, blocks [111,112). -/

/- Block 111 covers tail-support indices [2775,2800) and q from 4614 to 4654. -/

def TailChunk000Sub000Block111Part000SupportExplicit : Finset ℕ :=
  ([4614] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block111Part000 : ℚ :=
  (3281425 : ℚ) / 103079215104

def SurrogateDiagonalTailChunk000Sub000Block111Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4614
    = surrogateDiagTailX0RatChunk000Sub000Block111Part000

theorem surrogateDiagonalTailChunk000Sub000Block111Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block111Part000CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block111Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block111Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block111Part000CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block111Part000SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block111Part000] using hcert

def TailChunk000Sub000Block111Part001SupportExplicit : Finset ℕ :=
  ([4615] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block111Part001 : ℚ :=
  (20408436023 : ℚ) / 6374027958681600

def SurrogateDiagonalTailChunk000Sub000Block111Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4615
    = surrogateDiagTailX0RatChunk000Sub000Block111Part001

theorem surrogateDiagonalTailChunk000Sub000Block111Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block111Part001CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block111Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block111Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block111Part001CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block111Part001SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block111Part001] using hcert

def TailChunk000Sub000Block111Part002SupportExplicit : Finset ℕ :=
  ([4618] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block111Part002 : ℚ :=
  (666301837975 : ℚ) / 70952887926277248

def SurrogateDiagonalTailChunk000Sub000Block111Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4618
    = surrogateDiagTailX0RatChunk000Sub000Block111Part002

theorem surrogateDiagonalTailChunk000Sub000Block111Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block111Part002CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block111Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block111Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block111Part002CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block111Part002SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block111Part002] using hcert

def TailChunk000Sub000Block111Part003SupportExplicit : Finset ℕ :=
  ([4619] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block111Part003 : ℚ :=
  (10294658927 : ℚ) / 7774075003299840

def SurrogateDiagonalTailChunk000Sub000Block111Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4619
    = surrogateDiagTailX0RatChunk000Sub000Block111Part003

theorem surrogateDiagonalTailChunk000Sub000Block111Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block111Part003CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block111Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block111Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block111Part003CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block111Part003SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block111Part003] using hcert

def TailChunk000Sub000Block111Part004SupportExplicit : Finset ℕ :=
  ([4621] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block111Part004 : ℚ :=
  (533841025 : ℚ) / 455674528042272

def SurrogateDiagonalTailChunk000Sub000Block111Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4621
    = surrogateDiagTailX0RatChunk000Sub000Block111Part004

theorem surrogateDiagonalTailChunk000Sub000Block111Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block111Part004CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block111Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block111Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block111Part004CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block111Part004SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block111Part004] using hcert

def TailChunk000Sub000Block111Part005SupportExplicit : Finset ℕ :=
  ([4622] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block111Part005 : ℚ :=
  (26698264279 : ℚ) / 2847965800264200

def SurrogateDiagonalTailChunk000Sub000Block111Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4622
    = surrogateDiagTailX0RatChunk000Sub000Block111Part005

theorem surrogateDiagonalTailChunk000Sub000Block111Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block111Part005CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block111Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block111Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block111Part005CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block111Part005SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block111Part005] using hcert

def TailChunk000Sub000Block111Part006SupportExplicit : Finset ℕ :=
  ([4623] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block111Part006 : ℚ :=
  (421746235325 : ℚ) / 88916694911345664

def SurrogateDiagonalTailChunk000Sub000Block111Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4623
    = surrogateDiagTailX0RatChunk000Sub000Block111Part006

theorem surrogateDiagonalTailChunk000Sub000Block111Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block111Part006CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block111Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block111Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block111Part006CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block111Part006SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block111Part006] using hcert

def TailChunk000Sub000Block111Part007SupportExplicit : Finset ℕ :=
  ([4627] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block111Part007 : ℚ :=
  (169711241 : ℚ) / 91096948546560

def SurrogateDiagonalTailChunk000Sub000Block111Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4627
    = surrogateDiagTailX0RatChunk000Sub000Block111Part007

theorem surrogateDiagonalTailChunk000Sub000Block111Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block111Part007CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block111Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block111Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block111Part007CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block111Part007SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block111Part007] using hcert

def TailChunk000Sub000Block111Part008SupportExplicit : Finset ℕ :=
  ([4629] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block111Part008 : ℚ :=
  (29742875 : ℚ) / 7538348852928

def SurrogateDiagonalTailChunk000Sub000Block111Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4629
    = surrogateDiagTailX0RatChunk000Sub000Block111Part008

theorem surrogateDiagonalTailChunk000Sub000Block111Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block111Part008CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block111Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block111Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block111Part008CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block111Part008SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block111Part008] using hcert

def TailChunk000Sub000Block111Part009SupportExplicit : Finset ℕ :=
  ([4630] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block111Part009 : ℚ :=
  (62367372625 : ℚ) / 2430264149558784

def SurrogateDiagonalTailChunk000Sub000Block111Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4630
    = surrogateDiagTailX0RatChunk000Sub000Block111Part009

theorem surrogateDiagonalTailChunk000Sub000Block111Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block111Part009CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block111Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block111Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block111Part009CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block111Part009SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block111Part009] using hcert

def TailChunk000Sub000Block111Part010SupportExplicit : Finset ℕ :=
  ([4631] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block111Part010 : ℚ :=
  (103049213 : ℚ) / 34581314880000

def SurrogateDiagonalTailChunk000Sub000Block111Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4631
    = surrogateDiagTailX0RatChunk000Sub000Block111Part010

theorem surrogateDiagonalTailChunk000Sub000Block111Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block111Part010CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block111Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block111Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block111Part010CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block111Part010SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block111Part010] using hcert

def TailChunk000Sub000Block111Part011SupportExplicit : Finset ℕ :=
  ([4633] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block111Part011 : ℚ :=
  (51102136157 : ℚ) / 20145076017561600

def SurrogateDiagonalTailChunk000Sub000Block111Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4633
    = surrogateDiagTailX0RatChunk000Sub000Block111Part011

theorem surrogateDiagonalTailChunk000Sub000Block111Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block111Part011CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block111Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block111Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block111Part011CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block111Part011SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block111Part011] using hcert

def TailChunk000Sub000Block111Part012SupportExplicit : Finset ℕ :=
  ([4634] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block111Part012 : ℚ :=
  (23220604411 : ℚ) / 1537261006723200

def SurrogateDiagonalTailChunk000Sub000Block111Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4634
    = surrogateDiagTailX0RatChunk000Sub000Block111Part012

theorem surrogateDiagonalTailChunk000Sub000Block111Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block111Part012CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block111Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block111Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block111Part012CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block111Part012SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block111Part012] using hcert

def TailChunk000Sub000Block111Part013SupportExplicit : Finset ℕ :=
  ([4637] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block111Part013 : ℚ :=
  (335965140625 : ℚ) / 288762356116798752

def SurrogateDiagonalTailChunk000Sub000Block111Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4637
    = surrogateDiagTailX0RatChunk000Sub000Block111Part013

theorem surrogateDiagonalTailChunk000Sub000Block111Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block111Part013CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block111Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block111Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block111Part013CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block111Part013SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block111Part013] using hcert

def TailChunk000Sub000Block111Part014SupportExplicit : Finset ℕ :=
  ([4638] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block111Part014 : ℚ :=
  (242475407825 : ℚ) / 7105359352833024

def SurrogateDiagonalTailChunk000Sub000Block111Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4638
    = surrogateDiagTailX0RatChunk000Sub000Block111Part014

theorem surrogateDiagonalTailChunk000Sub000Block111Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block111Part014CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block111Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block111Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block111Part014CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block111Part014SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block111Part014] using hcert

def TailChunk000Sub000Block111Part015SupportExplicit : Finset ℕ :=
  ([4639] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block111Part015 : ℚ :=
  (336255015625 : ℚ) / 289260974357956242

def SurrogateDiagonalTailChunk000Sub000Block111Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4639
    = surrogateDiagTailX0RatChunk000Sub000Block111Part015

theorem surrogateDiagonalTailChunk000Sub000Block111Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block111Part015CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block111Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block111Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block111Part015CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block111Part015SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block111Part015] using hcert

def TailChunk000Sub000Block111Part016SupportExplicit : Finset ℕ :=
  ([4641] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block111Part016 : ℚ :=
  (339980167775 : ℚ) / 35231145356427264

def SurrogateDiagonalTailChunk000Sub000Block111Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4641
    = surrogateDiagTailX0RatChunk000Sub000Block111Part016

theorem surrogateDiagonalTailChunk000Sub000Block111Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block111Part016CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block111Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block111Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block111Part016CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block111Part016SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block111Part016] using hcert

def TailChunk000Sub000Block111Part017SupportExplicit : Finset ℕ :=
  ([4642] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block111Part017 : ℚ :=
  (195276899 : ℚ) / 15438087000000

def SurrogateDiagonalTailChunk000Sub000Block111Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4642
    = surrogateDiagTailX0RatChunk000Sub000Block111Part017

theorem surrogateDiagonalTailChunk000Sub000Block111Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block111Part017CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block111Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block111Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block111Part017CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block111Part017SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block111Part017] using hcert

def TailChunk000Sub000Block111Part018SupportExplicit : Finset ℕ :=
  ([4643] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block111Part018 : ℚ :=
  (336835140625 : ℚ) / 290260147778281362

def SurrogateDiagonalTailChunk000Sub000Block111Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4643
    = surrogateDiagTailX0RatChunk000Sub000Block111Part018

theorem surrogateDiagonalTailChunk000Sub000Block111Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block111Part018CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block111Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block111Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block111Part018CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block111Part018SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block111Part018] using hcert

def TailChunk000Sub000Block111Part019SupportExplicit : Finset ℕ :=
  ([4645] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block111Part019 : ℚ :=
  (538972647875 : ℚ) / 237371587018358784

def SurrogateDiagonalTailChunk000Sub000Block111Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4645
    = surrogateDiagTailX0RatChunk000Sub000Block111Part019

theorem surrogateDiagonalTailChunk000Sub000Block111Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block111Part019CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block111Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block111Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block111Part019CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block111Part019SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block111Part019] using hcert

def TailChunk000Sub000Block111Part020SupportExplicit : Finset ℕ :=
  ([4646] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block111Part020 : ℚ :=
  (116713849 : ℚ) / 10650129600000

def SurrogateDiagonalTailChunk000Sub000Block111Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4646
    = surrogateDiagTailX0RatChunk000Sub000Block111Part020

theorem surrogateDiagonalTailChunk000Sub000Block111Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block111Part020CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block111Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block111Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block111Part020CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block111Part020SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block111Part020] using hcert

def TailChunk000Sub000Block111Part021SupportExplicit : Finset ℕ :=
  ([4647] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block111Part021 : ℚ :=
  (1049187496525 : ℚ) / 229736852599523328

def SurrogateDiagonalTailChunk000Sub000Block111Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4647
    = surrogateDiagTailX0RatChunk000Sub000Block111Part021

theorem surrogateDiagonalTailChunk000Sub000Block111Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block111Part021CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block111Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block111Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block111Part021CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block111Part021SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block111Part021] using hcert

def TailChunk000Sub000Block111Part022SupportExplicit : Finset ℕ :=
  ([4649] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block111Part022 : ℚ :=
  (337706265625 : ℚ) / 291763758609265152

def SurrogateDiagonalTailChunk000Sub000Block111Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4649
    = surrogateDiagTailX0RatChunk000Sub000Block111Part022

theorem surrogateDiagonalTailChunk000Sub000Block111Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block111Part022CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block111Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block111Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block111Part022CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block111Part022SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block111Part022] using hcert

def TailChunk000Sub000Block111Part023SupportExplicit : Finset ℕ :=
  ([4651] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block111Part023 : ℚ :=
  (21631801 : ℚ) / 18705040510050

def SurrogateDiagonalTailChunk000Sub000Block111Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4651
    = surrogateDiagTailX0RatChunk000Sub000Block111Part023

theorem surrogateDiagonalTailChunk000Sub000Block111Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block111Part023CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block111Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block111Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block111Part023CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block111Part023SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block111Part023] using hcert

def TailChunk000Sub000Block111Part024SupportExplicit : Finset ℕ :=
  ([4654] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block111Part024 : ℚ :=
  (302944220675 : ℚ) / 17350444186638336

def SurrogateDiagonalTailChunk000Sub000Block111Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4654
    = surrogateDiagTailX0RatChunk000Sub000Block111Part024

theorem surrogateDiagonalTailChunk000Sub000Block111Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block111Part024CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block111Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block111Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block111Part024CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block111Part024SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block111Part024] using hcert

def surrogateDiagonalTailChunk000Sub000Block111HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block111Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block111Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block111Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block111Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block111Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block111Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block111Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block111Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block111Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block111Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block111Head : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block111Part000
    + surrogateDiagTailX0RatChunk000Sub000Block111Part001
    + surrogateDiagTailX0RatChunk000Sub000Block111Part002
    + surrogateDiagTailX0RatChunk000Sub000Block111Part003
    + surrogateDiagTailX0RatChunk000Sub000Block111Part004
    + surrogateDiagTailX0RatChunk000Sub000Block111Part005
    + surrogateDiagTailX0RatChunk000Sub000Block111Part006
    + surrogateDiagTailX0RatChunk000Sub000Block111Part007
    + surrogateDiagTailX0RatChunk000Sub000Block111Part008
    + surrogateDiagTailX0RatChunk000Sub000Block111Part009

def surrogateDiagonalTailChunk000Sub000Block111MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block111Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block111Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block111Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block111Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block111Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block111Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block111Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block111Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block111Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block111Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block111Mid : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block111Part010
    + surrogateDiagTailX0RatChunk000Sub000Block111Part011
    + surrogateDiagTailX0RatChunk000Sub000Block111Part012
    + surrogateDiagTailX0RatChunk000Sub000Block111Part013
    + surrogateDiagTailX0RatChunk000Sub000Block111Part014
    + surrogateDiagTailX0RatChunk000Sub000Block111Part015
    + surrogateDiagTailX0RatChunk000Sub000Block111Part016
    + surrogateDiagTailX0RatChunk000Sub000Block111Part017
    + surrogateDiagTailX0RatChunk000Sub000Block111Part018
    + surrogateDiagTailX0RatChunk000Sub000Block111Part019

def surrogateDiagonalTailChunk000Sub000Block111TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block111Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block111Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block111Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block111Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block111Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block111Tail : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block111Part020
    + surrogateDiagTailX0RatChunk000Sub000Block111Part021
    + surrogateDiagTailX0RatChunk000Sub000Block111Part022
    + surrogateDiagTailX0RatChunk000Sub000Block111Part023
    + surrogateDiagTailX0RatChunk000Sub000Block111Part024

def surrogateDiagonalTailChunk000Sub000Block111Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub000Block111HeadSum X0
    + surrogateDiagonalTailChunk000Sub000Block111MidSum X0
    + surrogateDiagonalTailChunk000Sub000Block111TailSum X0

def surrogateDiagTailX0RatChunk000Sub000Block111 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block111Part000
    + surrogateDiagTailX0RatChunk000Sub000Block111Part001
    + surrogateDiagTailX0RatChunk000Sub000Block111Part002
    + surrogateDiagTailX0RatChunk000Sub000Block111Part003
    + surrogateDiagTailX0RatChunk000Sub000Block111Part004
    + surrogateDiagTailX0RatChunk000Sub000Block111Part005
    + surrogateDiagTailX0RatChunk000Sub000Block111Part006
    + surrogateDiagTailX0RatChunk000Sub000Block111Part007
    + surrogateDiagTailX0RatChunk000Sub000Block111Part008
    + surrogateDiagTailX0RatChunk000Sub000Block111Part009
    + surrogateDiagTailX0RatChunk000Sub000Block111Part010
    + surrogateDiagTailX0RatChunk000Sub000Block111Part011
    + surrogateDiagTailX0RatChunk000Sub000Block111Part012
    + surrogateDiagTailX0RatChunk000Sub000Block111Part013
    + surrogateDiagTailX0RatChunk000Sub000Block111Part014
    + surrogateDiagTailX0RatChunk000Sub000Block111Part015
    + surrogateDiagTailX0RatChunk000Sub000Block111Part016
    + surrogateDiagTailX0RatChunk000Sub000Block111Part017
    + surrogateDiagTailX0RatChunk000Sub000Block111Part018
    + surrogateDiagTailX0RatChunk000Sub000Block111Part019
    + surrogateDiagTailX0RatChunk000Sub000Block111Part020
    + surrogateDiagTailX0RatChunk000Sub000Block111Part021
    + surrogateDiagTailX0RatChunk000Sub000Block111Part022
    + surrogateDiagTailX0RatChunk000Sub000Block111Part023
    + surrogateDiagTailX0RatChunk000Sub000Block111Part024

theorem surrogateDiagTailX0RatChunk000Sub000Block111_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk000Sub000Block111Head + surrogateDiagTailX0RatChunk000Sub000Block111Mid + surrogateDiagTailX0RatChunk000Sub000Block111Tail =
      surrogateDiagTailX0RatChunk000Sub000Block111 := by
  unfold surrogateDiagTailX0RatChunk000Sub000Block111Head surrogateDiagTailX0RatChunk000Sub000Block111Mid surrogateDiagTailX0RatChunk000Sub000Block111Tail surrogateDiagTailX0RatChunk000Sub000Block111
  ring

def SurrogateDiagonalTailChunk000Sub000Block111HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block111HeadSum X0 = surrogateDiagTailX0RatChunk000Sub000Block111Head

def SurrogateDiagonalTailChunk000Sub000Block111MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block111MidSum X0 = surrogateDiagTailX0RatChunk000Sub000Block111Mid

def SurrogateDiagonalTailChunk000Sub000Block111TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block111TailSum X0 = surrogateDiagTailX0RatChunk000Sub000Block111Tail

theorem surrogateDiagonalTailChunk000Sub000Block111_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk000Sub000Block111HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk000Sub000Block111MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk000Sub000Block111TailCertificateAt X0) :
    surrogateDiagonalTailChunk000Sub000Block111Sum X0 = surrogateDiagTailX0RatChunk000Sub000Block111 := by
  unfold SurrogateDiagonalTailChunk000Sub000Block111HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk000Sub000Block111MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk000Sub000Block111TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk000Sub000Block111Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk000Sub000Block111_eq_head_add_mid_add_tail

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

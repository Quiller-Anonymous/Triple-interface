import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0TailPilot25

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

open scoped BigOperators

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

/- Generated direct-term certificate blocks for tail chunk 000, subchunk 000, blocks [161,162). -/

/-- Block 161 covers tail-support indices [4025,4050) and q from 6671 to 6709. -/

def TailChunk000Sub000Block161Part000SupportExplicit : Finset ℕ :=
  ([6671] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block161Part000 : ℚ :=
  (133414112375 : ℚ) / 156577996805013504

def SurrogateDiagonalTailChunk000Sub000Block161Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6671
    = surrogateDiagTailX0RatChunk000Sub000Block161Part000

theorem surrogateDiagonalTailChunk000Sub000Block161Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block161Part000CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block161Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block161Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block161Part000CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block161Part000SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block161Part000] using hcert

def TailChunk000Sub000Block161Part001SupportExplicit : Finset ℕ :=
  ([6673] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block161Part001 : ℚ :=
  (695764515625 : ℚ) / 1238770966440517632

def SurrogateDiagonalTailChunk000Sub000Block161Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6673
    = surrogateDiagTailX0RatChunk000Sub000Block161Part001

theorem surrogateDiagonalTailChunk000Sub000Block161Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block161Part001CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block161Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block161Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block161Part001CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block161Part001SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block161Part001] using hcert

def TailChunk000Sub000Block161Part002SupportExplicit : Finset ℕ :=
  ([6674] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block161Part002 : ℚ :=
  (53246390581 : ℚ) / 10752521930371200

def SurrogateDiagonalTailChunk000Sub000Block161Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6674
    = surrogateDiagTailX0RatChunk000Sub000Block161Part002

theorem surrogateDiagonalTailChunk000Sub000Block161Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block161Part002CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block161Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block161Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block161Part002CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block161Part002SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block161Part002] using hcert

def TailChunk000Sub000Block161Part003SupportExplicit : Finset ℕ :=
  ([6677] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block161Part003 : ℚ :=
  (98378498851 : ℚ) / 134889252151939200

def SurrogateDiagonalTailChunk000Sub000Block161Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6677
    = surrogateDiagTailX0RatChunk000Sub000Block161Part003

theorem surrogateDiagonalTailChunk000Sub000Block161Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block161Part003CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block161Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block161Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block161Part003CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block161Part003SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block161Part003] using hcert

def TailChunk000Sub000Block161Part004SupportExplicit : Finset ℕ :=
  ([6679] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block161Part004 : ℚ :=
  (697016265625 : ℚ) / 1243232991521338482

def SurrogateDiagonalTailChunk000Sub000Block161Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6679
    = surrogateDiagTailX0RatChunk000Sub000Block161Part004

theorem surrogateDiagonalTailChunk000Sub000Block161Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block161Part004CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block161Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block161Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block161Part004CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block161Part004SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block161Part004] using hcert

def TailChunk000Sub000Block161Part005SupportExplicit : Finset ℕ :=
  ([6681] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block161Part005 : ℚ :=
  (28700056643 : ℚ) / 14977184405913600

def SurrogateDiagonalTailChunk000Sub000Block161Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6681
    = surrogateDiagTailX0RatChunk000Sub000Block161Part005

theorem surrogateDiagonalTailChunk000Sub000Block161Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block161Part005CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block161Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block161Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block161Part005CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block161Part005SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block161Part005] using hcert

def TailChunk000Sub000Block161Part006SupportExplicit : Finset ℕ :=
  ([6682] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block161Part006 : ℚ :=
  (1253224765075 : ℚ) / 222695634845564928

def SurrogateDiagonalTailChunk000Sub000Block161Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6682
    = surrogateDiagTailX0RatChunk000Sub000Block161Part006

theorem surrogateDiagonalTailChunk000Sub000Block161Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block161Part006CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block161Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block161Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block161Part006CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block161Part006SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block161Part006] using hcert

def TailChunk000Sub000Block161Part007SupportExplicit : Finset ℕ :=
  ([6683] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block161Part007 : ℚ :=
  (8955048647 : ℚ) / 14696219424153600

def SurrogateDiagonalTailChunk000Sub000Block161Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6683
    = surrogateDiagTailX0RatChunk000Sub000Block161Part007

theorem surrogateDiagonalTailChunk000Sub000Block161Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block161Part007CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block161Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block161Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block161Part007CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block161Part007SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block161Part007] using hcert

def TailChunk000Sub000Block161Part008SupportExplicit : Finset ℕ :=
  ([6685] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block161Part008 : ℚ :=
  (13888502129 : ℚ) / 8649205514403840

def SurrogateDiagonalTailChunk000Sub000Block161Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6685
    = surrogateDiagTailX0RatChunk000Sub000Block161Part008

theorem surrogateDiagonalTailChunk000Sub000Block161Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block161Part008CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block161Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block161Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block161Part008CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block161Part008SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block161Part008] using hcert

def TailChunk000Sub000Block161Part009SupportExplicit : Finset ℕ :=
  ([6686] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block161Part009 : ℚ :=
  (1396676733775 : ℚ) / 311926764961656648

def SurrogateDiagonalTailChunk000Sub000Block161Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6686
    = surrogateDiagTailX0RatChunk000Sub000Block161Part009

theorem surrogateDiagonalTailChunk000Sub000Block161Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block161Part009CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block161Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block161Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block161Part009CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block161Part009SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block161Part009] using hcert

def TailChunk000Sub000Block161Part010SupportExplicit : Finset ℕ :=
  ([6689] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block161Part010 : ℚ :=
  (699105015625 : ℚ) / 1250696473445793792

def SurrogateDiagonalTailChunk000Sub000Block161Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6689
    = surrogateDiagTailX0RatChunk000Sub000Block161Part010

theorem surrogateDiagonalTailChunk000Sub000Block161Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block161Part010CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block161Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block161Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block161Part010CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block161Part010SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block161Part010] using hcert

def TailChunk000Sub000Block161Part011SupportExplicit : Finset ℕ :=
  ([6690] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block161Part011 : ℚ :=
  (152816608175 : ℚ) / 8292346670186496

def SurrogateDiagonalTailChunk000Sub000Block161Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6690
    = surrogateDiagTailX0RatChunk000Sub000Block161Part011

theorem surrogateDiagonalTailChunk000Sub000Block161Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block161Part011CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block161Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block161Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block161Part011CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block161Part011SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block161Part011] using hcert

def TailChunk000Sub000Block161Part012SupportExplicit : Finset ℕ :=
  ([6691] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block161Part012 : ℚ :=
  (1119237025 : ℚ) / 2003509108907442

def SurrogateDiagonalTailChunk000Sub000Block161Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6691
    = surrogateDiagTailX0RatChunk000Sub000Block161Part012

theorem surrogateDiagonalTailChunk000Sub000Block161Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block161Part012CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block161Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block161Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block161Part012CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block161Part012SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block161Part012] using hcert

def TailChunk000Sub000Block161Part013SupportExplicit : Finset ℕ :=
  ([6693] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block161Part013 : ℚ :=
  (1464130628875 : ℚ) / 796017282659647488

def SurrogateDiagonalTailChunk000Sub000Block161Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6693
    = surrogateDiagTailX0RatChunk000Sub000Block161Part013

theorem surrogateDiagonalTailChunk000Sub000Block161Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block161Part013CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block161Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block161Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block161Part013CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block161Part013SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block161Part013] using hcert

def TailChunk000Sub000Block161Part014SupportExplicit : Finset ℕ :=
  ([6694] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block161Part014 : ℚ :=
  (175037640625 : ℚ) / 78355703477504082

def SurrogateDiagonalTailChunk000Sub000Block161Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6694
    = surrogateDiagTailX0RatChunk000Sub000Block161Part014

theorem surrogateDiagonalTailChunk000Sub000Block161Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block161Part014CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block161Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block161Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block161Part014CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block161Part014SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block161Part014] using hcert

def TailChunk000Sub000Block161Part015SupportExplicit : Finset ℕ :=
  ([6695] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block161Part015 : ℚ :=
  (106148734175 : ℚ) / 79821519404138496

def SurrogateDiagonalTailChunk000Sub000Block161Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6695
    = surrogateDiagTailX0RatChunk000Sub000Block161Part015

theorem surrogateDiagonalTailChunk000Sub000Block161Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block161Part015CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block161Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block161Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block161Part015CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block161Part015SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block161Part015] using hcert

def TailChunk000Sub000Block161Part016SupportExplicit : Finset ℕ :=
  ([6697] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block161Part016 : ℚ :=
  (3986275657 : ℚ) / 6531653077401600

def SurrogateDiagonalTailChunk000Sub000Block161Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6697
    = surrogateDiagTailX0RatChunk000Sub000Block161Part016

theorem surrogateDiagonalTailChunk000Sub000Block161Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block161Part016CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block161Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block161Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block161Part016CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block161Part016SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block161Part016] using hcert

def TailChunk000Sub000Block161Part017SupportExplicit : Finset ℕ :=
  ([6698] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block161Part017 : ℚ :=
  (677365210525 : ℚ) / 241841637590827008

def SurrogateDiagonalTailChunk000Sub000Block161Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6698
    = surrogateDiagTailX0RatChunk000Sub000Block161Part017

theorem surrogateDiagonalTailChunk000Sub000Block161Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block161Part017CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block161Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block161Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block161Part017CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block161Part017SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block161Part017] using hcert

def TailChunk000Sub000Block161Part018SupportExplicit : Finset ℕ :=
  ([6699] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block161Part018 : ℚ :=
  (26092319879 : ℚ) / 6374027958681600

def SurrogateDiagonalTailChunk000Sub000Block161Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6699
    = surrogateDiagTailX0RatChunk000Sub000Block161Part018

theorem surrogateDiagonalTailChunk000Sub000Block161Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block161Part018CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block161Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block161Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block161Part018CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block161Part018SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block161Part018] using hcert

def TailChunk000Sub000Block161Part019SupportExplicit : Finset ℕ :=
  ([6701] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block161Part019 : ℚ :=
  (44903401 : ℚ) / 80620604896800

def SurrogateDiagonalTailChunk000Sub000Block161Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6701
    = surrogateDiagTailX0RatChunk000Sub000Block161Part019

theorem surrogateDiagonalTailChunk000Sub000Block161Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block161Part019CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block161Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block161Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block161Part019CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block161Part019SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block161Part019] using hcert

def TailChunk000Sub000Block161Part020SupportExplicit : Finset ℕ :=
  ([6702] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block161Part020 : ℚ :=
  (623414911075 : ℚ) / 62058835202623488

def SurrogateDiagonalTailChunk000Sub000Block161Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6702
    = surrogateDiagTailX0RatChunk000Sub000Block161Part020

theorem surrogateDiagonalTailChunk000Sub000Block161Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block161Part020CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block161Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block161Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block161Part020CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block161Part020SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block161Part020] using hcert

def TailChunk000Sub000Block161Part021SupportExplicit : Finset ℕ :=
  ([6703] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block161Part021 : ℚ :=
  (702034515625 : ℚ) / 1261201740894206802

def SurrogateDiagonalTailChunk000Sub000Block161Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6703
    = surrogateDiagTailX0RatChunk000Sub000Block161Part021

theorem surrogateDiagonalTailChunk000Sub000Block161Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block161Part021CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block161Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block161Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block161Part021CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block161Part021SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block161Part021] using hcert

def TailChunk000Sub000Block161Part022SupportExplicit : Finset ℕ :=
  ([6706] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block161Part022 : ℚ :=
  (164712267625 : ℚ) / 42294457187357472

def SurrogateDiagonalTailChunk000Sub000Block161Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6706
    = surrogateDiagTailX0RatChunk000Sub000Block161Part022

theorem surrogateDiagonalTailChunk000Sub000Block161Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block161Part022CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block161Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block161Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block161Part022CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block161Part022SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block161Part022] using hcert

def TailChunk000Sub000Block161Part023SupportExplicit : Finset ℕ :=
  ([6707] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block161Part023 : ℚ :=
  (1307906380625 : ℚ) / 2014918746732232704

def SurrogateDiagonalTailChunk000Sub000Block161Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6707
    = surrogateDiagTailX0RatChunk000Sub000Block161Part023

theorem surrogateDiagonalTailChunk000Sub000Block161Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block161Part023CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block161Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block161Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block161Part023CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block161Part023SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block161Part023] using hcert

def TailChunk000Sub000Block161Part024SupportExplicit : Finset ℕ :=
  ([6709] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block161Part024 : ℚ :=
  (703291890625 : ℚ) / 1265724198899495712

def SurrogateDiagonalTailChunk000Sub000Block161Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6709
    = surrogateDiagTailX0RatChunk000Sub000Block161Part024

theorem surrogateDiagonalTailChunk000Sub000Block161Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block161Part024CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block161Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block161Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block161Part024CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block161Part024SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block161Part024] using hcert

def surrogateDiagonalTailChunk000Sub000Block161HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block161Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block161Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block161Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block161Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block161Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block161Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block161Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block161Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block161Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block161Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block161Head : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block161Part000
    + surrogateDiagTailX0RatChunk000Sub000Block161Part001
    + surrogateDiagTailX0RatChunk000Sub000Block161Part002
    + surrogateDiagTailX0RatChunk000Sub000Block161Part003
    + surrogateDiagTailX0RatChunk000Sub000Block161Part004
    + surrogateDiagTailX0RatChunk000Sub000Block161Part005
    + surrogateDiagTailX0RatChunk000Sub000Block161Part006
    + surrogateDiagTailX0RatChunk000Sub000Block161Part007
    + surrogateDiagTailX0RatChunk000Sub000Block161Part008
    + surrogateDiagTailX0RatChunk000Sub000Block161Part009

def surrogateDiagonalTailChunk000Sub000Block161MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block161Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block161Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block161Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block161Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block161Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block161Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block161Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block161Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block161Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block161Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block161Mid : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block161Part010
    + surrogateDiagTailX0RatChunk000Sub000Block161Part011
    + surrogateDiagTailX0RatChunk000Sub000Block161Part012
    + surrogateDiagTailX0RatChunk000Sub000Block161Part013
    + surrogateDiagTailX0RatChunk000Sub000Block161Part014
    + surrogateDiagTailX0RatChunk000Sub000Block161Part015
    + surrogateDiagTailX0RatChunk000Sub000Block161Part016
    + surrogateDiagTailX0RatChunk000Sub000Block161Part017
    + surrogateDiagTailX0RatChunk000Sub000Block161Part018
    + surrogateDiagTailX0RatChunk000Sub000Block161Part019

def surrogateDiagonalTailChunk000Sub000Block161TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block161Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block161Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block161Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block161Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block161Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block161Tail : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block161Part020
    + surrogateDiagTailX0RatChunk000Sub000Block161Part021
    + surrogateDiagTailX0RatChunk000Sub000Block161Part022
    + surrogateDiagTailX0RatChunk000Sub000Block161Part023
    + surrogateDiagTailX0RatChunk000Sub000Block161Part024

def surrogateDiagonalTailChunk000Sub000Block161Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub000Block161HeadSum X0
    + surrogateDiagonalTailChunk000Sub000Block161MidSum X0
    + surrogateDiagonalTailChunk000Sub000Block161TailSum X0

def surrogateDiagTailX0RatChunk000Sub000Block161 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block161Part000
    + surrogateDiagTailX0RatChunk000Sub000Block161Part001
    + surrogateDiagTailX0RatChunk000Sub000Block161Part002
    + surrogateDiagTailX0RatChunk000Sub000Block161Part003
    + surrogateDiagTailX0RatChunk000Sub000Block161Part004
    + surrogateDiagTailX0RatChunk000Sub000Block161Part005
    + surrogateDiagTailX0RatChunk000Sub000Block161Part006
    + surrogateDiagTailX0RatChunk000Sub000Block161Part007
    + surrogateDiagTailX0RatChunk000Sub000Block161Part008
    + surrogateDiagTailX0RatChunk000Sub000Block161Part009
    + surrogateDiagTailX0RatChunk000Sub000Block161Part010
    + surrogateDiagTailX0RatChunk000Sub000Block161Part011
    + surrogateDiagTailX0RatChunk000Sub000Block161Part012
    + surrogateDiagTailX0RatChunk000Sub000Block161Part013
    + surrogateDiagTailX0RatChunk000Sub000Block161Part014
    + surrogateDiagTailX0RatChunk000Sub000Block161Part015
    + surrogateDiagTailX0RatChunk000Sub000Block161Part016
    + surrogateDiagTailX0RatChunk000Sub000Block161Part017
    + surrogateDiagTailX0RatChunk000Sub000Block161Part018
    + surrogateDiagTailX0RatChunk000Sub000Block161Part019
    + surrogateDiagTailX0RatChunk000Sub000Block161Part020
    + surrogateDiagTailX0RatChunk000Sub000Block161Part021
    + surrogateDiagTailX0RatChunk000Sub000Block161Part022
    + surrogateDiagTailX0RatChunk000Sub000Block161Part023
    + surrogateDiagTailX0RatChunk000Sub000Block161Part024

theorem surrogateDiagTailX0RatChunk000Sub000Block161_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk000Sub000Block161Head + surrogateDiagTailX0RatChunk000Sub000Block161Mid + surrogateDiagTailX0RatChunk000Sub000Block161Tail =
      surrogateDiagTailX0RatChunk000Sub000Block161 := by
  unfold surrogateDiagTailX0RatChunk000Sub000Block161Head surrogateDiagTailX0RatChunk000Sub000Block161Mid surrogateDiagTailX0RatChunk000Sub000Block161Tail surrogateDiagTailX0RatChunk000Sub000Block161
  ring

def SurrogateDiagonalTailChunk000Sub000Block161HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block161HeadSum X0 = surrogateDiagTailX0RatChunk000Sub000Block161Head

def SurrogateDiagonalTailChunk000Sub000Block161MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block161MidSum X0 = surrogateDiagTailX0RatChunk000Sub000Block161Mid

def SurrogateDiagonalTailChunk000Sub000Block161TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block161TailSum X0 = surrogateDiagTailX0RatChunk000Sub000Block161Tail

theorem surrogateDiagonalTailChunk000Sub000Block161_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk000Sub000Block161HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk000Sub000Block161MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk000Sub000Block161TailCertificateAt X0) :
    surrogateDiagonalTailChunk000Sub000Block161Sum X0 = surrogateDiagTailX0RatChunk000Sub000Block161 := by
  unfold SurrogateDiagonalTailChunk000Sub000Block161HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk000Sub000Block161MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk000Sub000Block161TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk000Sub000Block161Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk000Sub000Block161_eq_head_add_mid_add_tail

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

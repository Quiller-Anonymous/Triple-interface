import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0TailPilot25

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

open scoped BigOperators

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

/- Generated direct-term certificate blocks for tail chunk 000, subchunk 000, blocks [109,110). -/

/- Block 109 covers tail-support indices [2725,2750) and q from 4533 to 4571. -/

def TailChunk000Sub000Block109Part000SupportExplicit : Finset ℕ :=
  ([4533] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block109Part000 : ℚ :=
  (39933581287 : ℚ) / 8319833249923200

def SurrogateDiagonalTailChunk000Sub000Block109Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4533
    = surrogateDiagTailX0RatChunk000Sub000Block109Part000

theorem surrogateDiagonalTailChunk000Sub000Block109Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block109Part000CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block109Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block109Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block109Part000CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block109Part000SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block109Part000] using hcert

def TailChunk000Sub000Block109Part001SupportExplicit : Finset ℕ :=
  ([4534] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block109Part001 : ℚ :=
  (642282642775 : ℚ) / 65927480808429768

def SurrogateDiagonalTailChunk000Sub000Block109Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4534
    = surrogateDiagTailX0RatChunk000Sub000Block109Part001

theorem surrogateDiagonalTailChunk000Sub000Block109Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block109Part001CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block109Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block109Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block109Part001CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block109Part001SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block109Part001] using hcert

def TailChunk000Sub000Block109Part002SupportExplicit : Finset ℕ :=
  ([4535] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block109Part002 : ℚ :=
  (513750104375 : ℚ) / 215650077838009344

def SurrogateDiagonalTailChunk000Sub000Block109Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4535
    = surrogateDiagTailX0RatChunk000Sub000Block109Part002

theorem surrogateDiagonalTailChunk000Sub000Block109Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block109Part002CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block109Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block109Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block109Part002CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block109Part002SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block109Part002] using hcert

def TailChunk000Sub000Block109Part003SupportExplicit : Finset ℕ :=
  ([4537] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block109Part003 : ℚ :=
  (1192313545225 : ℚ) / 760446768763404288

def SurrogateDiagonalTailChunk000Sub000Block109Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4537
    = surrogateDiagTailX0RatChunk000Sub000Block109Part003

theorem surrogateDiagonalTailChunk000Sub000Block109Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block109Part003CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block109Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block109Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block109Part003CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block109Part003SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block109Part003] using hcert

def TailChunk000Sub000Block109Part004SupportExplicit : Finset ℕ :=
  ([4538] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block109Part004 : ℚ :=
  (643416415975 : ℚ) / 66160542820111488

def SurrogateDiagonalTailChunk000Sub000Block109Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4538
    = surrogateDiagTailX0RatChunk000Sub000Block109Part004

theorem surrogateDiagonalTailChunk000Sub000Block109Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block109Part004CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block109Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block109Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block109Part004CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block109Part004SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block109Part004] using hcert

def TailChunk000Sub000Block109Part005SupportExplicit : Finset ℕ :=
  ([4539] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block109Part005 : ℚ :=
  (161117925 : ℚ) / 31441308090368

def SurrogateDiagonalTailChunk000Sub000Block109Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4539
    = surrogateDiagTailX0RatChunk000Sub000Block109Part005

theorem surrogateDiagonalTailChunk000Sub000Block109Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block109Part005CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block109Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block109Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block109Part005CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block109Part005SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block109Part005] using hcert

def TailChunk000Sub000Block109Part006SupportExplicit : Finset ℕ :=
  ([4541] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block109Part006 : ℚ :=
  (1220149478425 : ℚ) / 842218365626967168

def SurrogateDiagonalTailChunk000Sub000Block109Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4541
    = surrogateDiagTailX0RatChunk000Sub000Block109Part006

theorem surrogateDiagonalTailChunk000Sub000Block109Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block109Part006CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block109Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block109Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block109Part006CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block109Part006SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block109Part006] using hcert

def TailChunk000Sub000Block109Part007SupportExplicit : Finset ℕ :=
  ([4542] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block109Part007 : ℚ :=
  (232541574425 : ℚ) / 6534374599517184

def SurrogateDiagonalTailChunk000Sub000Block109Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4542
    = surrogateDiagTailX0RatChunk000Sub000Block109Part007

theorem surrogateDiagonalTailChunk000Sub000Block109Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block109Part007CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block109Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block109Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block109Part007CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block109Part007SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block109Part007] using hcert

def TailChunk000Sub000Block109Part008SupportExplicit : Finset ℕ :=
  ([4543] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block109Part008 : ℚ :=
  (40795149109 : ℚ) / 14669112051763200

def SurrogateDiagonalTailChunk000Sub000Block109Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4543
    = surrogateDiagTailX0RatChunk000Sub000Block109Part008

theorem surrogateDiagonalTailChunk000Sub000Block109Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block109Part008CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block109Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block109Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block109Part008CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block109Part008SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block109Part008] using hcert

def TailChunk000Sub000Block109Part009SupportExplicit : Finset ℕ :=
  ([4546] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block109Part009 : ℚ :=
  (322778899275 : ℚ) / 22209506693349376

def SurrogateDiagonalTailChunk000Sub000Block109Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4546
    = surrogateDiagTailX0RatChunk000Sub000Block109Part009

theorem surrogateDiagonalTailChunk000Sub000Block109Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block109Part009CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block109Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block109Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block109Part009CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block109Part009SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block109Part009] using hcert

def TailChunk000Sub000Block109Part010SupportExplicit : Finset ℕ :=
  ([4547] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block109Part010 : ℚ :=
  (2583884244775 : ℚ) / 1067934420488902728

def SurrogateDiagonalTailChunk000Sub000Block109Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4547
    = surrogateDiagTailX0RatChunk000Sub000Block109Part010

theorem surrogateDiagonalTailChunk000Sub000Block109Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block109Part010CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block109Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block109Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block109Part010CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block109Part010SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block109Part010] using hcert

def TailChunk000Sub000Block109Part011SupportExplicit : Finset ℕ :=
  ([4549] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block109Part011 : ℚ :=
  (2586157789975 : ℚ) / 1069815000127022208

def SurrogateDiagonalTailChunk000Sub000Block109Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4549
    = surrogateDiagTailX0RatChunk000Sub000Block109Part011

theorem surrogateDiagonalTailChunk000Sub000Block109Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block109Part011CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block109Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block109Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block109Part011CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block109Part011SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block109Part011] using hcert

def TailChunk000Sub000Block109Part012SupportExplicit : Finset ℕ :=
  ([4551] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block109Part012 : ℚ :=
  (16466841029 : ℚ) / 3440541538713600

def SurrogateDiagonalTailChunk000Sub000Block109Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4551
    = surrogateDiagTailX0RatChunk000Sub000Block109Part012

theorem surrogateDiagonalTailChunk000Sub000Block109Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block109Part012CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block109Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block109Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block109Part012CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block109Part012SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block109Part012] using hcert

def TailChunk000Sub000Block109Part013SupportExplicit : Finset ℕ :=
  ([4553] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block109Part013 : ℚ :=
  (1248540911725 : ℚ) / 910243062639525888

def SurrogateDiagonalTailChunk000Sub000Block109Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4553
    = surrogateDiagTailX0RatChunk000Sub000Block109Part013

theorem surrogateDiagonalTailChunk000Sub000Block109Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block109Part013CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block109Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block109Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block109Part013CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block109Part013SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block109Part013] using hcert

def TailChunk000Sub000Block109Part014SupportExplicit : Finset ℕ :=
  ([4555] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block109Part014 : ℚ :=
  (2902234929 : ℚ) / 1170580070266880

def SurrogateDiagonalTailChunk000Sub000Block109Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4555
    = surrogateDiagTailX0RatChunk000Sub000Block109Part014

theorem surrogateDiagonalTailChunk000Sub000Block109Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block109Part014CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block109Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block109Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block109Part014CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block109Part014SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block109Part014] using hcert

def TailChunk000Sub000Block109Part015SupportExplicit : Finset ℕ :=
  ([4558] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block109Part015 : ℚ :=
  (7716653825 : ℚ) / 702348042160128

def SurrogateDiagonalTailChunk000Sub000Block109Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4558
    = surrogateDiagTailX0RatChunk000Sub000Block109Part015

theorem surrogateDiagonalTailChunk000Sub000Block109Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block109Part015CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block109Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block109Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block109Part015CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block109Part015SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block109Part015] using hcert

def TailChunk000Sub000Block109Part016SupportExplicit : Finset ℕ :=
  ([4559] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block109Part016 : ℚ :=
  (631315380875 : ℚ) / 475459054190198784

def SurrogateDiagonalTailChunk000Sub000Block109Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4559
    = surrogateDiagTailX0RatChunk000Sub000Block109Part016

theorem surrogateDiagonalTailChunk000Sub000Block109Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block109Part016CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block109Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block109Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block109Part016CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block109Part016SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block109Part016] using hcert

def TailChunk000Sub000Block109Part017SupportExplicit : Finset ℕ :=
  ([4561] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block109Part017 : ℚ :=
  (520068025 : ℚ) / 432460275720192

def SurrogateDiagonalTailChunk000Sub000Block109Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4561
    = surrogateDiagTailX0RatChunk000Sub000Block109Part017

theorem surrogateDiagonalTailChunk000Sub000Block109Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block109Part017CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block109Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block109Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block109Part017CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block109Part017SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block109Part017] using hcert

def TailChunk000Sub000Block109Part018SupportExplicit : Finset ℕ :=
  ([4562] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block109Part018 : ℚ :=
  (26009602039 : ℚ) / 2702876723251200

def SurrogateDiagonalTailChunk000Sub000Block109Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4562
    = surrogateDiagTailX0RatChunk000Sub000Block109Part018

theorem surrogateDiagonalTailChunk000Sub000Block109Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block109Part018CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block109Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block109Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block109Part018CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block109Part018SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block109Part018] using hcert

def TailChunk000Sub000Block109Part019SupportExplicit : Finset ℕ :=
  ([4565] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block109Part019 : ℚ :=
  (1645190199 : ℚ) / 482359663308800

def SurrogateDiagonalTailChunk000Sub000Block109Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4565
    = surrogateDiagTailX0RatChunk000Sub000Block109Part019

theorem surrogateDiagonalTailChunk000Sub000Block109Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block109Part019CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block109Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block109Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block109Part019CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block109Part019SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block109Part019] using hcert

def TailChunk000Sub000Block109Part020SupportExplicit : Finset ℕ :=
  ([4566] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block109Part020 : ℚ :=
  (694119 : ℚ) / 21351792640

def SurrogateDiagonalTailChunk000Sub000Block109Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4566
    = surrogateDiagTailX0RatChunk000Sub000Block109Part020

theorem surrogateDiagonalTailChunk000Sub000Block109Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block109Part020CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block109Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block109Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block109Part020CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block109Part020SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block109Part020] using hcert

def TailChunk000Sub000Block109Part021SupportExplicit : Finset ℕ :=
  ([4567] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block109Part021 : ℚ :=
  (325898265625 : ℚ) / 271713049182697842

def SurrogateDiagonalTailChunk000Sub000Block109Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4567
    = surrogateDiagTailX0RatChunk000Sub000Block109Part021

theorem surrogateDiagonalTailChunk000Sub000Block109Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block109Part021CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block109Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block109Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block109Part021CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block109Part021SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block109Part021] using hcert

def TailChunk000Sub000Block109Part022SupportExplicit : Finset ℕ :=
  ([4569] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block109Part022 : ℚ :=
  (86930625 : ℚ) / 21464392489024

def SurrogateDiagonalTailChunk000Sub000Block109Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4569
    = surrogateDiagTailX0RatChunk000Sub000Block109Part022

theorem surrogateDiagonalTailChunk000Sub000Block109Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block109Part022CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block109Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block109Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block109Part022CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block109Part022SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block109Part022] using hcert

def TailChunk000Sub000Block109Part023SupportExplicit : Finset ℕ :=
  ([4570] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block109Part023 : ℚ :=
  (60760643125 : ℚ) / 2306454803841024

def SurrogateDiagonalTailChunk000Sub000Block109Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4570
    = surrogateDiagTailX0RatChunk000Sub000Block109Part023

theorem surrogateDiagonalTailChunk000Sub000Block109Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block109Part023CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block109Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block109Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block109Part023CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block109Part023SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block109Part023] using hcert

def TailChunk000Sub000Block109Part024SupportExplicit : Finset ℕ :=
  ([4571] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block109Part024 : ℚ :=
  (286140584125 : ℚ) / 146407138333512192

def SurrogateDiagonalTailChunk000Sub000Block109Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4571
    = surrogateDiagTailX0RatChunk000Sub000Block109Part024

theorem surrogateDiagonalTailChunk000Sub000Block109Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block109Part024CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block109Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block109Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block109Part024CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block109Part024SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block109Part024] using hcert

def surrogateDiagonalTailChunk000Sub000Block109HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block109Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block109Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block109Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block109Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block109Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block109Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block109Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block109Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block109Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block109Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block109Head : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block109Part000
    + surrogateDiagTailX0RatChunk000Sub000Block109Part001
    + surrogateDiagTailX0RatChunk000Sub000Block109Part002
    + surrogateDiagTailX0RatChunk000Sub000Block109Part003
    + surrogateDiagTailX0RatChunk000Sub000Block109Part004
    + surrogateDiagTailX0RatChunk000Sub000Block109Part005
    + surrogateDiagTailX0RatChunk000Sub000Block109Part006
    + surrogateDiagTailX0RatChunk000Sub000Block109Part007
    + surrogateDiagTailX0RatChunk000Sub000Block109Part008
    + surrogateDiagTailX0RatChunk000Sub000Block109Part009

def surrogateDiagonalTailChunk000Sub000Block109MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block109Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block109Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block109Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block109Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block109Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block109Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block109Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block109Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block109Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block109Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block109Mid : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block109Part010
    + surrogateDiagTailX0RatChunk000Sub000Block109Part011
    + surrogateDiagTailX0RatChunk000Sub000Block109Part012
    + surrogateDiagTailX0RatChunk000Sub000Block109Part013
    + surrogateDiagTailX0RatChunk000Sub000Block109Part014
    + surrogateDiagTailX0RatChunk000Sub000Block109Part015
    + surrogateDiagTailX0RatChunk000Sub000Block109Part016
    + surrogateDiagTailX0RatChunk000Sub000Block109Part017
    + surrogateDiagTailX0RatChunk000Sub000Block109Part018
    + surrogateDiagTailX0RatChunk000Sub000Block109Part019

def surrogateDiagonalTailChunk000Sub000Block109TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block109Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block109Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block109Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block109Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block109Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block109Tail : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block109Part020
    + surrogateDiagTailX0RatChunk000Sub000Block109Part021
    + surrogateDiagTailX0RatChunk000Sub000Block109Part022
    + surrogateDiagTailX0RatChunk000Sub000Block109Part023
    + surrogateDiagTailX0RatChunk000Sub000Block109Part024

def surrogateDiagonalTailChunk000Sub000Block109Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub000Block109HeadSum X0
    + surrogateDiagonalTailChunk000Sub000Block109MidSum X0
    + surrogateDiagonalTailChunk000Sub000Block109TailSum X0

def surrogateDiagTailX0RatChunk000Sub000Block109 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block109Part000
    + surrogateDiagTailX0RatChunk000Sub000Block109Part001
    + surrogateDiagTailX0RatChunk000Sub000Block109Part002
    + surrogateDiagTailX0RatChunk000Sub000Block109Part003
    + surrogateDiagTailX0RatChunk000Sub000Block109Part004
    + surrogateDiagTailX0RatChunk000Sub000Block109Part005
    + surrogateDiagTailX0RatChunk000Sub000Block109Part006
    + surrogateDiagTailX0RatChunk000Sub000Block109Part007
    + surrogateDiagTailX0RatChunk000Sub000Block109Part008
    + surrogateDiagTailX0RatChunk000Sub000Block109Part009
    + surrogateDiagTailX0RatChunk000Sub000Block109Part010
    + surrogateDiagTailX0RatChunk000Sub000Block109Part011
    + surrogateDiagTailX0RatChunk000Sub000Block109Part012
    + surrogateDiagTailX0RatChunk000Sub000Block109Part013
    + surrogateDiagTailX0RatChunk000Sub000Block109Part014
    + surrogateDiagTailX0RatChunk000Sub000Block109Part015
    + surrogateDiagTailX0RatChunk000Sub000Block109Part016
    + surrogateDiagTailX0RatChunk000Sub000Block109Part017
    + surrogateDiagTailX0RatChunk000Sub000Block109Part018
    + surrogateDiagTailX0RatChunk000Sub000Block109Part019
    + surrogateDiagTailX0RatChunk000Sub000Block109Part020
    + surrogateDiagTailX0RatChunk000Sub000Block109Part021
    + surrogateDiagTailX0RatChunk000Sub000Block109Part022
    + surrogateDiagTailX0RatChunk000Sub000Block109Part023
    + surrogateDiagTailX0RatChunk000Sub000Block109Part024

theorem surrogateDiagTailX0RatChunk000Sub000Block109_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk000Sub000Block109Head + surrogateDiagTailX0RatChunk000Sub000Block109Mid + surrogateDiagTailX0RatChunk000Sub000Block109Tail =
      surrogateDiagTailX0RatChunk000Sub000Block109 := by
  unfold surrogateDiagTailX0RatChunk000Sub000Block109Head surrogateDiagTailX0RatChunk000Sub000Block109Mid surrogateDiagTailX0RatChunk000Sub000Block109Tail surrogateDiagTailX0RatChunk000Sub000Block109
  ring

def SurrogateDiagonalTailChunk000Sub000Block109HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block109HeadSum X0 = surrogateDiagTailX0RatChunk000Sub000Block109Head

def SurrogateDiagonalTailChunk000Sub000Block109MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block109MidSum X0 = surrogateDiagTailX0RatChunk000Sub000Block109Mid

def SurrogateDiagonalTailChunk000Sub000Block109TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block109TailSum X0 = surrogateDiagTailX0RatChunk000Sub000Block109Tail

theorem surrogateDiagonalTailChunk000Sub000Block109_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk000Sub000Block109HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk000Sub000Block109MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk000Sub000Block109TailCertificateAt X0) :
    surrogateDiagonalTailChunk000Sub000Block109Sum X0 = surrogateDiagTailX0RatChunk000Sub000Block109 := by
  unfold SurrogateDiagonalTailChunk000Sub000Block109HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk000Sub000Block109MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk000Sub000Block109TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk000Sub000Block109Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk000Sub000Block109_eq_head_add_mid_add_tail

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

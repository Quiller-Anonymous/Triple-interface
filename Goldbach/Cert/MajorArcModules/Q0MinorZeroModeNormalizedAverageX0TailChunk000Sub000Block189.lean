import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0TailPilot25

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

open scoped BigOperators

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

/- Generated direct-term certificate blocks for tail chunk 000, subchunk 000, blocks [189,190). -/

/-- Block 189 covers tail-support indices [4725,4750) and q from 7818 to 7858. -/

def TailChunk000Sub000Block189Part000SupportExplicit : Finset ℕ :=
  ([7818] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block189Part000 : ℚ :=
  (530127067475 : ℚ) / 57485826898726464

def SurrogateDiagonalTailChunk000Sub000Block189Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7818
    = surrogateDiagTailX0RatChunk000Sub000Block189Part000

theorem surrogateDiagonalTailChunk000Sub000Block189Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block189Part000CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block189Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block189Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block189Part000CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block189Part000SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block189Part000] using hcert

def TailChunk000Sub000Block189Part001SupportExplicit : Finset ℕ :=
  ([7819] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block189Part001 : ℚ :=
  (3116072487775 : ℚ) / 5026765651412502528

def SurrogateDiagonalTailChunk000Sub000Block189Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7819
    = surrogateDiagTailX0RatChunk000Sub000Block189Part001

theorem surrogateDiagonalTailChunk000Sub000Block189Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block189Part001CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block189Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block189Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block189Part001CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block189Part001SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block189Part001] using hcert

def TailChunk000Sub000Block189Part002SupportExplicit : Finset ℕ :=
  ([7822] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block189Part002 : ℚ :=
  (76464309079 : ℚ) / 23377274681032200

def SurrogateDiagonalTailChunk000Sub000Block189Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7822
    = surrogateDiagTailX0RatChunk000Sub000Block189Part002

theorem surrogateDiagonalTailChunk000Sub000Block189Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block189Part002CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block189Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block189Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block189Part002CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block189Part002SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block189Part002] using hcert

def TailChunk000Sub000Block189Part003SupportExplicit : Finset ℕ :=
  ([7823] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block189Part003 : ℚ :=
  (956239515625 : ℚ) / 2340119922780886482

def SurrogateDiagonalTailChunk000Sub000Block189Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7823
    = surrogateDiagTailX0RatChunk000Sub000Block189Part003

theorem surrogateDiagonalTailChunk000Sub000Block189Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block189Part003CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block189Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block189Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block189Part003CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block189Part003SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block189Part003] using hcert

def TailChunk000Sub000Block189Part004SupportExplicit : Finset ℕ :=
  ([7826] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block189Part004 : ℚ :=
  (1342060542925 : ℚ) / 209099987184549888

def SurrogateDiagonalTailChunk000Sub000Block189Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7826
    = surrogateDiagTailX0RatChunk000Sub000Block189Part004

theorem surrogateDiagonalTailChunk000Sub000Block189Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block189Part004CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block189Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block189Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block189Part004CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block189Part004SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block189Part004] using hcert

def TailChunk000Sub000Block189Part005SupportExplicit : Finset ℕ :=
  ([7827] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block189Part005 : ℚ :=
  (1063242477725 : ℚ) / 925437713910595584

def SurrogateDiagonalTailChunk000Sub000Block189Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7827
    = surrogateDiagTailX0RatChunk000Sub000Block189Part005

theorem surrogateDiagonalTailChunk000Sub000Block189Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block189Part005CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block189Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block189Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block189Part005CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block189Part005SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block189Part005] using hcert

def TailChunk000Sub000Block189Part006SupportExplicit : Finset ℕ :=
  ([7829] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block189Part006 : ℚ :=
  (957706890625 : ℚ) / 2347308305835769632

def SurrogateDiagonalTailChunk000Sub000Block189Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7829
    = surrogateDiagTailX0RatChunk000Sub000Block189Part006

theorem surrogateDiagonalTailChunk000Sub000Block189Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block189Part006CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block189Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block189Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block189Part006CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block189Part006SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block189Part006] using hcert

def TailChunk000Sub000Block189Part007SupportExplicit : Finset ℕ :=
  ([7831] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block189Part007 : ℚ :=
  (147177714229 : ℚ) / 333688484352000000

def SurrogateDiagonalTailChunk000Sub000Block189Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7831
    = surrogateDiagTailX0RatChunk000Sub000Block189Part007

theorem surrogateDiagonalTailChunk000Sub000Block189Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block189Part007CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block189Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block189Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block189Part007CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block189Part007SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block189Part007] using hcert

def TailChunk000Sub000Block189Part008SupportExplicit : Finset ℕ :=
  ([7833] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block189Part008 : ℚ :=
  (1759791606325 : ℚ) / 992941363241975808

def SurrogateDiagonalTailChunk000Sub000Block189Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7833
    = surrogateDiagTailX0RatChunk000Sub000Block189Part008

theorem surrogateDiagonalTailChunk000Sub000Block189Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block189Part008CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block189Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block189Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block189Part008CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block189Part008SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block189Part008] using hcert

def TailChunk000Sub000Block189Part009SupportExplicit : Finset ℕ :=
  ([7834] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block189Part009 : ℚ :=
  (239732640625 : ℚ) / 147006859569775392

def SurrogateDiagonalTailChunk000Sub000Block189Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7834
    = surrogateDiagTailX0RatChunk000Sub000Block189Part009

theorem surrogateDiagonalTailChunk000Sub000Block189Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block189Part009CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block189Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block189Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block189Part009CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block189Part009SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block189Part009] using hcert

def TailChunk000Sub000Block189Part010SupportExplicit : Finset ℕ :=
  ([7835] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block189Part010 : ℚ :=
  (2760579943825 : ℚ) / 3849761766864734208

def SurrogateDiagonalTailChunk000Sub000Block189Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7835
    = surrogateDiagTailX0RatChunk000Sub000Block189Part010

theorem surrogateDiagonalTailChunk000Sub000Block189Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block189Part010CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block189Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block189Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block189Part010CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block189Part010SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block189Part010] using hcert

def TailChunk000Sub000Block189Part011SupportExplicit : Finset ℕ :=
  ([7837] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block189Part011 : ℚ :=
  (2936200239 : ℚ) / 6114442569318400

def SurrogateDiagonalTailChunk000Sub000Block189Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7837
    = surrogateDiagTailX0RatChunk000Sub000Block189Part011

theorem surrogateDiagonalTailChunk000Sub000Block189Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block189Part011CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block189Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block189Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block189Part011CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block189Part011SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block189Part011] using hcert

def TailChunk000Sub000Block189Part012SupportExplicit : Finset ℕ :=
  ([7838] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block189Part012 : ℚ :=
  (239977515625 : ℚ) / 147307410168525522

def SurrogateDiagonalTailChunk000Sub000Block189Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7838
    = surrogateDiagTailX0RatChunk000Sub000Block189Part012

theorem surrogateDiagonalTailChunk000Sub000Block189Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block189Part012CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block189Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block189Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block189Part012CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block189Part012SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block189Part012] using hcert

def TailChunk000Sub000Block189Part013SupportExplicit : Finset ℕ :=
  ([7841] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block189Part013 : ℚ :=
  (1537032025 : ℚ) / 3778775587356672

def SurrogateDiagonalTailChunk000Sub000Block189Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7841
    = surrogateDiagTailX0RatChunk000Sub000Block189Part013

theorem surrogateDiagonalTailChunk000Sub000Block189Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block189Part013CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block189Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block189Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block189Part013CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block189Part013SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block189Part013] using hcert

def TailChunk000Sub000Block189Part014SupportExplicit : Finset ℕ :=
  ([7842] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block189Part014 : ℚ :=
  (746968452475 : ℚ) / 116391040133155968

def SurrogateDiagonalTailChunk000Sub000Block189Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7842
    = surrogateDiagTailX0RatChunk000Sub000Block189Part014

theorem surrogateDiagonalTailChunk000Sub000Block189Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block189Part014CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block189Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block189Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block189Part014CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block189Part014SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block189Part014] using hcert

def TailChunk000Sub000Block189Part015SupportExplicit : Finset ℕ :=
  ([7843] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block189Part015 : ℚ :=
  (30335533117 : ℚ) / 47446327368000000

def SurrogateDiagonalTailChunk000Sub000Block189Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7843
    = surrogateDiagTailX0RatChunk000Sub000Block189Part015

theorem surrogateDiagonalTailChunk000Sub000Block189Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block189Part015CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block189Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block189Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block189Part015CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block189Part015SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block189Part015] using hcert

def TailChunk000Sub000Block189Part016SupportExplicit : Finset ℕ :=
  ([7845] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block189Part016 : ℚ :=
  (1377203725 : ℚ) / 660110042329344

def SurrogateDiagonalTailChunk000Sub000Block189Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7845
    = surrogateDiagTailX0RatChunk000Sub000Block189Part016

theorem surrogateDiagonalTailChunk000Sub000Block189Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block189Part016CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block189Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block189Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block189Part016CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block189Part016SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block189Part016] using hcert

def TailChunk000Sub000Block189Part017SupportExplicit : Finset ℕ :=
  ([7846] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block189Part017 : ℚ :=
  (240467640625 : ℚ) / 147909893677932882

def SurrogateDiagonalTailChunk000Sub000Block189Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7846
    = surrogateDiagTailX0RatChunk000Sub000Block189Part017

theorem surrogateDiagonalTailChunk000Sub000Block189Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block189Part017CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block189Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block189Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block189Part017CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block189Part017SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block189Part017] using hcert

def TailChunk000Sub000Block189Part018SupportExplicit : Finset ℕ :=
  ([7847] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block189Part018 : ℚ :=
  (929202646775 : ℚ) / 1283253922288244736

def SurrogateDiagonalTailChunk000Sub000Block189Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7847
    = surrogateDiagTailX0RatChunk000Sub000Block189Part018

theorem surrogateDiagonalTailChunk000Sub000Block189Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block189Part018CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block189Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block189Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block189Part018CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block189Part018SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block189Part018] using hcert

def TailChunk000Sub000Block189Part019SupportExplicit : Finset ℕ :=
  ([7849] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block189Part019 : ℚ :=
  (3707321393575 : ℚ) / 8501401704807931008

def SurrogateDiagonalTailChunk000Sub000Block189Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7849
    = surrogateDiagTailX0RatChunk000Sub000Block189Part019

theorem surrogateDiagonalTailChunk000Sub000Block189Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block189Part019CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block189Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block189Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block189Part019CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block189Part019SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block189Part019] using hcert

def TailChunk000Sub000Block189Part020SupportExplicit : Finset ℕ :=
  ([7851] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block189Part020 : ℚ :=
  (1711488738325 : ℚ) / 1873690264077631488

def SurrogateDiagonalTailChunk000Sub000Block189Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7851
    = surrogateDiagTailX0RatChunk000Sub000Block189Part020

theorem surrogateDiagonalTailChunk000Sub000Block189Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block189Part020CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block189Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block189Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block189Part020CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block189Part020SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block189Part020] using hcert

def TailChunk000Sub000Block189Part021SupportExplicit : Finset ℕ :=
  ([7853] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block189Part021 : ℚ :=
  (963587640625 : ℚ) / 2376227574510565152

def SurrogateDiagonalTailChunk000Sub000Block189Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7853
    = surrogateDiagTailX0RatChunk000Sub000Block189Part021

theorem surrogateDiagonalTailChunk000Sub000Block189Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block189Part021CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block189Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block189Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block189Part021CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block189Part021SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block189Part021] using hcert

def TailChunk000Sub000Block189Part022SupportExplicit : Finset ℕ :=
  ([7854] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block189Part022 : ℚ :=
  (11316766589 : ℚ) / 679613143449600

def SurrogateDiagonalTailChunk000Sub000Block189Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7854
    = surrogateDiagTailX0RatChunk000Sub000Block189Part022

theorem surrogateDiagonalTailChunk000Sub000Block189Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block189Part022CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block189Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block189Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block189Part022CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block189Part022SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block189Part022] using hcert

def TailChunk000Sub000Block189Part023SupportExplicit : Finset ℕ :=
  ([7855] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block189Part023 : ℚ :=
  (36995921859 : ℚ) / 51856615734630400

def SurrogateDiagonalTailChunk000Sub000Block189Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7855
    = surrogateDiagTailX0RatChunk000Sub000Block189Part023

theorem surrogateDiagonalTailChunk000Sub000Block189Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block189Part023CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block189Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block189Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block189Part023CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block189Part023SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block189Part023] using hcert

def TailChunk000Sub000Block189Part024SupportExplicit : Finset ℕ :=
  ([7858] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block189Part024 : ℚ :=
  (241203765625 : ℚ) / 148817081781023232

def SurrogateDiagonalTailChunk000Sub000Block189Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7858
    = surrogateDiagTailX0RatChunk000Sub000Block189Part024

theorem surrogateDiagonalTailChunk000Sub000Block189Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block189Part024CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block189Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block189Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block189Part024CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block189Part024SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block189Part024] using hcert

def surrogateDiagonalTailChunk000Sub000Block189HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block189Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block189Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block189Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block189Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block189Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block189Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block189Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block189Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block189Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block189Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block189Head : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block189Part000
    + surrogateDiagTailX0RatChunk000Sub000Block189Part001
    + surrogateDiagTailX0RatChunk000Sub000Block189Part002
    + surrogateDiagTailX0RatChunk000Sub000Block189Part003
    + surrogateDiagTailX0RatChunk000Sub000Block189Part004
    + surrogateDiagTailX0RatChunk000Sub000Block189Part005
    + surrogateDiagTailX0RatChunk000Sub000Block189Part006
    + surrogateDiagTailX0RatChunk000Sub000Block189Part007
    + surrogateDiagTailX0RatChunk000Sub000Block189Part008
    + surrogateDiagTailX0RatChunk000Sub000Block189Part009

def surrogateDiagonalTailChunk000Sub000Block189MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block189Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block189Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block189Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block189Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block189Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block189Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block189Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block189Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block189Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block189Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block189Mid : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block189Part010
    + surrogateDiagTailX0RatChunk000Sub000Block189Part011
    + surrogateDiagTailX0RatChunk000Sub000Block189Part012
    + surrogateDiagTailX0RatChunk000Sub000Block189Part013
    + surrogateDiagTailX0RatChunk000Sub000Block189Part014
    + surrogateDiagTailX0RatChunk000Sub000Block189Part015
    + surrogateDiagTailX0RatChunk000Sub000Block189Part016
    + surrogateDiagTailX0RatChunk000Sub000Block189Part017
    + surrogateDiagTailX0RatChunk000Sub000Block189Part018
    + surrogateDiagTailX0RatChunk000Sub000Block189Part019

def surrogateDiagonalTailChunk000Sub000Block189TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block189Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block189Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block189Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block189Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block189Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block189Tail : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block189Part020
    + surrogateDiagTailX0RatChunk000Sub000Block189Part021
    + surrogateDiagTailX0RatChunk000Sub000Block189Part022
    + surrogateDiagTailX0RatChunk000Sub000Block189Part023
    + surrogateDiagTailX0RatChunk000Sub000Block189Part024

def surrogateDiagonalTailChunk000Sub000Block189Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub000Block189HeadSum X0
    + surrogateDiagonalTailChunk000Sub000Block189MidSum X0
    + surrogateDiagonalTailChunk000Sub000Block189TailSum X0

def surrogateDiagTailX0RatChunk000Sub000Block189 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block189Part000
    + surrogateDiagTailX0RatChunk000Sub000Block189Part001
    + surrogateDiagTailX0RatChunk000Sub000Block189Part002
    + surrogateDiagTailX0RatChunk000Sub000Block189Part003
    + surrogateDiagTailX0RatChunk000Sub000Block189Part004
    + surrogateDiagTailX0RatChunk000Sub000Block189Part005
    + surrogateDiagTailX0RatChunk000Sub000Block189Part006
    + surrogateDiagTailX0RatChunk000Sub000Block189Part007
    + surrogateDiagTailX0RatChunk000Sub000Block189Part008
    + surrogateDiagTailX0RatChunk000Sub000Block189Part009
    + surrogateDiagTailX0RatChunk000Sub000Block189Part010
    + surrogateDiagTailX0RatChunk000Sub000Block189Part011
    + surrogateDiagTailX0RatChunk000Sub000Block189Part012
    + surrogateDiagTailX0RatChunk000Sub000Block189Part013
    + surrogateDiagTailX0RatChunk000Sub000Block189Part014
    + surrogateDiagTailX0RatChunk000Sub000Block189Part015
    + surrogateDiagTailX0RatChunk000Sub000Block189Part016
    + surrogateDiagTailX0RatChunk000Sub000Block189Part017
    + surrogateDiagTailX0RatChunk000Sub000Block189Part018
    + surrogateDiagTailX0RatChunk000Sub000Block189Part019
    + surrogateDiagTailX0RatChunk000Sub000Block189Part020
    + surrogateDiagTailX0RatChunk000Sub000Block189Part021
    + surrogateDiagTailX0RatChunk000Sub000Block189Part022
    + surrogateDiagTailX0RatChunk000Sub000Block189Part023
    + surrogateDiagTailX0RatChunk000Sub000Block189Part024

theorem surrogateDiagTailX0RatChunk000Sub000Block189_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk000Sub000Block189Head + surrogateDiagTailX0RatChunk000Sub000Block189Mid + surrogateDiagTailX0RatChunk000Sub000Block189Tail =
      surrogateDiagTailX0RatChunk000Sub000Block189 := by
  unfold surrogateDiagTailX0RatChunk000Sub000Block189Head surrogateDiagTailX0RatChunk000Sub000Block189Mid surrogateDiagTailX0RatChunk000Sub000Block189Tail surrogateDiagTailX0RatChunk000Sub000Block189
  ring

def SurrogateDiagonalTailChunk000Sub000Block189HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block189HeadSum X0 = surrogateDiagTailX0RatChunk000Sub000Block189Head

def SurrogateDiagonalTailChunk000Sub000Block189MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block189MidSum X0 = surrogateDiagTailX0RatChunk000Sub000Block189Mid

def SurrogateDiagonalTailChunk000Sub000Block189TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block189TailSum X0 = surrogateDiagTailX0RatChunk000Sub000Block189Tail

theorem surrogateDiagonalTailChunk000Sub000Block189_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk000Sub000Block189HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk000Sub000Block189MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk000Sub000Block189TailCertificateAt X0) :
    surrogateDiagonalTailChunk000Sub000Block189Sum X0 = surrogateDiagTailX0RatChunk000Sub000Block189 := by
  unfold SurrogateDiagonalTailChunk000Sub000Block189HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk000Sub000Block189MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk000Sub000Block189TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk000Sub000Block189Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk000Sub000Block189_eq_head_add_mid_add_tail

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

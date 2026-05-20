import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0TailPilot25

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

open scoped BigOperators

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

/- Generated direct-term certificate blocks for tail chunk 000, subchunk 000, blocks [94,95). -/

/- Block 094 covers tail-support indices [2350,2375) and q from 3917 to 3955. -/

def TailChunk000Sub000Block094Part000SupportExplicit : Finset ℕ :=
  ([3917] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block094Part000 : ℚ :=
  (239732640625 : ℚ) / 147006859569775392

def SurrogateDiagonalTailChunk000Sub000Block094Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3917
    = surrogateDiagTailX0RatChunk000Sub000Block094Part000

theorem surrogateDiagonalTailChunk000Sub000Block094Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block094Part000CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block094Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block094Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block094Part000CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block094Part000SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block094Part000] using hcert

def TailChunk000Sub000Block094Part001SupportExplicit : Finset ℕ :=
  ([3918] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block094Part001 : ℚ :=
  (23290215475 : ℚ) / 451873883745408

def SurrogateDiagonalTailChunk000Sub000Block094Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3918
    = surrogateDiagTailX0RatChunk000Sub000Block094Part001

theorem surrogateDiagonalTailChunk000Sub000Block094Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block094Part001CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block094Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block094Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block094Part001CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block094Part001SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block094Part001] using hcert

def TailChunk000Sub000Block094Part002SupportExplicit : Finset ℕ :=
  ([3919] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block094Part002 : ℚ :=
  (239977515625 : ℚ) / 147307410168525522

def SurrogateDiagonalTailChunk000Sub000Block094Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3919
    = surrogateDiagTailX0RatChunk000Sub000Block094Part002

theorem surrogateDiagonalTailChunk000Sub000Block094Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block094Part002CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block094Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block094Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block094Part002CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block094Part002SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block094Part002] using hcert

def TailChunk000Sub000Block094Part003SupportExplicit : Finset ℕ :=
  ([3921] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block094Part003 : ℚ :=
  (746968452475 : ℚ) / 116391040133155968

def SurrogateDiagonalTailChunk000Sub000Block094Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3921
    = surrogateDiagTailX0RatChunk000Sub000Block094Part003

theorem surrogateDiagonalTailChunk000Sub000Block094Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block094Part003CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block094Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block094Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block094Part003CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block094Part003SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block094Part003] using hcert

def TailChunk000Sub000Block094Part004SupportExplicit : Finset ℕ :=
  ([3922] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block094Part004 : ℚ :=
  (683737980625 : ℚ) / 30707908402249728

def SurrogateDiagonalTailChunk000Sub000Block094Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3922
    = surrogateDiagTailX0RatChunk000Sub000Block094Part004

theorem surrogateDiagonalTailChunk000Sub000Block094Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block094Part004CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block094Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block094Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block094Part004CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block094Part004SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block094Part004] using hcert

def TailChunk000Sub000Block094Part005SupportExplicit : Finset ℕ :=
  ([3923] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block094Part005 : ℚ :=
  (240467640625 : ℚ) / 147909893677932882

def SurrogateDiagonalTailChunk000Sub000Block094Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3923
    = surrogateDiagTailX0RatChunk000Sub000Block094Part005

theorem surrogateDiagonalTailChunk000Sub000Block094Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block094Part005CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block094Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block094Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block094Part005CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block094Part005SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block094Part005] using hcert

def TailChunk000Sub000Block094Part006SupportExplicit : Finset ℕ :=
  ([3926] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block094Part006 : ℚ :=
  (5228261099 : ℚ) / 209993990400000

def SurrogateDiagonalTailChunk000Sub000Block094Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3926
    = surrogateDiagTailX0RatChunk000Sub000Block094Part006

theorem surrogateDiagonalTailChunk000Sub000Block094Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block094Part006CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block094Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block094Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block094Part006CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block094Part006SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block094Part006] using hcert

def TailChunk000Sub000Block094Part007SupportExplicit : Finset ℕ :=
  ([3927] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block094Part007 : ℚ :=
  (11316766589 : ℚ) / 679613143449600

def SurrogateDiagonalTailChunk000Sub000Block094Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3927
    = surrogateDiagTailX0RatChunk000Sub000Block094Part007

theorem surrogateDiagonalTailChunk000Sub000Block094Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block094Part007CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block094Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block094Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block094Part007CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block094Part007SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block094Part007] using hcert

def TailChunk000Sub000Block094Part008SupportExplicit : Finset ℕ :=
  ([3929] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block094Part008 : ℚ :=
  (241203765625 : ℚ) / 148817081781023232

def SurrogateDiagonalTailChunk000Sub000Block094Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3929
    = surrogateDiagTailX0RatChunk000Sub000Block094Part008

theorem surrogateDiagonalTailChunk000Sub000Block094Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block094Part008CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block094Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block094Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block094Part008CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block094Part008SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block094Part008] using hcert

def TailChunk000Sub000Block094Part009SupportExplicit : Finset ℕ :=
  ([3930] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block094Part009 : ℚ :=
  (1433350259 : ℚ) / 14626156646400

def SurrogateDiagonalTailChunk000Sub000Block094Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3930
    = surrogateDiagTailX0RatChunk000Sub000Block094Part009

theorem surrogateDiagonalTailChunk000Sub000Block094Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block094Part009CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block094Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block094Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block094Part009CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block094Part009SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block094Part009] using hcert

def TailChunk000Sub000Block094Part010SupportExplicit : Finset ℕ :=
  ([3931] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block094Part010 : ℚ :=
  (386319025 : ℚ) / 238592644997202

def SurrogateDiagonalTailChunk000Sub000Block094Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3931
    = surrogateDiagTailX0RatChunk000Sub000Block094Part010

theorem surrogateDiagonalTailChunk000Sub000Block094Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block094Part010CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block094Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block094Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block094Part010CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block094Part010SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block094Part010] using hcert

def TailChunk000Sub000Block094Part011SupportExplicit : Finset ℕ :=
  ([3934] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block094Part011 : ℚ :=
  (17325593731 : ℚ) / 796753494835200

def SurrogateDiagonalTailChunk000Sub000Block094Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3934
    = surrogateDiagTailX0RatChunk000Sub000Block094Part011

theorem surrogateDiagonalTailChunk000Sub000Block094Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block094Part011CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block094Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block094Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block094Part011CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block094Part011SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block094Part011] using hcert

def TailChunk000Sub000Block094Part012SupportExplicit : Finset ℕ :=
  ([3935] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block094Part012 : ℚ :=
  (812261537875 : ℚ) / 244318868477134848

def SurrogateDiagonalTailChunk000Sub000Block094Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3935
    = surrogateDiagTailX0RatChunk000Sub000Block094Part012

theorem surrogateDiagonalTailChunk000Sub000Block094Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block094Part012CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block094Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block094Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block094Part012CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block094Part012SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block094Part012] using hcert

def TailChunk000Sub000Block094Part013SupportExplicit : Finset ℕ :=
  ([3937] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block094Part013 : ℚ :=
  (37608239227 : ℚ) / 20419920623491200

def SurrogateDiagonalTailChunk000Sub000Block094Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3937
    = surrogateDiagTailX0RatChunk000Sub000Block094Part013

theorem surrogateDiagonalTailChunk000Sub000Block094Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block094Part013CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block094Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block094Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block094Part013CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block094Part013SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block094Part013] using hcert

def TailChunk000Sub000Block094Part014SupportExplicit : Finset ℕ :=
  ([3938] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block094Part014 : ℚ :=
  (862410969 : ℚ) / 33469221039040

def SurrogateDiagonalTailChunk000Sub000Block094Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3938
    = surrogateDiagTailX0RatChunk000Sub000Block094Part014

theorem surrogateDiagonalTailChunk000Sub000Block094Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block094Part014CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block094Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block094Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block094Part014CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block094Part014SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block094Part014] using hcert

def TailChunk000Sub000Block094Part015SupportExplicit : Finset ℕ :=
  ([3939] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block094Part015 : ℚ :=
  (40103923 : ℚ) / 3456691200000

def SurrogateDiagonalTailChunk000Sub000Block094Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3939
    = surrogateDiagTailX0RatChunk000Sub000Block094Part015

theorem surrogateDiagonalTailChunk000Sub000Block094Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block094Part015CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block094Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block094Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block094Part015CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block094Part015SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block094Part015] using hcert

def TailChunk000Sub000Block094Part016SupportExplicit : Finset ℕ :=
  ([3941] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block094Part016 : ℚ :=
  (10706767325 : ℚ) / 2244991136005512

def SurrogateDiagonalTailChunk000Sub000Block094Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3941
    = surrogateDiagTailX0RatChunk000Sub000Block094Part016

theorem surrogateDiagonalTailChunk000Sub000Block094Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block094Part016CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block094Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block094Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block094Part016CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block094Part016SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block094Part016] using hcert

def TailChunk000Sub000Block094Part017SupportExplicit : Finset ℕ :=
  ([3943] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block094Part017 : ℚ :=
  (1943017443775 : ℚ) / 603800319728002248

def SurrogateDiagonalTailChunk000Sub000Block094Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3943
    = surrogateDiagTailX0RatChunk000Sub000Block094Part017

theorem surrogateDiagonalTailChunk000Sub000Block094Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block094Part017CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block094Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block094Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block094Part017CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block094Part017SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block094Part017] using hcert

def TailChunk000Sub000Block094Part018SupportExplicit : Finset ℕ :=
  ([3945] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block094Part018 : ℚ :=
  (204435853675 : ℚ) / 12065129307512832

def SurrogateDiagonalTailChunk000Sub000Block094Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3945
    = surrogateDiagTailX0RatChunk000Sub000Block094Part018

theorem surrogateDiagonalTailChunk000Sub000Block094Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block094Part018CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block094Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block094Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block094Part018CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block094Part018SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block094Part018] using hcert

def TailChunk000Sub000Block094Part019SupportExplicit : Finset ℕ :=
  ([3946] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block094Part019 : ℚ :=
  (486493806775 : ℚ) / 37814163817139328

def SurrogateDiagonalTailChunk000Sub000Block094Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3946
    = surrogateDiagTailX0RatChunk000Sub000Block094Part019

theorem surrogateDiagonalTailChunk000Sub000Block094Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block094Part019CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block094Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block094Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block094Part019CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block094Part019SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block094Part019] using hcert

def TailChunk000Sub000Block094Part020SupportExplicit : Finset ℕ :=
  ([3947] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block094Part020 : ℚ :=
  (243418890625 : ℚ) / 151563697352544882

def SurrogateDiagonalTailChunk000Sub000Block094Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3947
    = surrogateDiagTailX0RatChunk000Sub000Block094Part020

theorem surrogateDiagonalTailChunk000Sub000Block094Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block094Part020CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block094Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block094Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block094Part020CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block094Part020SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block094Part020] using hcert

def TailChunk000Sub000Block094Part021SupportExplicit : Finset ℕ :=
  ([3949] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block094Part021 : ℚ :=
  (9084461113 : ℚ) / 4107324024544800

def SurrogateDiagonalTailChunk000Sub000Block094Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3949
    = surrogateDiagTailX0RatChunk000Sub000Block094Part021

theorem surrogateDiagonalTailChunk000Sub000Block094Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block094Part021CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block094Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block094Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block094Part021CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block094Part021SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block094Part021] using hcert

def TailChunk000Sub000Block094Part022SupportExplicit : Finset ℕ :=
  ([3953] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block094Part022 : ℚ :=
  (106015019375 : ℚ) / 59658463763851392

def SurrogateDiagonalTailChunk000Sub000Block094Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3953
    = surrogateDiagTailX0RatChunk000Sub000Block094Part022

theorem surrogateDiagonalTailChunk000Sub000Block094Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block094Part022CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block094Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block094Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block094Part022CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block094Part022SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block094Part022] using hcert

def TailChunk000Sub000Block094Part023SupportExplicit : Finset ℕ :=
  ([3954] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block094Part023 : ℚ :=
  (230367506825 : ℚ) / 3749906337221184

def SurrogateDiagonalTailChunk000Sub000Block094Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3954
    = surrogateDiagTailX0RatChunk000Sub000Block094Part023

theorem surrogateDiagonalTailChunk000Sub000Block094Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block094Part023CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block094Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block094Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block094Part023CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block094Part023SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block094Part023] using hcert

def TailChunk000Sub000Block094Part024SupportExplicit : Finset ℕ :=
  ([3955] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block094Part024 : ℚ :=
  (724944956125 : ℚ) / 130540092593799168

def SurrogateDiagonalTailChunk000Sub000Block094Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3955
    = surrogateDiagTailX0RatChunk000Sub000Block094Part024

theorem surrogateDiagonalTailChunk000Sub000Block094Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block094Part024CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block094Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block094Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block094Part024CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block094Part024SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block094Part024] using hcert

def surrogateDiagonalTailChunk000Sub000Block094HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block094Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block094Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block094Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block094Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block094Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block094Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block094Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block094Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block094Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block094Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block094Head : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block094Part000
    + surrogateDiagTailX0RatChunk000Sub000Block094Part001
    + surrogateDiagTailX0RatChunk000Sub000Block094Part002
    + surrogateDiagTailX0RatChunk000Sub000Block094Part003
    + surrogateDiagTailX0RatChunk000Sub000Block094Part004
    + surrogateDiagTailX0RatChunk000Sub000Block094Part005
    + surrogateDiagTailX0RatChunk000Sub000Block094Part006
    + surrogateDiagTailX0RatChunk000Sub000Block094Part007
    + surrogateDiagTailX0RatChunk000Sub000Block094Part008
    + surrogateDiagTailX0RatChunk000Sub000Block094Part009

def surrogateDiagonalTailChunk000Sub000Block094MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block094Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block094Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block094Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block094Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block094Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block094Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block094Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block094Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block094Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block094Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block094Mid : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block094Part010
    + surrogateDiagTailX0RatChunk000Sub000Block094Part011
    + surrogateDiagTailX0RatChunk000Sub000Block094Part012
    + surrogateDiagTailX0RatChunk000Sub000Block094Part013
    + surrogateDiagTailX0RatChunk000Sub000Block094Part014
    + surrogateDiagTailX0RatChunk000Sub000Block094Part015
    + surrogateDiagTailX0RatChunk000Sub000Block094Part016
    + surrogateDiagTailX0RatChunk000Sub000Block094Part017
    + surrogateDiagTailX0RatChunk000Sub000Block094Part018
    + surrogateDiagTailX0RatChunk000Sub000Block094Part019

def surrogateDiagonalTailChunk000Sub000Block094TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block094Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block094Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block094Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block094Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block094Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block094Tail : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block094Part020
    + surrogateDiagTailX0RatChunk000Sub000Block094Part021
    + surrogateDiagTailX0RatChunk000Sub000Block094Part022
    + surrogateDiagTailX0RatChunk000Sub000Block094Part023
    + surrogateDiagTailX0RatChunk000Sub000Block094Part024

def surrogateDiagonalTailChunk000Sub000Block094Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub000Block094HeadSum X0
    + surrogateDiagonalTailChunk000Sub000Block094MidSum X0
    + surrogateDiagonalTailChunk000Sub000Block094TailSum X0

def surrogateDiagTailX0RatChunk000Sub000Block094 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block094Part000
    + surrogateDiagTailX0RatChunk000Sub000Block094Part001
    + surrogateDiagTailX0RatChunk000Sub000Block094Part002
    + surrogateDiagTailX0RatChunk000Sub000Block094Part003
    + surrogateDiagTailX0RatChunk000Sub000Block094Part004
    + surrogateDiagTailX0RatChunk000Sub000Block094Part005
    + surrogateDiagTailX0RatChunk000Sub000Block094Part006
    + surrogateDiagTailX0RatChunk000Sub000Block094Part007
    + surrogateDiagTailX0RatChunk000Sub000Block094Part008
    + surrogateDiagTailX0RatChunk000Sub000Block094Part009
    + surrogateDiagTailX0RatChunk000Sub000Block094Part010
    + surrogateDiagTailX0RatChunk000Sub000Block094Part011
    + surrogateDiagTailX0RatChunk000Sub000Block094Part012
    + surrogateDiagTailX0RatChunk000Sub000Block094Part013
    + surrogateDiagTailX0RatChunk000Sub000Block094Part014
    + surrogateDiagTailX0RatChunk000Sub000Block094Part015
    + surrogateDiagTailX0RatChunk000Sub000Block094Part016
    + surrogateDiagTailX0RatChunk000Sub000Block094Part017
    + surrogateDiagTailX0RatChunk000Sub000Block094Part018
    + surrogateDiagTailX0RatChunk000Sub000Block094Part019
    + surrogateDiagTailX0RatChunk000Sub000Block094Part020
    + surrogateDiagTailX0RatChunk000Sub000Block094Part021
    + surrogateDiagTailX0RatChunk000Sub000Block094Part022
    + surrogateDiagTailX0RatChunk000Sub000Block094Part023
    + surrogateDiagTailX0RatChunk000Sub000Block094Part024

theorem surrogateDiagTailX0RatChunk000Sub000Block094_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk000Sub000Block094Head + surrogateDiagTailX0RatChunk000Sub000Block094Mid + surrogateDiagTailX0RatChunk000Sub000Block094Tail =
      surrogateDiagTailX0RatChunk000Sub000Block094 := by
  unfold surrogateDiagTailX0RatChunk000Sub000Block094Head surrogateDiagTailX0RatChunk000Sub000Block094Mid surrogateDiagTailX0RatChunk000Sub000Block094Tail surrogateDiagTailX0RatChunk000Sub000Block094
  ring

def SurrogateDiagonalTailChunk000Sub000Block094HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block094HeadSum X0 = surrogateDiagTailX0RatChunk000Sub000Block094Head

def SurrogateDiagonalTailChunk000Sub000Block094MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block094MidSum X0 = surrogateDiagTailX0RatChunk000Sub000Block094Mid

def SurrogateDiagonalTailChunk000Sub000Block094TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block094TailSum X0 = surrogateDiagTailX0RatChunk000Sub000Block094Tail

theorem surrogateDiagonalTailChunk000Sub000Block094_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk000Sub000Block094HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk000Sub000Block094MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk000Sub000Block094TailCertificateAt X0) :
    surrogateDiagonalTailChunk000Sub000Block094Sum X0 = surrogateDiagTailX0RatChunk000Sub000Block094 := by
  unfold SurrogateDiagonalTailChunk000Sub000Block094HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk000Sub000Block094MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk000Sub000Block094TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk000Sub000Block094Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk000Sub000Block094_eq_head_add_mid_add_tail

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

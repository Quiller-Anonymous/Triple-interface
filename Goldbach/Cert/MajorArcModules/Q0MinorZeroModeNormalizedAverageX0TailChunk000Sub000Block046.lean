import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0TailPilot25

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

open scoped BigOperators

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

/- Generated direct-term certificate blocks for tail chunk 000, subchunk 000, blocks [46,47). -/

/- Block 046 covers tail-support indices [1150,1175) and q from 1946 to 1985. -/

def TailChunk000Sub000Block046Part000SupportExplicit : Finset ℕ :=
  ([1946] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block046Part000 : ℚ :=
  (2728803125 : ℚ) / 10882394123616

def SurrogateDiagonalTailChunk000Sub000Block046Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1946
    = surrogateDiagTailX0RatChunk000Sub000Block046Part000

theorem surrogateDiagonalTailChunk000Sub000Block046Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block046Part000CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block046Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block046Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block046Part000CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block046Part000SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block046Part000] using hcert

def TailChunk000Sub000Block046Part001SupportExplicit : Finset ℕ :=
  ([1947] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block046Part001 : ℚ :=
  (7924712039 : ℚ) / 90550074393600

def SurrogateDiagonalTailChunk000Sub000Block046Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1947
    = surrogateDiagTailX0RatChunk000Sub000Block046Part001

theorem surrogateDiagonalTailChunk000Sub000Block046Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block046Part001CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block046Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block046Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block046Part001CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block046Part001SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block046Part001] using hcert

def TailChunk000Sub000Block046Part002SupportExplicit : Finset ℕ :=
  ([1949] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block046Part002 : ℚ :=
  (237317597475 : ℚ) / 12002215336087936

def SurrogateDiagonalTailChunk000Sub000Block046Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1949
    = surrogateDiagTailX0RatChunk000Sub000Block046Part002

theorem surrogateDiagonalTailChunk000Sub000Block046Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block046Part002CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block046Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block046Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block046Part002CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block046Part002SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block046Part002] using hcert

def TailChunk000Sub000Block046Part003SupportExplicit : Finset ℕ :=
  ([1951] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block046Part003 : ℚ :=
  (19028198599 : ℚ) / 1446189805125000

def SurrogateDiagonalTailChunk000Sub000Block046Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1951
    = surrogateDiagTailX0RatChunk000Sub000Block046Part003

theorem surrogateDiagonalTailChunk000Sub000Block046Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block046Part003CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block046Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block046Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block046Part003CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block046Part003SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block046Part003] using hcert

def TailChunk000Sub000Block046Part004SupportExplicit : Finset ℕ :=
  ([1954] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block046Part004 : ℚ :=
  (149025840125 : ℚ) / 1134478144978944

def SurrogateDiagonalTailChunk000Sub000Block046Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1954
    = surrogateDiagTailX0RatChunk000Sub000Block046Part004

theorem surrogateDiagonalTailChunk000Sub000Block046Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block046Part004CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block046Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block046Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block046Part004CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block046Part004SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block046Part004] using hcert

def TailChunk000Sub000Block046Part005SupportExplicit : Finset ℕ :=
  ([1955] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block046Part005 : ℚ :=
  (493081347775 : ℚ) / 9827373859995648

def SurrogateDiagonalTailChunk000Sub000Block046Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1955
    = surrogateDiagTailX0RatChunk000Sub000Block046Part005

theorem surrogateDiagonalTailChunk000Sub000Block046Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block046Part005CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block046Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block046Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block046Part005CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block046Part005SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block046Part005] using hcert

def TailChunk000Sub000Block046Part006SupportExplicit : Finset ℕ :=
  ([1957] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block046Part006 : ℚ :=
  (166746275125 : ℚ) / 7103257769240352

def SurrogateDiagonalTailChunk000Sub000Block046Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1957
    = surrogateDiagTailX0RatChunk000Sub000Block046Part006

theorem surrogateDiagonalTailChunk000Sub000Block046Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block046Part006CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block046Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block046Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block046Part006CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block046Part006SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block046Part006] using hcert

def TailChunk000Sub000Block046Part007SupportExplicit : Finset ℕ :=
  ([1958] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block046Part007 : ℚ :=
  (10812600529 : ℚ) / 59981529907200

def SurrogateDiagonalTailChunk000Sub000Block046Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1958
    = surrogateDiagTailX0RatChunk000Sub000Block046Part007

theorem surrogateDiagonalTailChunk000Sub000Block046Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block046Part007CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block046Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block046Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block046Part007CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block046Part007SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block046Part007] using hcert

def TailChunk000Sub000Block046Part008SupportExplicit : Finset ℕ :=
  ([1959] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block046Part008 : ℚ :=
  (23290215475 : ℚ) / 451873883745408

def SurrogateDiagonalTailChunk000Sub000Block046Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1959
    = surrogateDiagTailX0RatChunk000Sub000Block046Part008

theorem surrogateDiagonalTailChunk000Sub000Block046Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block046Part008CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block046Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block046Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block046Part008CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block046Part008SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block046Part008] using hcert

def TailChunk000Sub000Block046Part009SupportExplicit : Finset ℕ :=
  ([1961] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block046Part009 : ℚ :=
  (683737980625 : ℚ) / 30707908402249728

def SurrogateDiagonalTailChunk000Sub000Block046Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1961
    = surrogateDiagTailX0RatChunk000Sub000Block046Part009

theorem surrogateDiagonalTailChunk000Sub000Block046Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block046Part009CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block046Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block046Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block046Part009CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block046Part009SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block046Part009] using hcert

def TailChunk000Sub000Block046Part010SupportExplicit : Finset ℕ :=
  ([1963] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block046Part010 : ℚ :=
  (5228261099 : ℚ) / 209993990400000

def SurrogateDiagonalTailChunk000Sub000Block046Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1963
    = surrogateDiagTailX0RatChunk000Sub000Block046Part010

theorem surrogateDiagonalTailChunk000Sub000Block046Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block046Part010CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block046Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block046Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block046Part010CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block046Part010SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block046Part010] using hcert

def TailChunk000Sub000Block046Part011SupportExplicit : Finset ℕ :=
  ([1965] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block046Part011 : ℚ :=
  (1433350259 : ℚ) / 14626156646400

def SurrogateDiagonalTailChunk000Sub000Block046Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1965
    = surrogateDiagTailX0RatChunk000Sub000Block046Part011

theorem surrogateDiagonalTailChunk000Sub000Block046Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block046Part011CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block046Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block046Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block046Part011CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block046Part011SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block046Part011] using hcert

def TailChunk000Sub000Block046Part012SupportExplicit : Finset ℕ :=
  ([1966] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block046Part012 : ℚ :=
  (150861870125 : ℚ) / 1162633451414244

def SurrogateDiagonalTailChunk000Sub000Block046Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1966
    = surrogateDiagTailX0RatChunk000Sub000Block046Part012

theorem surrogateDiagonalTailChunk000Sub000Block046Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block046Part012CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block046Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block046Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block046Part012CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block046Part012SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block046Part012] using hcert

def TailChunk000Sub000Block046Part013SupportExplicit : Finset ℕ :=
  ([1967] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block046Part013 : ℚ :=
  (17325593731 : ℚ) / 796753494835200

def SurrogateDiagonalTailChunk000Sub000Block046Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1967
    = surrogateDiagTailX0RatChunk000Sub000Block046Part013

theorem surrogateDiagonalTailChunk000Sub000Block046Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block046Part013CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block046Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block046Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block046Part013CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block046Part013SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block046Part013] using hcert

def TailChunk000Sub000Block046Part014SupportExplicit : Finset ℕ :=
  ([1969] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block046Part014 : ℚ :=
  (862410969 : ℚ) / 33469221039040

def SurrogateDiagonalTailChunk000Sub000Block046Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1969
    = surrogateDiagTailX0RatChunk000Sub000Block046Part014

theorem surrogateDiagonalTailChunk000Sub000Block046Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block046Part014CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block046Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block046Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block046Part014CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block046Part014SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block046Part014] using hcert

def TailChunk000Sub000Block046Part015SupportExplicit : Finset ℕ :=
  ([1970] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block046Part015 : ℚ :=
  (120696509375 : ℚ) / 472346948419584

def SurrogateDiagonalTailChunk000Sub000Block046Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1970
    = surrogateDiagTailX0RatChunk000Sub000Block046Part015

theorem surrogateDiagonalTailChunk000Sub000Block046Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block046Part015CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block046Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block046Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block046Part015CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block046Part015SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block046Part015] using hcert

def TailChunk000Sub000Block046Part016SupportExplicit : Finset ℕ :=
  ([1973] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block046Part016 : ℚ :=
  (486493806775 : ℚ) / 37814163817139328

def SurrogateDiagonalTailChunk000Sub000Block046Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1973
    = surrogateDiagTailX0RatChunk000Sub000Block046Part016

theorem surrogateDiagonalTailChunk000Sub000Block046Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block046Part016CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block046Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block046Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block046Part016CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block046Part016SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block046Part016] using hcert

def TailChunk000Sub000Block046Part017SupportExplicit : Finset ℕ :=
  ([1974] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block046Part017 : ℚ :=
  (85235686175 : ℚ) / 116078870651904

def SurrogateDiagonalTailChunk000Sub000Block046Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1974
    = surrogateDiagTailX0RatChunk000Sub000Block046Part017

theorem surrogateDiagonalTailChunk000Sub000Block046Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block046Part017CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block046Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block046Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block046Part017CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block046Part017SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block046Part017] using hcert

def TailChunk000Sub000Block046Part018SupportExplicit : Finset ℕ :=
  ([1977] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block046Part018 : ℚ :=
  (230367506825 : ℚ) / 3749906337221184

def SurrogateDiagonalTailChunk000Sub000Block046Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1977
    = surrogateDiagTailX0RatChunk000Sub000Block046Part018

theorem surrogateDiagonalTailChunk000Sub000Block046Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block046Part018CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block046Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block046Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block046Part018CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block046Part018SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block046Part018] using hcert

def TailChunk000Sub000Block046Part019SupportExplicit : Finset ℕ :=
  ([1978] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block046Part019 : ℚ :=
  (5105626775 : ℚ) / 32548180574448

def SurrogateDiagonalTailChunk000Sub000Block046Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1978
    = surrogateDiagTailX0RatChunk000Sub000Block046Part019

theorem surrogateDiagonalTailChunk000Sub000Block046Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block046Part019CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block046Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block046Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block046Part019CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block046Part019SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block046Part019] using hcert

def TailChunk000Sub000Block046Part020SupportExplicit : Finset ℕ :=
  ([1979] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block046Part020 : ℚ :=
  (244679651475 : ℚ) / 12758827130388376

def SurrogateDiagonalTailChunk000Sub000Block046Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1979
    = surrogateDiagTailX0RatChunk000Sub000Block046Part020

theorem surrogateDiagonalTailChunk000Sub000Block046Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block046Part020CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block046Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block046Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block046Part020CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block046Part020SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block046Part020] using hcert

def TailChunk000Sub000Block046Part021SupportExplicit : Finset ℕ :=
  ([1981] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block046Part021 : ℚ :=
  (439322854675 : ℚ) / 20494073701381248

def SurrogateDiagonalTailChunk000Sub000Block046Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1981
    = surrogateDiagTailX0RatChunk000Sub000Block046Part021

theorem surrogateDiagonalTailChunk000Sub000Block046Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block046Part021CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block046Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block046Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block046Part021CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block046Part021SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block046Part021] using hcert

def TailChunk000Sub000Block046Part022SupportExplicit : Finset ℕ :=
  ([1982] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block046Part022 : ℚ :=
  (1226619169 : ℚ) / 9607881292020

def SurrogateDiagonalTailChunk000Sub000Block046Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1982
    = surrogateDiagTailX0RatChunk000Sub000Block046Part022

theorem surrogateDiagonalTailChunk000Sub000Block046Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block046Part022CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block046Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block046Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block046Part022CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block046Part022SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block046Part022] using hcert

def TailChunk000Sub000Block046Part023SupportExplicit : Finset ℕ :=
  ([1983] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block046Part023 : ℚ :=
  (7092295217 : ℚ) / 151828247577600

def SurrogateDiagonalTailChunk000Sub000Block046Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1983
    = surrogateDiagTailX0RatChunk000Sub000Block046Part023

theorem surrogateDiagonalTailChunk000Sub000Block046Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block046Part023CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block046Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block046Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block046Part023CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block046Part023SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block046Part023] using hcert

def TailChunk000Sub000Block046Part024SupportExplicit : Finset ℕ :=
  ([1985] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block046Part024 : ℚ :=
  (569811514825 : ℚ) / 15741552708845568

def SurrogateDiagonalTailChunk000Sub000Block046Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1985
    = surrogateDiagTailX0RatChunk000Sub000Block046Part024

theorem surrogateDiagonalTailChunk000Sub000Block046Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block046Part024CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block046Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block046Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block046Part024CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block046Part024SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block046Part024] using hcert

def surrogateDiagonalTailChunk000Sub000Block046HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block046Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block046Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block046Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block046Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block046Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block046Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block046Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block046Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block046Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block046Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block046Head : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block046Part000
    + surrogateDiagTailX0RatChunk000Sub000Block046Part001
    + surrogateDiagTailX0RatChunk000Sub000Block046Part002
    + surrogateDiagTailX0RatChunk000Sub000Block046Part003
    + surrogateDiagTailX0RatChunk000Sub000Block046Part004
    + surrogateDiagTailX0RatChunk000Sub000Block046Part005
    + surrogateDiagTailX0RatChunk000Sub000Block046Part006
    + surrogateDiagTailX0RatChunk000Sub000Block046Part007
    + surrogateDiagTailX0RatChunk000Sub000Block046Part008
    + surrogateDiagTailX0RatChunk000Sub000Block046Part009

def surrogateDiagonalTailChunk000Sub000Block046MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block046Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block046Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block046Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block046Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block046Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block046Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block046Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block046Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block046Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block046Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block046Mid : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block046Part010
    + surrogateDiagTailX0RatChunk000Sub000Block046Part011
    + surrogateDiagTailX0RatChunk000Sub000Block046Part012
    + surrogateDiagTailX0RatChunk000Sub000Block046Part013
    + surrogateDiagTailX0RatChunk000Sub000Block046Part014
    + surrogateDiagTailX0RatChunk000Sub000Block046Part015
    + surrogateDiagTailX0RatChunk000Sub000Block046Part016
    + surrogateDiagTailX0RatChunk000Sub000Block046Part017
    + surrogateDiagTailX0RatChunk000Sub000Block046Part018
    + surrogateDiagTailX0RatChunk000Sub000Block046Part019

def surrogateDiagonalTailChunk000Sub000Block046TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block046Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block046Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block046Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block046Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block046Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block046Tail : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block046Part020
    + surrogateDiagTailX0RatChunk000Sub000Block046Part021
    + surrogateDiagTailX0RatChunk000Sub000Block046Part022
    + surrogateDiagTailX0RatChunk000Sub000Block046Part023
    + surrogateDiagTailX0RatChunk000Sub000Block046Part024

def surrogateDiagonalTailChunk000Sub000Block046Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub000Block046HeadSum X0
    + surrogateDiagonalTailChunk000Sub000Block046MidSum X0
    + surrogateDiagonalTailChunk000Sub000Block046TailSum X0

def surrogateDiagTailX0RatChunk000Sub000Block046 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block046Part000
    + surrogateDiagTailX0RatChunk000Sub000Block046Part001
    + surrogateDiagTailX0RatChunk000Sub000Block046Part002
    + surrogateDiagTailX0RatChunk000Sub000Block046Part003
    + surrogateDiagTailX0RatChunk000Sub000Block046Part004
    + surrogateDiagTailX0RatChunk000Sub000Block046Part005
    + surrogateDiagTailX0RatChunk000Sub000Block046Part006
    + surrogateDiagTailX0RatChunk000Sub000Block046Part007
    + surrogateDiagTailX0RatChunk000Sub000Block046Part008
    + surrogateDiagTailX0RatChunk000Sub000Block046Part009
    + surrogateDiagTailX0RatChunk000Sub000Block046Part010
    + surrogateDiagTailX0RatChunk000Sub000Block046Part011
    + surrogateDiagTailX0RatChunk000Sub000Block046Part012
    + surrogateDiagTailX0RatChunk000Sub000Block046Part013
    + surrogateDiagTailX0RatChunk000Sub000Block046Part014
    + surrogateDiagTailX0RatChunk000Sub000Block046Part015
    + surrogateDiagTailX0RatChunk000Sub000Block046Part016
    + surrogateDiagTailX0RatChunk000Sub000Block046Part017
    + surrogateDiagTailX0RatChunk000Sub000Block046Part018
    + surrogateDiagTailX0RatChunk000Sub000Block046Part019
    + surrogateDiagTailX0RatChunk000Sub000Block046Part020
    + surrogateDiagTailX0RatChunk000Sub000Block046Part021
    + surrogateDiagTailX0RatChunk000Sub000Block046Part022
    + surrogateDiagTailX0RatChunk000Sub000Block046Part023
    + surrogateDiagTailX0RatChunk000Sub000Block046Part024

theorem surrogateDiagTailX0RatChunk000Sub000Block046_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk000Sub000Block046Head + surrogateDiagTailX0RatChunk000Sub000Block046Mid + surrogateDiagTailX0RatChunk000Sub000Block046Tail =
      surrogateDiagTailX0RatChunk000Sub000Block046 := by
  unfold surrogateDiagTailX0RatChunk000Sub000Block046Head surrogateDiagTailX0RatChunk000Sub000Block046Mid surrogateDiagTailX0RatChunk000Sub000Block046Tail surrogateDiagTailX0RatChunk000Sub000Block046
  ring

def SurrogateDiagonalTailChunk000Sub000Block046HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block046HeadSum X0 = surrogateDiagTailX0RatChunk000Sub000Block046Head

def SurrogateDiagonalTailChunk000Sub000Block046MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block046MidSum X0 = surrogateDiagTailX0RatChunk000Sub000Block046Mid

def SurrogateDiagonalTailChunk000Sub000Block046TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block046TailSum X0 = surrogateDiagTailX0RatChunk000Sub000Block046Tail

theorem surrogateDiagonalTailChunk000Sub000Block046_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk000Sub000Block046HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk000Sub000Block046MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk000Sub000Block046TailCertificateAt X0) :
    surrogateDiagonalTailChunk000Sub000Block046Sum X0 = surrogateDiagTailX0RatChunk000Sub000Block046 := by
  unfold SurrogateDiagonalTailChunk000Sub000Block046HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk000Sub000Block046MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk000Sub000Block046TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk000Sub000Block046Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk000Sub000Block046_eq_head_add_mid_add_tail

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

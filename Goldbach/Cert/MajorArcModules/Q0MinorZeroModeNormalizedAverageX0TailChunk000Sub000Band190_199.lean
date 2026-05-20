import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0TailPilot25

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

open scoped BigOperators

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

/- Generated direct-term certificate blocks for tail chunk 000, subchunk 000, blocks [190,200). -/

/-- Block 190 covers tail-support indices [4750,4775) and q from 7859 to 7898. -/

def TailChunk000Sub000Block190Part000SupportExplicit : Finset ℕ :=
  ([7859] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block190Part000 : ℚ :=
  (180684227 : ℚ) / 403356456760320

def SurrogateDiagonalTailChunk000Sub000Block190Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7859
    = surrogateDiagTailX0RatChunk000Sub000Block190Part000

theorem surrogateDiagonalTailChunk000Sub000Block190Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block190Part000CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block190Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block190Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block190Part000CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block190Part000SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block190Part000] using hcert

def TailChunk000Sub000Block190Part001SupportExplicit : Finset ℕ :=
  ([7861] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block190Part001 : ℚ :=
  (170604094475 : ℚ) / 285319058983396416

def SurrogateDiagonalTailChunk000Sub000Block190Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7861
    = surrogateDiagTailX0RatChunk000Sub000Block190Part001

theorem surrogateDiagonalTailChunk000Sub000Block190Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block190Part001CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block190Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block190Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block190Part001CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block190Part001SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block190Part001] using hcert

def TailChunk000Sub000Block190Part002SupportExplicit : Finset ℕ :=
  ([7862] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block190Part002 : ℚ :=
  (386319025 : ℚ) / 238592644997202

def SurrogateDiagonalTailChunk000Sub000Block190Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7862
    = surrogateDiagTailX0RatChunk000Sub000Block190Part002

theorem surrogateDiagonalTailChunk000Sub000Block190Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block190Part002CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block190Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block190Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block190Part002CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block190Part002SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block190Part002] using hcert

def TailChunk000Sub000Block190Part003SupportExplicit : Finset ℕ :=
  ([7863] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block190Part003 : ℚ :=
  (42921861839 : ℚ) / 37703529085977600

def SurrogateDiagonalTailChunk000Sub000Block190Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7863
    = surrogateDiagTailX0RatChunk000Sub000Block190Part003

theorem surrogateDiagonalTailChunk000Sub000Block190Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block190Part003CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block190Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block190Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block190Part003CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block190Part003SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block190Part003] using hcert

def TailChunk000Sub000Block190Part004SupportExplicit : Finset ℕ :=
  ([7867] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block190Part004 : ℚ :=
  (967026390625 : ℚ) / 2393220067735096242

def SurrogateDiagonalTailChunk000Sub000Block190Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7867
    = surrogateDiagTailX0RatChunk000Sub000Block190Part004

theorem surrogateDiagonalTailChunk000Sub000Block190Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block190Part004CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block190Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block190Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block190Part004CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block190Part004SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block190Part004] using hcert

def TailChunk000Sub000Block190Part005SupportExplicit : Finset ℕ :=
  ([7869] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block190Part005 : ℚ :=
  (16369736051 : ℚ) / 12907406616330240

def SurrogateDiagonalTailChunk000Sub000Block190Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7869
    = surrogateDiagTailX0RatChunk000Sub000Block190Part005

theorem surrogateDiagonalTailChunk000Sub000Block190Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block190Part005CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block190Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block190Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block190Part005CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block190Part005SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block190Part005] using hcert

def TailChunk000Sub000Block190Part006SupportExplicit : Finset ℕ :=
  ([7870] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block190Part006 : ℚ :=
  (812261537875 : ℚ) / 244318868477134848

def SurrogateDiagonalTailChunk000Sub000Block190Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7870
    = surrogateDiagTailX0RatChunk000Sub000Block190Part006

theorem surrogateDiagonalTailChunk000Sub000Block190Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block190Part006CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block190Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block190Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block190Part006CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block190Part006SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block190Part006] using hcert

def TailChunk000Sub000Block190Part007SupportExplicit : Finset ℕ :=
  ([7871] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block190Part007 : ℚ :=
  (3365626975 : ℚ) / 7069859344171008

def SurrogateDiagonalTailChunk000Sub000Block190Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7871
    = surrogateDiagTailX0RatChunk000Sub000Block190Part007

theorem surrogateDiagonalTailChunk000Sub000Block190Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block190Part007CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block190Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block190Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block190Part007CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block190Part007SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block190Part007] using hcert

def TailChunk000Sub000Block190Part008SupportExplicit : Finset ℕ :=
  ([7873] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block190Part008 : ℚ :=
  (968502015625 : ℚ) / 2400530394809106432

def SurrogateDiagonalTailChunk000Sub000Block190Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7873
    = surrogateDiagTailX0RatChunk000Sub000Block190Part008

theorem surrogateDiagonalTailChunk000Sub000Block190Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block190Part008CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block190Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block190Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block190Part008CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block190Part008SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block190Part008] using hcert

def TailChunk000Sub000Block190Part009SupportExplicit : Finset ℕ :=
  ([7874] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block190Part009 : ℚ :=
  (37608239227 : ℚ) / 20419920623491200

def SurrogateDiagonalTailChunk000Sub000Block190Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7874
    = surrogateDiagTailX0RatChunk000Sub000Block190Part009

theorem surrogateDiagonalTailChunk000Sub000Block190Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block190Part009CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block190Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block190Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block190Part009CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block190Part009SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block190Part009] using hcert

def TailChunk000Sub000Block190Part010SupportExplicit : Finset ℕ :=
  ([7877] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block190Part010 : ℚ :=
  (969486390625 : ℚ) / 2405413241734416672

def SurrogateDiagonalTailChunk000Sub000Block190Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7877
    = surrogateDiagTailX0RatChunk000Sub000Block190Part010

theorem surrogateDiagonalTailChunk000Sub000Block190Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block190Part010CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block190Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block190Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block190Part010CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block190Part010SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block190Part010] using hcert

def TailChunk000Sub000Block190Part011SupportExplicit : Finset ℕ :=
  ([7878] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block190Part011 : ℚ :=
  (40103923 : ℚ) / 3456691200000

def SurrogateDiagonalTailChunk000Sub000Block190Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7878
    = surrogateDiagTailX0RatChunk000Sub000Block190Part011

theorem surrogateDiagonalTailChunk000Sub000Block190Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block190Part011CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block190Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block190Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block190Part011CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block190Part011SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block190Part011] using hcert

def TailChunk000Sub000Block190Part012SupportExplicit : Finset ℕ :=
  ([7879] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block190Part012 : ℚ :=
  (969978765625 : ℚ) / 2407857456694709682

def SurrogateDiagonalTailChunk000Sub000Block190Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7879
    = surrogateDiagTailX0RatChunk000Sub000Block190Part012

theorem surrogateDiagonalTailChunk000Sub000Block190Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block190Part012CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block190Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block190Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block190Part012CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block190Part012SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block190Part012] using hcert

def TailChunk000Sub000Block190Part013SupportExplicit : Finset ℕ :=
  ([7881] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block190Part013 : ℚ :=
  (81916836217 : ℚ) / 64537033081651200

def SurrogateDiagonalTailChunk000Sub000Block190Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7881
    = surrogateDiagTailX0RatChunk000Sub000Block190Part013

theorem surrogateDiagonalTailChunk000Sub000Block190Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block190Part013CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block190Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block190Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block190Part013CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block190Part013SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block190Part013] using hcert

def TailChunk000Sub000Block190Part014SupportExplicit : Finset ℕ :=
  ([7882] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block190Part014 : ℚ :=
  (10706767325 : ℚ) / 2244991136005512

def SurrogateDiagonalTailChunk000Sub000Block190Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7882
    = surrogateDiagTailX0RatChunk000Sub000Block190Part014

theorem surrogateDiagonalTailChunk000Sub000Block190Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block190Part014CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block190Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block190Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block190Part014CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block190Part014SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block190Part014] using hcert

def TailChunk000Sub000Block190Part015SupportExplicit : Finset ℕ :=
  ([7883] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block190Part015 : ℚ :=
  (970963890625 : ℚ) / 2412751474337716722

def SurrogateDiagonalTailChunk000Sub000Block190Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7883
    = surrogateDiagTailX0RatChunk000Sub000Block190Part015

theorem surrogateDiagonalTailChunk000Sub000Block190Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block190Part015CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block190Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block190Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block190Part015CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block190Part015SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block190Part015] using hcert

def TailChunk000Sub000Block190Part016SupportExplicit : Finset ℕ :=
  ([7885] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block190Part016 : ℚ :=
  (2566505709025 : ℚ) / 3038171280930275328

def SurrogateDiagonalTailChunk000Sub000Block190Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7885
    = surrogateDiagTailX0RatChunk000Sub000Block190Part016

theorem surrogateDiagonalTailChunk000Sub000Block190Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block190Part016CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block190Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block190Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block190Part016CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block190Part016SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block190Part016] using hcert

def TailChunk000Sub000Block190Part017SupportExplicit : Finset ℕ :=
  ([7886] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block190Part017 : ℚ :=
  (1943017443775 : ℚ) / 603800319728002248

def SurrogateDiagonalTailChunk000Sub000Block190Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7886
    = surrogateDiagTailX0RatChunk000Sub000Block190Part017

theorem surrogateDiagonalTailChunk000Sub000Block190Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block190Part017CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block190Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block190Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block190Part017CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block190Part017SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block190Part017] using hcert

def TailChunk000Sub000Block190Part018SupportExplicit : Finset ℕ :=
  ([7887] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block190Part018 : ℚ :=
  (25388166033 : ℚ) / 17115650370918400

def SurrogateDiagonalTailChunk000Sub000Block190Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7887
    = surrogateDiagTailX0RatChunk000Sub000Block190Part018

theorem surrogateDiagonalTailChunk000Sub000Block190Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block190Part018CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block190Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block190Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block190Part018CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block190Part018SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block190Part018] using hcert

def TailChunk000Sub000Block190Part019SupportExplicit : Finset ℕ :=
  ([7890] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block190Part019 : ℚ :=
  (204435853675 : ℚ) / 12065129307512832

def SurrogateDiagonalTailChunk000Sub000Block190Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7890
    = surrogateDiagTailX0RatChunk000Sub000Block190Part019

theorem surrogateDiagonalTailChunk000Sub000Block190Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block190Part019CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block190Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block190Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block190Part019CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block190Part019SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block190Part019] using hcert

def TailChunk000Sub000Block190Part020SupportExplicit : Finset ℕ :=
  ([7891] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block190Part020 : ℚ :=
  (433132475 : ℚ) / 16186710258232704

def SurrogateDiagonalTailChunk000Sub000Block190Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7891
    = surrogateDiagTailX0RatChunk000Sub000Block190Part020

theorem surrogateDiagonalTailChunk000Sub000Block190Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block190Part020CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block190Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block190Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block190Part020CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block190Part020SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block190Part020] using hcert

def TailChunk000Sub000Block190Part021SupportExplicit : Finset ℕ :=
  ([7894] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block190Part021 : ℚ :=
  (243418890625 : ℚ) / 151563697352544882

def SurrogateDiagonalTailChunk000Sub000Block190Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7894
    = surrogateDiagTailX0RatChunk000Sub000Block190Part021

theorem surrogateDiagonalTailChunk000Sub000Block190Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block190Part021CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block190Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block190Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block190Part021CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block190Part021SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block190Part021] using hcert

def TailChunk000Sub000Block190Part022SupportExplicit : Finset ℕ :=
  ([7895] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block190Part022 : ℚ :=
  (116988556825 : ℚ) / 992281348915425792

def SurrogateDiagonalTailChunk000Sub000Block190Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7895
    = surrogateDiagTailX0RatChunk000Sub000Block190Part022

theorem surrogateDiagonalTailChunk000Sub000Block190Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block190Part022CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block190Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block190Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block190Part022CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block190Part022SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block190Part022] using hcert

def TailChunk000Sub000Block190Part023SupportExplicit : Finset ℕ :=
  ([7897] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block190Part023 : ℚ :=
  (5216079675 : ℚ) / 730980596441964544

def SurrogateDiagonalTailChunk000Sub000Block190Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7897
    = surrogateDiagTailX0RatChunk000Sub000Block190Part023

theorem surrogateDiagonalTailChunk000Sub000Block190Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block190Part023CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block190Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block190Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block190Part023CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block190Part023SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block190Part023] using hcert

def TailChunk000Sub000Block190Part024SupportExplicit : Finset ℕ :=
  ([7898] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block190Part024 : ℚ :=
  (9084461113 : ℚ) / 4107324024544800

def SurrogateDiagonalTailChunk000Sub000Block190Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7898
    = surrogateDiagTailX0RatChunk000Sub000Block190Part024

theorem surrogateDiagonalTailChunk000Sub000Block190Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block190Part024CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block190Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block190Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block190Part024CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block190Part024SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block190Part024] using hcert

def surrogateDiagonalTailChunk000Sub000Block190HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block190Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block190Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block190Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block190Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block190Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block190Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block190Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block190Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block190Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block190Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block190Head : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block190Part000
    + surrogateDiagTailX0RatChunk000Sub000Block190Part001
    + surrogateDiagTailX0RatChunk000Sub000Block190Part002
    + surrogateDiagTailX0RatChunk000Sub000Block190Part003
    + surrogateDiagTailX0RatChunk000Sub000Block190Part004
    + surrogateDiagTailX0RatChunk000Sub000Block190Part005
    + surrogateDiagTailX0RatChunk000Sub000Block190Part006
    + surrogateDiagTailX0RatChunk000Sub000Block190Part007
    + surrogateDiagTailX0RatChunk000Sub000Block190Part008
    + surrogateDiagTailX0RatChunk000Sub000Block190Part009

def surrogateDiagonalTailChunk000Sub000Block190MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block190Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block190Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block190Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block190Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block190Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block190Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block190Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block190Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block190Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block190Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block190Mid : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block190Part010
    + surrogateDiagTailX0RatChunk000Sub000Block190Part011
    + surrogateDiagTailX0RatChunk000Sub000Block190Part012
    + surrogateDiagTailX0RatChunk000Sub000Block190Part013
    + surrogateDiagTailX0RatChunk000Sub000Block190Part014
    + surrogateDiagTailX0RatChunk000Sub000Block190Part015
    + surrogateDiagTailX0RatChunk000Sub000Block190Part016
    + surrogateDiagTailX0RatChunk000Sub000Block190Part017
    + surrogateDiagTailX0RatChunk000Sub000Block190Part018
    + surrogateDiagTailX0RatChunk000Sub000Block190Part019

def surrogateDiagonalTailChunk000Sub000Block190TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block190Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block190Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block190Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block190Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block190Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block190Tail : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block190Part020
    + surrogateDiagTailX0RatChunk000Sub000Block190Part021
    + surrogateDiagTailX0RatChunk000Sub000Block190Part022
    + surrogateDiagTailX0RatChunk000Sub000Block190Part023
    + surrogateDiagTailX0RatChunk000Sub000Block190Part024

def surrogateDiagonalTailChunk000Sub000Block190Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub000Block190HeadSum X0
    + surrogateDiagonalTailChunk000Sub000Block190MidSum X0
    + surrogateDiagonalTailChunk000Sub000Block190TailSum X0

def surrogateDiagTailX0RatChunk000Sub000Block190 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block190Part000
    + surrogateDiagTailX0RatChunk000Sub000Block190Part001
    + surrogateDiagTailX0RatChunk000Sub000Block190Part002
    + surrogateDiagTailX0RatChunk000Sub000Block190Part003
    + surrogateDiagTailX0RatChunk000Sub000Block190Part004
    + surrogateDiagTailX0RatChunk000Sub000Block190Part005
    + surrogateDiagTailX0RatChunk000Sub000Block190Part006
    + surrogateDiagTailX0RatChunk000Sub000Block190Part007
    + surrogateDiagTailX0RatChunk000Sub000Block190Part008
    + surrogateDiagTailX0RatChunk000Sub000Block190Part009
    + surrogateDiagTailX0RatChunk000Sub000Block190Part010
    + surrogateDiagTailX0RatChunk000Sub000Block190Part011
    + surrogateDiagTailX0RatChunk000Sub000Block190Part012
    + surrogateDiagTailX0RatChunk000Sub000Block190Part013
    + surrogateDiagTailX0RatChunk000Sub000Block190Part014
    + surrogateDiagTailX0RatChunk000Sub000Block190Part015
    + surrogateDiagTailX0RatChunk000Sub000Block190Part016
    + surrogateDiagTailX0RatChunk000Sub000Block190Part017
    + surrogateDiagTailX0RatChunk000Sub000Block190Part018
    + surrogateDiagTailX0RatChunk000Sub000Block190Part019
    + surrogateDiagTailX0RatChunk000Sub000Block190Part020
    + surrogateDiagTailX0RatChunk000Sub000Block190Part021
    + surrogateDiagTailX0RatChunk000Sub000Block190Part022
    + surrogateDiagTailX0RatChunk000Sub000Block190Part023
    + surrogateDiagTailX0RatChunk000Sub000Block190Part024

theorem surrogateDiagTailX0RatChunk000Sub000Block190_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk000Sub000Block190Head + surrogateDiagTailX0RatChunk000Sub000Block190Mid + surrogateDiagTailX0RatChunk000Sub000Block190Tail =
      surrogateDiagTailX0RatChunk000Sub000Block190 := by
  unfold surrogateDiagTailX0RatChunk000Sub000Block190Head surrogateDiagTailX0RatChunk000Sub000Block190Mid surrogateDiagTailX0RatChunk000Sub000Block190Tail surrogateDiagTailX0RatChunk000Sub000Block190
  ring

def SurrogateDiagonalTailChunk000Sub000Block190HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block190HeadSum X0 = surrogateDiagTailX0RatChunk000Sub000Block190Head

def SurrogateDiagonalTailChunk000Sub000Block190MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block190MidSum X0 = surrogateDiagTailX0RatChunk000Sub000Block190Mid

def SurrogateDiagonalTailChunk000Sub000Block190TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block190TailSum X0 = surrogateDiagTailX0RatChunk000Sub000Block190Tail

theorem surrogateDiagonalTailChunk000Sub000Block190_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk000Sub000Block190HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk000Sub000Block190MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk000Sub000Block190TailCertificateAt X0) :
    surrogateDiagonalTailChunk000Sub000Block190Sum X0 = surrogateDiagTailX0RatChunk000Sub000Block190 := by
  unfold SurrogateDiagonalTailChunk000Sub000Block190HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk000Sub000Block190MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk000Sub000Block190TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk000Sub000Block190Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk000Sub000Block190_eq_head_add_mid_add_tail

/-- Block 191 covers tail-support indices [4775,4800) and q from 7899 to 7941. -/

def TailChunk000Sub000Block191Part000SupportExplicit : Finset ℕ :=
  ([7899] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block191Part000 : ℚ :=
  (433189838075 : ℚ) / 959976022328623104

def SurrogateDiagonalTailChunk000Sub000Block191Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7899
    = surrogateDiagTailX0RatChunk000Sub000Block191Part000

theorem surrogateDiagonalTailChunk000Sub000Block191Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block191Part000CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block191Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block191Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block191Part000CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block191Part000SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block191Part000] using hcert

def TailChunk000Sub000Block191Part001SupportExplicit : Finset ℕ :=
  ([7901] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block191Part001 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub000Block191Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7901
    = surrogateDiagTailX0RatChunk000Sub000Block191Part001

theorem surrogateDiagonalTailChunk000Sub000Block191Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block191Part001CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block191Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block191Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block191Part001CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block191Part001SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block191Part001] using hcert

def TailChunk000Sub000Block191Part002SupportExplicit : Finset ℕ :=
  ([7903] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block191Part002 : ℚ :=
  (399176121775 : ℚ) / 5246482867553599488

def SurrogateDiagonalTailChunk000Sub000Block191Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7903
    = surrogateDiagTailX0RatChunk000Sub000Block191Part002

theorem surrogateDiagonalTailChunk000Sub000Block191Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block191Part002CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block191Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block191Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block191Part002CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block191Part002SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block191Part002] using hcert

def TailChunk000Sub000Block191Part003SupportExplicit : Finset ℕ :=
  ([7905] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block191Part003 : ℚ :=
  (3264124813 : ℚ) / 2174762059038720

def SurrogateDiagonalTailChunk000Sub000Block191Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7905
    = surrogateDiagTailX0RatChunk000Sub000Block191Part003

theorem surrogateDiagonalTailChunk000Sub000Block191Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block191Part003CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block191Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block191Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block191Part003CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block191Part003SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block191Part003] using hcert

def TailChunk000Sub000Block191Part004SupportExplicit : Finset ℕ :=
  ([7906] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block191Part004 : ℚ :=
  (106015019375 : ℚ) / 59658463763851392

def SurrogateDiagonalTailChunk000Sub000Block191Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7906
    = surrogateDiagTailX0RatChunk000Sub000Block191Part004

theorem surrogateDiagonalTailChunk000Sub000Block191Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block191Part004CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block191Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block191Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block191Part004CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block191Part004SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block191Part004] using hcert

def TailChunk000Sub000Block191Part005SupportExplicit : Finset ℕ :=
  ([7907] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block191Part005 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub000Block191Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7907
    = surrogateDiagTailX0RatChunk000Sub000Block191Part005

theorem surrogateDiagonalTailChunk000Sub000Block191Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block191Part005CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block191Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block191Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block191Part005CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block191Part005SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block191Part005] using hcert

def TailChunk000Sub000Block191Part006SupportExplicit : Finset ℕ :=
  ([7909] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block191Part006 : ℚ :=
  (3045303723 : ℚ) / 88606049191638400

def SurrogateDiagonalTailChunk000Sub000Block191Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7909
    = surrogateDiagTailX0RatChunk000Sub000Block191Part006

theorem surrogateDiagonalTailChunk000Sub000Block191Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block191Part006CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block191Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block191Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block191Part006CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block191Part006SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block191Part006] using hcert

def TailChunk000Sub000Block191Part007SupportExplicit : Finset ℕ :=
  ([7910] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block191Part007 : ℚ :=
  (724944956125 : ℚ) / 130540092593799168

def SurrogateDiagonalTailChunk000Sub000Block191Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7910
    = surrogateDiagTailX0RatChunk000Sub000Block191Part007

theorem surrogateDiagonalTailChunk000Sub000Block191Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block191Part007CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block191Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block191Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block191Part007CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block191Part007SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block191Part007] using hcert

def TailChunk000Sub000Block191Part008SupportExplicit : Finset ℕ :=
  ([7913] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block191Part008 : ℚ :=
  (480712763 : ℚ) / 57993654907699200

def SurrogateDiagonalTailChunk000Sub000Block191Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7913
    = surrogateDiagTailX0RatChunk000Sub000Block191Part008

theorem surrogateDiagonalTailChunk000Sub000Block191Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block191Part008CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block191Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block191Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block191Part008CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block191Part008SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block191Part008] using hcert

def TailChunk000Sub000Block191Part009SupportExplicit : Finset ℕ :=
  ([7914] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block191Part009 : ℚ :=
  (65204625 : ℚ) / 12070399165504

def SurrogateDiagonalTailChunk000Sub000Block191Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7914
    = surrogateDiagTailX0RatChunk000Sub000Block191Part009

theorem surrogateDiagonalTailChunk000Sub000Block191Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block191Part009CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block191Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block191Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block191Part009CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block191Part009SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block191Part009] using hcert

def TailChunk000Sub000Block191Part010SupportExplicit : Finset ℕ :=
  ([7915] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block191Part010 : ℚ :=
  (104425887525 : ℚ) / 668253882203737088

def SurrogateDiagonalTailChunk000Sub000Block191Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7915
    = surrogateDiagTailX0RatChunk000Sub000Block191Part010

theorem surrogateDiagonalTailChunk000Sub000Block191Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block191Part010CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block191Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block191Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block191Part010CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block191Part010SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block191Part010] using hcert

def TailChunk000Sub000Block191Part011SupportExplicit : Finset ℕ :=
  ([7917] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block191Part011 : ℚ :=
  (115486044025 : ℚ) / 94408459822301184

def SurrogateDiagonalTailChunk000Sub000Block191Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7917
    = surrogateDiagTailX0RatChunk000Sub000Block191Part011

theorem surrogateDiagonalTailChunk000Sub000Block191Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block191Part011CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block191Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block191Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block191Part011CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block191Part011SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block191Part011] using hcert

def TailChunk000Sub000Block191Part012SupportExplicit : Finset ℕ :=
  ([7918] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block191Part012 : ℚ :=
  (476875656875 : ℚ) / 265112574618461184

def SurrogateDiagonalTailChunk000Sub000Block191Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7918
    = surrogateDiagTailX0RatChunk000Sub000Block191Part012

theorem surrogateDiagonalTailChunk000Sub000Block191Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block191Part012CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block191Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block191Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block191Part012CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block191Part012SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block191Part012] using hcert

def TailChunk000Sub000Block191Part013SupportExplicit : Finset ℕ :=
  ([7919] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block191Part013 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub000Block191Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7919
    = surrogateDiagTailX0RatChunk000Sub000Block191Part013

theorem surrogateDiagonalTailChunk000Sub000Block191Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block191Part013CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block191Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block191Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block191Part013CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block191Part013SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block191Part013] using hcert

def TailChunk000Sub000Block191Part014SupportExplicit : Finset ℕ :=
  ([7922] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block191Part014 : ℚ :=
  (936979358725 : ℚ) / 474743174036717568

def SurrogateDiagonalTailChunk000Sub000Block191Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7922
    = surrogateDiagTailX0RatChunk000Sub000Block191Part014

theorem surrogateDiagonalTailChunk000Sub000Block191Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block191Part014CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block191Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block191Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block191Part014CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block191Part014SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block191Part014] using hcert

def TailChunk000Sub000Block191Part015SupportExplicit : Finset ℕ :=
  ([7923] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block191Part015 : ℚ :=
  (8015189525 : ℚ) / 14103582784206336

def SurrogateDiagonalTailChunk000Sub000Block191Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7923
    = surrogateDiagTailX0RatChunk000Sub000Block191Part015

theorem surrogateDiagonalTailChunk000Sub000Block191Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block191Part015CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block191Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block191Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block191Part015CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block191Part015SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block191Part015] using hcert

def TailChunk000Sub000Block191Part016SupportExplicit : Finset ℕ :=
  ([7926] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block191Part016 : ℚ :=
  (30522218377 : ℚ) / 4858503922483200

def SurrogateDiagonalTailChunk000Sub000Block191Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7926
    = surrogateDiagTailX0RatChunk000Sub000Block191Part016

theorem surrogateDiagonalTailChunk000Sub000Block191Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block191Part016CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block191Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block191Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block191Part016CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block191Part016SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block191Part016] using hcert

def TailChunk000Sub000Block191Part017SupportExplicit : Finset ℕ :=
  ([7927] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block191Part017 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub000Block191Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7927
    = surrogateDiagTailX0RatChunk000Sub000Block191Part017

theorem surrogateDiagonalTailChunk000Sub000Block191Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block191Part017CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block191Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block191Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block191Part017CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block191Part017SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block191Part017] using hcert

def TailChunk000Sub000Block191Part018SupportExplicit : Finset ℕ :=
  ([7930] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block191Part018 : ℚ :=
  (30523158511 : ℚ) / 6881083077427200

def SurrogateDiagonalTailChunk000Sub000Block191Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7930
    = surrogateDiagTailX0RatChunk000Sub000Block191Part018

theorem surrogateDiagonalTailChunk000Sub000Block191Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block191Part018CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block191Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block191Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block191Part018CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block191Part018SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block191Part018] using hcert

def TailChunk000Sub000Block191Part019SupportExplicit : Finset ℕ :=
  ([7931] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block191Part019 : ℚ :=
  (3110466407 : ℚ) / 23385210762931200

def SurrogateDiagonalTailChunk000Sub000Block191Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7931
    = surrogateDiagTailX0RatChunk000Sub000Block191Part019

theorem surrogateDiagonalTailChunk000Sub000Block191Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block191Part019CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block191Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block191Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block191Part019CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block191Part019SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block191Part019] using hcert

def TailChunk000Sub000Block191Part020SupportExplicit : Finset ℕ :=
  ([7933] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block191Part020 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub000Block191Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7933
    = surrogateDiagTailX0RatChunk000Sub000Block191Part020

theorem surrogateDiagonalTailChunk000Sub000Block191Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block191Part020CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block191Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block191Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block191Part020CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block191Part020SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block191Part020] using hcert

def TailChunk000Sub000Block191Part021SupportExplicit : Finset ℕ :=
  ([7934] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block191Part021 : ℚ :=
  (245892015625 : ℚ) / 154659893588769042

def SurrogateDiagonalTailChunk000Sub000Block191Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7934
    = surrogateDiagTailX0RatChunk000Sub000Block191Part021

theorem surrogateDiagonalTailChunk000Sub000Block191Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block191Part021CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block191Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block191Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block191Part021CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block191Part021SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block191Part021] using hcert

def TailChunk000Sub000Block191Part022SupportExplicit : Finset ℕ :=
  ([7937] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block191Part022 : ℚ :=
  (984312015625 : ℚ) / 2479553619167281152

def SurrogateDiagonalTailChunk000Sub000Block191Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7937
    = surrogateDiagTailX0RatChunk000Sub000Block191Part022

theorem surrogateDiagonalTailChunk000Sub000Block191Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block191Part022CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block191Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block191Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block191Part022CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block191Part022SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block191Part022] using hcert

def TailChunk000Sub000Block191Part023SupportExplicit : Finset ℕ :=
  ([7939] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block191Part023 : ℚ :=
  (150659364675 : ℚ) / 321987650093514752

def SurrogateDiagonalTailChunk000Sub000Block191Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7939
    = surrogateDiagTailX0RatChunk000Sub000Block191Part023

theorem surrogateDiagonalTailChunk000Sub000Block191Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block191Part023CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block191Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block191Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block191Part023CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block191Part023SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block191Part023] using hcert

def TailChunk000Sub000Block191Part024SupportExplicit : Finset ℕ :=
  ([7941] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block191Part024 : ℚ :=
  (547221546775 : ℚ) / 490282294170023712

def SurrogateDiagonalTailChunk000Sub000Block191Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7941
    = surrogateDiagTailX0RatChunk000Sub000Block191Part024

theorem surrogateDiagonalTailChunk000Sub000Block191Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block191Part024CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block191Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block191Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block191Part024CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block191Part024SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block191Part024] using hcert

def surrogateDiagonalTailChunk000Sub000Block191HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block191Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block191Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block191Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block191Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block191Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block191Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block191Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block191Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block191Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block191Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block191Head : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block191Part000
    + surrogateDiagTailX0RatChunk000Sub000Block191Part001
    + surrogateDiagTailX0RatChunk000Sub000Block191Part002
    + surrogateDiagTailX0RatChunk000Sub000Block191Part003
    + surrogateDiagTailX0RatChunk000Sub000Block191Part004
    + surrogateDiagTailX0RatChunk000Sub000Block191Part005
    + surrogateDiagTailX0RatChunk000Sub000Block191Part006
    + surrogateDiagTailX0RatChunk000Sub000Block191Part007
    + surrogateDiagTailX0RatChunk000Sub000Block191Part008
    + surrogateDiagTailX0RatChunk000Sub000Block191Part009

def surrogateDiagonalTailChunk000Sub000Block191MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block191Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block191Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block191Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block191Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block191Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block191Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block191Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block191Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block191Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block191Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block191Mid : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block191Part010
    + surrogateDiagTailX0RatChunk000Sub000Block191Part011
    + surrogateDiagTailX0RatChunk000Sub000Block191Part012
    + surrogateDiagTailX0RatChunk000Sub000Block191Part013
    + surrogateDiagTailX0RatChunk000Sub000Block191Part014
    + surrogateDiagTailX0RatChunk000Sub000Block191Part015
    + surrogateDiagTailX0RatChunk000Sub000Block191Part016
    + surrogateDiagTailX0RatChunk000Sub000Block191Part017
    + surrogateDiagTailX0RatChunk000Sub000Block191Part018
    + surrogateDiagTailX0RatChunk000Sub000Block191Part019

def surrogateDiagonalTailChunk000Sub000Block191TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block191Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block191Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block191Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block191Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block191Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block191Tail : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block191Part020
    + surrogateDiagTailX0RatChunk000Sub000Block191Part021
    + surrogateDiagTailX0RatChunk000Sub000Block191Part022
    + surrogateDiagTailX0RatChunk000Sub000Block191Part023
    + surrogateDiagTailX0RatChunk000Sub000Block191Part024

def surrogateDiagonalTailChunk000Sub000Block191Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub000Block191HeadSum X0
    + surrogateDiagonalTailChunk000Sub000Block191MidSum X0
    + surrogateDiagonalTailChunk000Sub000Block191TailSum X0

def surrogateDiagTailX0RatChunk000Sub000Block191 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block191Part000
    + surrogateDiagTailX0RatChunk000Sub000Block191Part001
    + surrogateDiagTailX0RatChunk000Sub000Block191Part002
    + surrogateDiagTailX0RatChunk000Sub000Block191Part003
    + surrogateDiagTailX0RatChunk000Sub000Block191Part004
    + surrogateDiagTailX0RatChunk000Sub000Block191Part005
    + surrogateDiagTailX0RatChunk000Sub000Block191Part006
    + surrogateDiagTailX0RatChunk000Sub000Block191Part007
    + surrogateDiagTailX0RatChunk000Sub000Block191Part008
    + surrogateDiagTailX0RatChunk000Sub000Block191Part009
    + surrogateDiagTailX0RatChunk000Sub000Block191Part010
    + surrogateDiagTailX0RatChunk000Sub000Block191Part011
    + surrogateDiagTailX0RatChunk000Sub000Block191Part012
    + surrogateDiagTailX0RatChunk000Sub000Block191Part013
    + surrogateDiagTailX0RatChunk000Sub000Block191Part014
    + surrogateDiagTailX0RatChunk000Sub000Block191Part015
    + surrogateDiagTailX0RatChunk000Sub000Block191Part016
    + surrogateDiagTailX0RatChunk000Sub000Block191Part017
    + surrogateDiagTailX0RatChunk000Sub000Block191Part018
    + surrogateDiagTailX0RatChunk000Sub000Block191Part019
    + surrogateDiagTailX0RatChunk000Sub000Block191Part020
    + surrogateDiagTailX0RatChunk000Sub000Block191Part021
    + surrogateDiagTailX0RatChunk000Sub000Block191Part022
    + surrogateDiagTailX0RatChunk000Sub000Block191Part023
    + surrogateDiagTailX0RatChunk000Sub000Block191Part024

theorem surrogateDiagTailX0RatChunk000Sub000Block191_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk000Sub000Block191Head + surrogateDiagTailX0RatChunk000Sub000Block191Mid + surrogateDiagTailX0RatChunk000Sub000Block191Tail =
      surrogateDiagTailX0RatChunk000Sub000Block191 := by
  unfold surrogateDiagTailX0RatChunk000Sub000Block191Head surrogateDiagTailX0RatChunk000Sub000Block191Mid surrogateDiagTailX0RatChunk000Sub000Block191Tail surrogateDiagTailX0RatChunk000Sub000Block191
  ring

def SurrogateDiagonalTailChunk000Sub000Block191HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block191HeadSum X0 = surrogateDiagTailX0RatChunk000Sub000Block191Head

def SurrogateDiagonalTailChunk000Sub000Block191MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block191MidSum X0 = surrogateDiagTailX0RatChunk000Sub000Block191Mid

def SurrogateDiagonalTailChunk000Sub000Block191TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block191TailSum X0 = surrogateDiagTailX0RatChunk000Sub000Block191Tail

theorem surrogateDiagonalTailChunk000Sub000Block191_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk000Sub000Block191HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk000Sub000Block191MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk000Sub000Block191TailCertificateAt X0) :
    surrogateDiagonalTailChunk000Sub000Block191Sum X0 = surrogateDiagTailX0RatChunk000Sub000Block191 := by
  unfold SurrogateDiagonalTailChunk000Sub000Block191HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk000Sub000Block191MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk000Sub000Block191TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk000Sub000Block191Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk000Sub000Block191_eq_head_add_mid_add_tail

/-- Block 192 covers tail-support indices [4800,4825) and q from 7945 to 7985. -/

def TailChunk000Sub000Block192Part000SupportExplicit : Finset ℕ :=
  ([7945] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block192Part000 : ℚ :=
  (570158502625 : ℚ) / 541060202833846272

def SurrogateDiagonalTailChunk000Sub000Block192Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7945
    = surrogateDiagTailX0RatChunk000Sub000Block192Part000

theorem surrogateDiagonalTailChunk000Sub000Block192Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block192Part000CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block192Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block192Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block192Part000CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block192Part000SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block192Part000] using hcert

def TailChunk000Sub000Block192Part001SupportExplicit : Finset ℕ :=
  ([7946] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block192Part001 : ℚ :=
  (109527386075 : ℚ) / 30928987023212544

def SurrogateDiagonalTailChunk000Sub000Block192Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7946
    = surrogateDiagTailX0RatChunk000Sub000Block192Part001

theorem surrogateDiagonalTailChunk000Sub000Block192Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block192Part001CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block192Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block192Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block192Part001CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block192Part001SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block192Part001] using hcert

def TailChunk000Sub000Block192Part002SupportExplicit : Finset ℕ :=
  ([7949] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block192Part002 : ℚ :=
  (987290640625 : ℚ) / 2494584969640241952

def SurrogateDiagonalTailChunk000Sub000Block192Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7949
    = surrogateDiagTailX0RatChunk000Sub000Block192Part002

theorem surrogateDiagonalTailChunk000Sub000Block192Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block192Part002CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block192Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block192Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block192Part002CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block192Part002SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block192Part002] using hcert

def TailChunk000Sub000Block192Part003SupportExplicit : Finset ℕ :=
  ([7951] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block192Part003 : ℚ :=
  (63218401 : ℚ) / 159814196698050

def SurrogateDiagonalTailChunk000Sub000Block192Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7951
    = surrogateDiagTailX0RatChunk000Sub000Block192Part003

theorem surrogateDiagonalTailChunk000Sub000Block192Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block192Part003CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block192Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block192Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block192Part003CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block192Part003SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block192Part003] using hcert

def TailChunk000Sub000Block192Part004SupportExplicit : Finset ℕ :=
  ([7953] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block192Part004 : ℚ :=
  (2873672801 : ℚ) / 1966473216000000

def SurrogateDiagonalTailChunk000Sub000Block192Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7953
    = surrogateDiagTailX0RatChunk000Sub000Block192Part004

theorem surrogateDiagonalTailChunk000Sub000Block192Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block192Part004CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block192Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block192Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block192Part004CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block192Part004SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block192Part004] using hcert

def TailChunk000Sub000Block192Part005SupportExplicit : Finset ℕ :=
  ([7954] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block192Part005 : ℚ :=
  (1284741557 : ℚ) / 724920686346240

def SurrogateDiagonalTailChunk000Sub000Block192Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7954
    = surrogateDiagTailX0RatChunk000Sub000Block192Part005

theorem surrogateDiagonalTailChunk000Sub000Block192Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block192Part005CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block192Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block192Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block192Part005CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block192Part005SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block192Part005] using hcert

def TailChunk000Sub000Block192Part006SupportExplicit : Finset ℕ :=
  ([7955] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block192Part006 : ℚ :=
  (95169055075 : ℚ) / 119485706962599936

def SurrogateDiagonalTailChunk000Sub000Block192Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7955
    = surrogateDiagTailX0RatChunk000Sub000Block192Part006

theorem surrogateDiagonalTailChunk000Sub000Block192Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block192Part006CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block192Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block192Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block192Part006CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block192Part006SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block192Part006] using hcert

def TailChunk000Sub000Block192Part007SupportExplicit : Finset ℕ :=
  ([7957] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block192Part007 : ℚ :=
  (958652571475 : ℚ) / 2285556044844367872

def SurrogateDiagonalTailChunk000Sub000Block192Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7957
    = surrogateDiagTailX0RatChunk000Sub000Block192Part007

theorem surrogateDiagonalTailChunk000Sub000Block192Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block192Part007CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block192Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block192Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block192Part007CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block192Part007SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block192Part007] using hcert

def TailChunk000Sub000Block192Part008SupportExplicit : Finset ℕ :=
  ([7958] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block192Part008 : ℚ :=
  (476848372025 : ℚ) / 256331143035331584

def SurrogateDiagonalTailChunk000Sub000Block192Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7958
    = surrogateDiagTailX0RatChunk000Sub000Block192Part008

theorem surrogateDiagonalTailChunk000Sub000Block192Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block192Part008CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block192Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block192Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block192Part008CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block192Part008SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block192Part008] using hcert

def TailChunk000Sub000Block192Part009SupportExplicit : Finset ℕ :=
  ([7959] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block192Part009 : ℚ :=
  (259556480725 : ℚ) / 151224097874540544

def SurrogateDiagonalTailChunk000Sub000Block192Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7959
    = surrogateDiagTailX0RatChunk000Sub000Block192Part009

theorem surrogateDiagonalTailChunk000Sub000Block192Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block192Part009CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block192Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block192Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block192Part009CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block192Part009SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block192Part009] using hcert

def TailChunk000Sub000Block192Part010SupportExplicit : Finset ℕ :=
  ([7961] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block192Part010 : ℚ :=
  (1221503213275 : ℚ) / 2671165222095655296

def SurrogateDiagonalTailChunk000Sub000Block192Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7961
    = surrogateDiagTailX0RatChunk000Sub000Block192Part010

theorem surrogateDiagonalTailChunk000Sub000Block192Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block192Part010CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block192Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block192Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block192Part010CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block192Part010SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block192Part010] using hcert

def TailChunk000Sub000Block192Part011SupportExplicit : Finset ℕ :=
  ([7962] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block192Part011 : ℚ :=
  (770002399975 : ℚ) / 123686111962977408

def SurrogateDiagonalTailChunk000Sub000Block192Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7962
    = surrogateDiagTailX0RatChunk000Sub000Block192Part011

theorem surrogateDiagonalTailChunk000Sub000Block192Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block192Part011CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block192Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block192Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block192Part011CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block192Part011SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block192Part011] using hcert

def TailChunk000Sub000Block192Part012SupportExplicit : Finset ℕ :=
  ([7963] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block192Part012 : ℚ :=
  (990771390625 : ℚ) / 2512207804955982642

def SurrogateDiagonalTailChunk000Sub000Block192Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7963
    = surrogateDiagTailX0RatChunk000Sub000Block192Part012

theorem surrogateDiagonalTailChunk000Sub000Block192Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block192Part012CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block192Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block192Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block192Part012CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block192Part012SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block192Part012] using hcert

def TailChunk000Sub000Block192Part013SupportExplicit : Finset ℕ :=
  ([7966] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block192Part013 : ℚ :=
  (889249402225 : ℚ) / 337306882905243648

def SurrogateDiagonalTailChunk000Sub000Block192Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7966
    = surrogateDiagTailX0RatChunk000Sub000Block192Part013

theorem surrogateDiagonalTailChunk000Sub000Block192Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block192Part013CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block192Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block192Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block192Part013CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block192Part013SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block192Part013] using hcert

def TailChunk000Sub000Block192Part014SupportExplicit : Finset ℕ :=
  ([7967] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block192Part014 : ℚ :=
  (150802544017 : ℚ) / 347961929446195200

def SurrogateDiagonalTailChunk000Sub000Block192Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7967
    = surrogateDiagTailX0RatChunk000Sub000Block192Part014

theorem surrogateDiagonalTailChunk000Sub000Block192Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block192Part014CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block192Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block192Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block192Part014CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block192Part014SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block192Part014] using hcert

def TailChunk000Sub000Block192Part015SupportExplicit : Finset ℕ :=
  ([7969] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block192Part015 : ℚ :=
  (27649169075 : ℚ) / 56826062153922816

def SurrogateDiagonalTailChunk000Sub000Block192Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7969
    = surrogateDiagTailX0RatChunk000Sub000Block192Part015

theorem surrogateDiagonalTailChunk000Sub000Block192Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block192Part015CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block192Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block192Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block192Part015CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block192Part015SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block192Part015] using hcert

def TailChunk000Sub000Block192Part016SupportExplicit : Finset ℕ :=
  ([7970] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block192Part016 : ℚ :=
  (277676413875 : ℚ) / 85663899584659456

def SurrogateDiagonalTailChunk000Sub000Block192Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7970
    = surrogateDiagTailX0RatChunk000Sub000Block192Part016

theorem surrogateDiagonalTailChunk000Sub000Block192Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block192Part016CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block192Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block192Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block192Part016CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block192Part016SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block192Part016] using hcert

def TailChunk000Sub000Block192Part017SupportExplicit : Finset ℕ :=
  ([7971] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block192Part017 : ℚ :=
  (1102728793925 : ℚ) / 995472182643523584

def SurrogateDiagonalTailChunk000Sub000Block192Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7971
    = surrogateDiagTailX0RatChunk000Sub000Block192Part017

theorem surrogateDiagonalTailChunk000Sub000Block192Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block192Part017CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block192Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block192Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block192Part017CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block192Part017SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block192Part017] using hcert

def TailChunk000Sub000Block192Part018SupportExplicit : Finset ℕ :=
  ([7973] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block192Part018 : ℚ :=
  (974159873275 : ℚ) / 1343279164488155136

def SurrogateDiagonalTailChunk000Sub000Block192Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7973
    = surrogateDiagTailX0RatChunk000Sub000Block192Part018

theorem surrogateDiagonalTailChunk000Sub000Block192Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block192Part018CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block192Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block192Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block192Part018CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block192Part018SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block192Part018] using hcert

def TailChunk000Sub000Block192Part019SupportExplicit : Finset ℕ :=
  ([7977] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block192Part019 : ℚ :=
  (1766865734125 : ℚ) / 1996947962582410368

def SurrogateDiagonalTailChunk000Sub000Block192Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7977
    = surrogateDiagTailX0RatChunk000Sub000Block192Part019

theorem surrogateDiagonalTailChunk000Sub000Block192Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block192Part019CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block192Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block192Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block192Part019CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block192Part019SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block192Part019] using hcert

def TailChunk000Sub000Block192Part020SupportExplicit : Finset ℕ :=
  ([7978] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block192Part020 : ℚ :=
  (248626890625 : ℚ) / 158120240457506592

def SurrogateDiagonalTailChunk000Sub000Block192Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7978
    = surrogateDiagTailX0RatChunk000Sub000Block192Part020

theorem surrogateDiagonalTailChunk000Sub000Block192Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block192Part020CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block192Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block192Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block192Part020CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block192Part020SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block192Part020] using hcert

def TailChunk000Sub000Block192Part021SupportExplicit : Finset ℕ :=
  ([7979] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block192Part021 : ℚ :=
  (38576684611 : ℚ) / 92556147528000000

def SurrogateDiagonalTailChunk000Sub000Block192Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7979
    = surrogateDiagTailX0RatChunk000Sub000Block192Part021

theorem surrogateDiagonalTailChunk000Sub000Block192Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block192Part021CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block192Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block192Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block192Part021CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block192Part021SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block192Part021] using hcert

def TailChunk000Sub000Block192Part022SupportExplicit : Finset ℕ :=
  ([7981] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block192Part022 : ℚ :=
  (3733642201075 : ℚ) / 8395024682182435968

def SurrogateDiagonalTailChunk000Sub000Block192Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7981
    = surrogateDiagTailX0RatChunk000Sub000Block192Part022

theorem surrogateDiagonalTailChunk000Sub000Block192Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block192Part022CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block192Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block192Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block192Part022CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block192Part022SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block192Part022] using hcert

def TailChunk000Sub000Block192Part023SupportExplicit : Finset ℕ :=
  ([7982] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block192Part023 : ℚ :=
  (467213733725 : ℚ) / 227304248615691264

def SurrogateDiagonalTailChunk000Sub000Block192Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7982
    = surrogateDiagTailX0RatChunk000Sub000Block192Part023

theorem surrogateDiagonalTailChunk000Sub000Block192Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block192Part023CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block192Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block192Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block192Part023CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block192Part023SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block192Part023] using hcert

def TailChunk000Sub000Block192Part024SupportExplicit : Finset ℕ :=
  ([7985] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block192Part024 : ℚ :=
  (409616292475 : ℚ) / 593335498288103424

def SurrogateDiagonalTailChunk000Sub000Block192Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7985
    = surrogateDiagTailX0RatChunk000Sub000Block192Part024

theorem surrogateDiagonalTailChunk000Sub000Block192Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block192Part024CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block192Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block192Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block192Part024CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block192Part024SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block192Part024] using hcert

def surrogateDiagonalTailChunk000Sub000Block192HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block192Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block192Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block192Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block192Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block192Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block192Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block192Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block192Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block192Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block192Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block192Head : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block192Part000
    + surrogateDiagTailX0RatChunk000Sub000Block192Part001
    + surrogateDiagTailX0RatChunk000Sub000Block192Part002
    + surrogateDiagTailX0RatChunk000Sub000Block192Part003
    + surrogateDiagTailX0RatChunk000Sub000Block192Part004
    + surrogateDiagTailX0RatChunk000Sub000Block192Part005
    + surrogateDiagTailX0RatChunk000Sub000Block192Part006
    + surrogateDiagTailX0RatChunk000Sub000Block192Part007
    + surrogateDiagTailX0RatChunk000Sub000Block192Part008
    + surrogateDiagTailX0RatChunk000Sub000Block192Part009

def surrogateDiagonalTailChunk000Sub000Block192MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block192Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block192Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block192Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block192Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block192Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block192Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block192Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block192Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block192Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block192Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block192Mid : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block192Part010
    + surrogateDiagTailX0RatChunk000Sub000Block192Part011
    + surrogateDiagTailX0RatChunk000Sub000Block192Part012
    + surrogateDiagTailX0RatChunk000Sub000Block192Part013
    + surrogateDiagTailX0RatChunk000Sub000Block192Part014
    + surrogateDiagTailX0RatChunk000Sub000Block192Part015
    + surrogateDiagTailX0RatChunk000Sub000Block192Part016
    + surrogateDiagTailX0RatChunk000Sub000Block192Part017
    + surrogateDiagTailX0RatChunk000Sub000Block192Part018
    + surrogateDiagTailX0RatChunk000Sub000Block192Part019

def surrogateDiagonalTailChunk000Sub000Block192TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block192Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block192Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block192Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block192Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block192Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block192Tail : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block192Part020
    + surrogateDiagTailX0RatChunk000Sub000Block192Part021
    + surrogateDiagTailX0RatChunk000Sub000Block192Part022
    + surrogateDiagTailX0RatChunk000Sub000Block192Part023
    + surrogateDiagTailX0RatChunk000Sub000Block192Part024

def surrogateDiagonalTailChunk000Sub000Block192Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub000Block192HeadSum X0
    + surrogateDiagonalTailChunk000Sub000Block192MidSum X0
    + surrogateDiagonalTailChunk000Sub000Block192TailSum X0

def surrogateDiagTailX0RatChunk000Sub000Block192 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block192Part000
    + surrogateDiagTailX0RatChunk000Sub000Block192Part001
    + surrogateDiagTailX0RatChunk000Sub000Block192Part002
    + surrogateDiagTailX0RatChunk000Sub000Block192Part003
    + surrogateDiagTailX0RatChunk000Sub000Block192Part004
    + surrogateDiagTailX0RatChunk000Sub000Block192Part005
    + surrogateDiagTailX0RatChunk000Sub000Block192Part006
    + surrogateDiagTailX0RatChunk000Sub000Block192Part007
    + surrogateDiagTailX0RatChunk000Sub000Block192Part008
    + surrogateDiagTailX0RatChunk000Sub000Block192Part009
    + surrogateDiagTailX0RatChunk000Sub000Block192Part010
    + surrogateDiagTailX0RatChunk000Sub000Block192Part011
    + surrogateDiagTailX0RatChunk000Sub000Block192Part012
    + surrogateDiagTailX0RatChunk000Sub000Block192Part013
    + surrogateDiagTailX0RatChunk000Sub000Block192Part014
    + surrogateDiagTailX0RatChunk000Sub000Block192Part015
    + surrogateDiagTailX0RatChunk000Sub000Block192Part016
    + surrogateDiagTailX0RatChunk000Sub000Block192Part017
    + surrogateDiagTailX0RatChunk000Sub000Block192Part018
    + surrogateDiagTailX0RatChunk000Sub000Block192Part019
    + surrogateDiagTailX0RatChunk000Sub000Block192Part020
    + surrogateDiagTailX0RatChunk000Sub000Block192Part021
    + surrogateDiagTailX0RatChunk000Sub000Block192Part022
    + surrogateDiagTailX0RatChunk000Sub000Block192Part023
    + surrogateDiagTailX0RatChunk000Sub000Block192Part024

theorem surrogateDiagTailX0RatChunk000Sub000Block192_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk000Sub000Block192Head + surrogateDiagTailX0RatChunk000Sub000Block192Mid + surrogateDiagTailX0RatChunk000Sub000Block192Tail =
      surrogateDiagTailX0RatChunk000Sub000Block192 := by
  unfold surrogateDiagTailX0RatChunk000Sub000Block192Head surrogateDiagTailX0RatChunk000Sub000Block192Mid surrogateDiagTailX0RatChunk000Sub000Block192Tail surrogateDiagTailX0RatChunk000Sub000Block192
  ring

def SurrogateDiagonalTailChunk000Sub000Block192HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block192HeadSum X0 = surrogateDiagTailX0RatChunk000Sub000Block192Head

def SurrogateDiagonalTailChunk000Sub000Block192MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block192MidSum X0 = surrogateDiagTailX0RatChunk000Sub000Block192Mid

def SurrogateDiagonalTailChunk000Sub000Block192TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block192TailSum X0 = surrogateDiagTailX0RatChunk000Sub000Block192Tail

theorem surrogateDiagonalTailChunk000Sub000Block192_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk000Sub000Block192HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk000Sub000Block192MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk000Sub000Block192TailCertificateAt X0) :
    surrogateDiagonalTailChunk000Sub000Block192Sum X0 = surrogateDiagTailX0RatChunk000Sub000Block192 := by
  unfold SurrogateDiagonalTailChunk000Sub000Block192HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk000Sub000Block192MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk000Sub000Block192TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk000Sub000Block192Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk000Sub000Block192_eq_head_add_mid_add_tail

/-- Block 193 covers tail-support indices [4825,4850) and q from 7989 to 8026. -/

def TailChunk000Sub000Block193Part000SupportExplicit : Finset ℕ :=
  ([7989] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block193Part000 : ℚ :=
  (553857608275 : ℚ) / 502248969983415072

def SurrogateDiagonalTailChunk000Sub000Block193Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7989
    = surrogateDiagTailX0RatChunk000Sub000Block193Part000

theorem surrogateDiagonalTailChunk000Sub000Block193Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block193Part000CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block193Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block193Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block193Part000CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block193Part000SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block193Part000] using hcert

def TailChunk000Sub000Block193Part001SupportExplicit : Finset ℕ :=
  ([7990] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block193Part001 : ℚ :=
  (817397001625 : ℚ) / 187835675729461248

def SurrogateDiagonalTailChunk000Sub000Block193Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7990
    = surrogateDiagTailX0RatChunk000Sub000Block193Part001

theorem surrogateDiagonalTailChunk000Sub000Block193Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block193Part001CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block193Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block193Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block193Part001CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block193Part001SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block193Part001] using hcert

def TailChunk000Sub000Block193Part002SupportExplicit : Finset ℕ :=
  ([7991] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block193Part002 : ℚ :=
  (51476933273 : ℚ) / 123408196704000000

def SurrogateDiagonalTailChunk000Sub000Block193Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7991
    = surrogateDiagTailX0RatChunk000Sub000Block193Part002

theorem surrogateDiagonalTailChunk000Sub000Block193Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block193Part002CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block193Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block193Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block193Part002CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block193Part002SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block193Part002] using hcert

def TailChunk000Sub000Block193Part003SupportExplicit : Finset ℕ :=
  ([7993] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block193Part003 : ℚ :=
  (998250765625 : ℚ) / 2550285304832512512

def SurrogateDiagonalTailChunk000Sub000Block193Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7993
    = surrogateDiagTailX0RatChunk000Sub000Block193Part003

theorem surrogateDiagonalTailChunk000Sub000Block193Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block193Part003CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block193Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block193Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block193Part003CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block193Part003SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block193Part003] using hcert

def TailChunk000Sub000Block193Part004SupportExplicit : Finset ℕ :=
  ([7994] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block193Part004 : ℚ :=
  (35820381613 : ℚ) / 13683313411459200

def SurrogateDiagonalTailChunk000Sub000Block193Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7994
    = surrogateDiagTailX0RatChunk000Sub000Block193Part004

theorem surrogateDiagonalTailChunk000Sub000Block193Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block193Part004CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block193Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block193Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block193Part004CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block193Part004SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block193Part004] using hcert

def TailChunk000Sub000Block193Part005SupportExplicit : Finset ℕ :=
  ([7995] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block193Part005 : ℚ :=
  (7275798953 : ℚ) / 2718452573798400

def SurrogateDiagonalTailChunk000Sub000Block193Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7995
    = surrogateDiagTailX0RatChunk000Sub000Block193Part005

theorem surrogateDiagonalTailChunk000Sub000Block193Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block193Part005CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block193Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block193Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block193Part005CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block193Part005SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block193Part005] using hcert

def TailChunk000Sub000Block193Part006SupportExplicit : Finset ℕ :=
  ([7997] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block193Part006 : ℚ :=
  (423708283 : ℚ) / 842014156357440

def SurrogateDiagonalTailChunk000Sub000Block193Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7997
    = surrogateDiagTailX0RatChunk000Sub000Block193Part006

theorem surrogateDiagonalTailChunk000Sub000Block193Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block193Part006CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block193Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block193Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block193Part006CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block193Part006SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block193Part006] using hcert

def TailChunk000Sub000Block193Part007SupportExplicit : Finset ℕ :=
  ([7998] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block193Part007 : ℚ :=
  (25561468291 : ℚ) / 4033564567603200

def SurrogateDiagonalTailChunk000Sub000Block193Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7998
    = surrogateDiagTailX0RatChunk000Sub000Block193Part007

theorem surrogateDiagonalTailChunk000Sub000Block193Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block193Part007CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block193Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block193Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block193Part007CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block193Part007SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block193Part007] using hcert

def TailChunk000Sub000Block193Part008SupportExplicit : Finset ℕ :=
  ([7999] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block193Part008 : ℚ :=
  (147984275107 : ℚ) / 326718729975859200

def SurrogateDiagonalTailChunk000Sub000Block193Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7999
    = surrogateDiagTailX0RatChunk000Sub000Block193Part008

theorem surrogateDiagonalTailChunk000Sub000Block193Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block193Part008CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block193Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block193Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block193Part008CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block193Part008SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block193Part008] using hcert

def TailChunk000Sub000Block193Part009SupportExplicit : Finset ℕ :=
  ([8002] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block193Part009 : ℚ :=
  (80023996999 : ℚ) / 25605120000000000

def SurrogateDiagonalTailChunk000Sub000Block193Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8002
    = surrogateDiagTailX0RatChunk000Sub000Block193Part009

theorem surrogateDiagonalTailChunk000Sub000Block193Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block193Part009CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block193Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block193Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block193Part009CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block193Part009SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block193Part009] using hcert

def TailChunk000Sub000Block193Part010SupportExplicit : Finset ℕ :=
  ([8003] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block193Part010 : ℚ :=
  (154574076427 : ℚ) / 370224590112000000

def SurrogateDiagonalTailChunk000Sub000Block193Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8003
    = surrogateDiagTailX0RatChunk000Sub000Block193Part010

theorem surrogateDiagonalTailChunk000Sub000Block193Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block193Part010CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block193Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block193Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block193Part010CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block193Part010SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block193Part010] using hcert

def TailChunk000Sub000Block193Part011SupportExplicit : Finset ℕ :=
  ([8005] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block193Part011 : ℚ :=
  (38422643799 : ℚ) / 55935238144000000

def SurrogateDiagonalTailChunk000Sub000Block193Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8005
    = surrogateDiagTailX0RatChunk000Sub000Block193Part011

theorem surrogateDiagonalTailChunk000Sub000Block193Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block193Part011CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block193Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block193Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block193Part011CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block193Part011SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block193Part011] using hcert

def TailChunk000Sub000Block193Part012SupportExplicit : Finset ℕ :=
  ([8006] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block193Part012 : ℚ :=
  (2002600524775 : ℚ) / 641409216512104008

def SurrogateDiagonalTailChunk000Sub000Block193Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8006
    = surrogateDiagTailX0RatChunk000Sub000Block193Part012

theorem surrogateDiagonalTailChunk000Sub000Block193Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block193Part012CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block193Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block193Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block193Part012CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block193Part012SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block193Part012] using hcert

def TailChunk000Sub000Block193Part013SupportExplicit : Finset ℕ :=
  ([8007] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block193Part013 : ℚ :=
  (2048383358725 : ℚ) / 1552834479205122048

def SurrogateDiagonalTailChunk000Sub000Block193Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8007
    = surrogateDiagTailX0RatChunk000Sub000Block193Part013

theorem surrogateDiagonalTailChunk000Sub000Block193Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block193Part013CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block193Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block193Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block193Part013CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block193Part013SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block193Part013] using hcert

def TailChunk000Sub000Block193Part014SupportExplicit : Finset ℕ :=
  ([8009] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block193Part014 : ℚ :=
  (1002251265625 : ℚ) / 2570769421316608512

def SurrogateDiagonalTailChunk000Sub000Block193Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8009
    = surrogateDiagTailX0RatChunk000Sub000Block193Part014

theorem surrogateDiagonalTailChunk000Sub000Block193Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block193Part014CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block193Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block193Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block193Part014CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block193Part014SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block193Part014] using hcert

def TailChunk000Sub000Block193Part015SupportExplicit : Finset ℕ :=
  ([8011] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block193Part015 : ℚ :=
  (1604403025 : ℚ) / 4117341735696402

def SurrogateDiagonalTailChunk000Sub000Block193Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8011
    = surrogateDiagTailX0RatChunk000Sub000Block193Part015

theorem surrogateDiagonalTailChunk000Sub000Block193Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block193Part015CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block193Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block193Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block193Part015CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block193Part015SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block193Part015] using hcert

def TailChunk000Sub000Block193Part016SupportExplicit : Finset ℕ :=
  ([8013] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block193Part016 : ℚ :=
  (22287625657 : ℚ) / 20332551781216800

def SurrogateDiagonalTailChunk000Sub000Block193Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8013
    = surrogateDiagTailX0RatChunk000Sub000Block193Part016

theorem surrogateDiagonalTailChunk000Sub000Block193Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block193Part016CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block193Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block193Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block193Part016CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block193Part016SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block193Part016] using hcert

def TailChunk000Sub000Block193Part017SupportExplicit : Finset ℕ :=
  ([8014] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block193Part017 : ℚ :=
  (2006604723775 : ℚ) / 643977418372968648

def SurrogateDiagonalTailChunk000Sub000Block193Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8014
    = surrogateDiagTailX0RatChunk000Sub000Block193Part017

theorem surrogateDiagonalTailChunk000Sub000Block193Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block193Part017CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block193Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block193Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block193Part017CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block193Part017SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block193Part017] using hcert

def TailChunk000Sub000Block193Part018SupportExplicit : Finset ℕ :=
  ([8015] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block193Part018 : ℚ :=
  (2483681656975 : ℚ) / 2241874069333475328

def SurrogateDiagonalTailChunk000Sub000Block193Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8015
    = surrogateDiagTailX0RatChunk000Sub000Block193Part018

theorem surrogateDiagonalTailChunk000Sub000Block193Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block193Part018CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block193Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block193Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block193Part018CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block193Part018SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block193Part018] using hcert

def TailChunk000Sub000Block193Part019SupportExplicit : Finset ℕ :=
  ([8017] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block193Part019 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub000Block193Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8017
    = surrogateDiagTailX0RatChunk000Sub000Block193Part019

theorem surrogateDiagonalTailChunk000Sub000Block193Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block193Part019CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block193Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block193Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block193Part019CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block193Part019SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block193Part019] using hcert

def TailChunk000Sub000Block193Part020SupportExplicit : Finset ℕ :=
  ([8018] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block193Part020 : ℚ :=
  (38487901351 : ℚ) / 20419920623491200

def SurrogateDiagonalTailChunk000Sub000Block193Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8018
    = surrogateDiagTailX0RatChunk000Sub000Block193Part020

theorem surrogateDiagonalTailChunk000Sub000Block193Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block193Part020CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block193Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block193Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block193Part020CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block193Part020SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block193Part020] using hcert

def TailChunk000Sub000Block193Part021SupportExplicit : Finset ℕ :=
  ([8021] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block193Part021 : ℚ :=
  (3018978925 : ℚ) / 116652679178821632

def SurrogateDiagonalTailChunk000Sub000Block193Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8021
    = surrogateDiagTailX0RatChunk000Sub000Block193Part021

theorem surrogateDiagonalTailChunk000Sub000Block193Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block193Part021CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block193Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block193Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block193Part021CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block193Part021SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block193Part021] using hcert

def TailChunk000Sub000Block193Part022SupportExplicit : Finset ℕ :=
  ([8022] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block193Part022 : ℚ :=
  (540959027 : ℚ) / 54057534465024

def SurrogateDiagonalTailChunk000Sub000Block193Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8022
    = surrogateDiagTailX0RatChunk000Sub000Block193Part022

theorem surrogateDiagonalTailChunk000Sub000Block193Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block193Part022CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block193Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block193Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block193Part022CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block193Part022SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block193Part022] using hcert

def TailChunk000Sub000Block193Part023SupportExplicit : Finset ℕ :=
  ([8023] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block193Part023 : ℚ :=
  (12963427 : ℚ) / 2159300335632384

def SurrogateDiagonalTailChunk000Sub000Block193Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8023
    = surrogateDiagTailX0RatChunk000Sub000Block193Part023

theorem surrogateDiagonalTailChunk000Sub000Block193Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block193Part023CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block193Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block193Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block193Part023CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block193Part023SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block193Part023] using hcert

def TailChunk000Sub000Block193Part024SupportExplicit : Finset ℕ :=
  ([8026] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block193Part024 : ℚ :=
  (251627640625 : ℚ) / 161961043024418592

def SurrogateDiagonalTailChunk000Sub000Block193Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8026
    = surrogateDiagTailX0RatChunk000Sub000Block193Part024

theorem surrogateDiagonalTailChunk000Sub000Block193Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block193Part024CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block193Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block193Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block193Part024CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block193Part024SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block193Part024] using hcert

def surrogateDiagonalTailChunk000Sub000Block193HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block193Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block193Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block193Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block193Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block193Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block193Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block193Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block193Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block193Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block193Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block193Head : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block193Part000
    + surrogateDiagTailX0RatChunk000Sub000Block193Part001
    + surrogateDiagTailX0RatChunk000Sub000Block193Part002
    + surrogateDiagTailX0RatChunk000Sub000Block193Part003
    + surrogateDiagTailX0RatChunk000Sub000Block193Part004
    + surrogateDiagTailX0RatChunk000Sub000Block193Part005
    + surrogateDiagTailX0RatChunk000Sub000Block193Part006
    + surrogateDiagTailX0RatChunk000Sub000Block193Part007
    + surrogateDiagTailX0RatChunk000Sub000Block193Part008
    + surrogateDiagTailX0RatChunk000Sub000Block193Part009

def surrogateDiagonalTailChunk000Sub000Block193MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block193Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block193Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block193Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block193Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block193Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block193Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block193Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block193Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block193Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block193Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block193Mid : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block193Part010
    + surrogateDiagTailX0RatChunk000Sub000Block193Part011
    + surrogateDiagTailX0RatChunk000Sub000Block193Part012
    + surrogateDiagTailX0RatChunk000Sub000Block193Part013
    + surrogateDiagTailX0RatChunk000Sub000Block193Part014
    + surrogateDiagTailX0RatChunk000Sub000Block193Part015
    + surrogateDiagTailX0RatChunk000Sub000Block193Part016
    + surrogateDiagTailX0RatChunk000Sub000Block193Part017
    + surrogateDiagTailX0RatChunk000Sub000Block193Part018
    + surrogateDiagTailX0RatChunk000Sub000Block193Part019

def surrogateDiagonalTailChunk000Sub000Block193TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block193Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block193Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block193Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block193Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block193Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block193Tail : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block193Part020
    + surrogateDiagTailX0RatChunk000Sub000Block193Part021
    + surrogateDiagTailX0RatChunk000Sub000Block193Part022
    + surrogateDiagTailX0RatChunk000Sub000Block193Part023
    + surrogateDiagTailX0RatChunk000Sub000Block193Part024

def surrogateDiagonalTailChunk000Sub000Block193Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub000Block193HeadSum X0
    + surrogateDiagonalTailChunk000Sub000Block193MidSum X0
    + surrogateDiagonalTailChunk000Sub000Block193TailSum X0

def surrogateDiagTailX0RatChunk000Sub000Block193 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block193Part000
    + surrogateDiagTailX0RatChunk000Sub000Block193Part001
    + surrogateDiagTailX0RatChunk000Sub000Block193Part002
    + surrogateDiagTailX0RatChunk000Sub000Block193Part003
    + surrogateDiagTailX0RatChunk000Sub000Block193Part004
    + surrogateDiagTailX0RatChunk000Sub000Block193Part005
    + surrogateDiagTailX0RatChunk000Sub000Block193Part006
    + surrogateDiagTailX0RatChunk000Sub000Block193Part007
    + surrogateDiagTailX0RatChunk000Sub000Block193Part008
    + surrogateDiagTailX0RatChunk000Sub000Block193Part009
    + surrogateDiagTailX0RatChunk000Sub000Block193Part010
    + surrogateDiagTailX0RatChunk000Sub000Block193Part011
    + surrogateDiagTailX0RatChunk000Sub000Block193Part012
    + surrogateDiagTailX0RatChunk000Sub000Block193Part013
    + surrogateDiagTailX0RatChunk000Sub000Block193Part014
    + surrogateDiagTailX0RatChunk000Sub000Block193Part015
    + surrogateDiagTailX0RatChunk000Sub000Block193Part016
    + surrogateDiagTailX0RatChunk000Sub000Block193Part017
    + surrogateDiagTailX0RatChunk000Sub000Block193Part018
    + surrogateDiagTailX0RatChunk000Sub000Block193Part019
    + surrogateDiagTailX0RatChunk000Sub000Block193Part020
    + surrogateDiagTailX0RatChunk000Sub000Block193Part021
    + surrogateDiagTailX0RatChunk000Sub000Block193Part022
    + surrogateDiagTailX0RatChunk000Sub000Block193Part023
    + surrogateDiagTailX0RatChunk000Sub000Block193Part024

theorem surrogateDiagTailX0RatChunk000Sub000Block193_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk000Sub000Block193Head + surrogateDiagTailX0RatChunk000Sub000Block193Mid + surrogateDiagTailX0RatChunk000Sub000Block193Tail =
      surrogateDiagTailX0RatChunk000Sub000Block193 := by
  unfold surrogateDiagTailX0RatChunk000Sub000Block193Head surrogateDiagTailX0RatChunk000Sub000Block193Mid surrogateDiagTailX0RatChunk000Sub000Block193Tail surrogateDiagTailX0RatChunk000Sub000Block193
  ring

def SurrogateDiagonalTailChunk000Sub000Block193HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block193HeadSum X0 = surrogateDiagTailX0RatChunk000Sub000Block193Head

def SurrogateDiagonalTailChunk000Sub000Block193MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block193MidSum X0 = surrogateDiagTailX0RatChunk000Sub000Block193Mid

def SurrogateDiagonalTailChunk000Sub000Block193TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block193TailSum X0 = surrogateDiagTailX0RatChunk000Sub000Block193Tail

theorem surrogateDiagonalTailChunk000Sub000Block193_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk000Sub000Block193HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk000Sub000Block193MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk000Sub000Block193TailCertificateAt X0) :
    surrogateDiagonalTailChunk000Sub000Block193Sum X0 = surrogateDiagTailX0RatChunk000Sub000Block193 := by
  unfold SurrogateDiagonalTailChunk000Sub000Block193HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk000Sub000Block193MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk000Sub000Block193TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk000Sub000Block193Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk000Sub000Block193_eq_head_add_mid_add_tail

/-- Block 194 covers tail-support indices [4850,4875) and q from 8027 to 8065. -/

def TailChunk000Sub000Block194Part000SupportExplicit : Finset ℕ :=
  ([8027] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block194Part000 : ℚ :=
  (112553748475 : ℚ) / 8590818781994600448

def SurrogateDiagonalTailChunk000Sub000Block194Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8027
    = surrogateDiagTailX0RatChunk000Sub000Block194Part000

theorem surrogateDiagonalTailChunk000Sub000Block194Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block194Part000CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block194Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block194Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block194Part000CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block194Part000SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block194Part000] using hcert

def TailChunk000Sub000Block194Part001SupportExplicit : Finset ℕ :=
  ([8029] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block194Part001 : ℚ :=
  (717646751 : ℚ) / 6531653077401600

def SurrogateDiagonalTailChunk000Sub000Block194Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8029
    = surrogateDiagTailX0RatChunk000Sub000Block194Part001

theorem surrogateDiagonalTailChunk000Sub000Block194Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block194Part001CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block194Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block194Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block194Part001CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block194Part001SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block194Part001] using hcert

def TailChunk000Sub000Block194Part002SupportExplicit : Finset ℕ :=
  ([8030] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block194Part002 : ℚ :=
  (10349026417 : ℚ) / 2293694359142400

def SurrogateDiagonalTailChunk000Sub000Block194Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8030
    = surrogateDiagTailX0RatChunk000Sub000Block194Part002

theorem surrogateDiagonalTailChunk000Sub000Block194Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block194Part002CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block194Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block194Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block194Part002CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block194Part002SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block194Part002] using hcert

def TailChunk000Sub000Block194Part003SupportExplicit : Finset ℕ :=
  ([8031] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block194Part003 : ℚ :=
  (447783916475 : ℚ) / 1025796663760610304

def SurrogateDiagonalTailChunk000Sub000Block194Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8031
    = surrogateDiagTailX0RatChunk000Sub000Block194Part003

theorem surrogateDiagonalTailChunk000Sub000Block194Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block194Part003CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block194Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block194Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block194Part003CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block194Part003SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block194Part003] using hcert

def TailChunk000Sub000Block194Part004SupportExplicit : Finset ℕ :=
  ([8033] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block194Part004 : ℚ :=
  (13448062675 : ℚ) / 1274081684275298304

def SurrogateDiagonalTailChunk000Sub000Block194Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8033
    = surrogateDiagTailX0RatChunk000Sub000Block194Part004

theorem surrogateDiagonalTailChunk000Sub000Block194Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block194Part004CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block194Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block194Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block194Part004CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block194Part004SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block194Part004] using hcert

def TailChunk000Sub000Block194Part005SupportExplicit : Finset ℕ :=
  ([8034] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block194Part005 : ℚ :=
  (20024331175 : ℚ) / 2494422481379328

def SurrogateDiagonalTailChunk000Sub000Block194Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8034
    = surrogateDiagTailX0RatChunk000Sub000Block194Part005

theorem surrogateDiagonalTailChunk000Sub000Block194Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block194Part005CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block194Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block194Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block194Part005CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block194Part005SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block194Part005] using hcert

def TailChunk000Sub000Block194Part006SupportExplicit : Finset ℕ :=
  ([8035] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block194Part006 : ℚ :=
  (60582940775 : ℚ) / 532303106829179136

def SurrogateDiagonalTailChunk000Sub000Block194Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8035
    = surrogateDiagTailX0RatChunk000Sub000Block194Part006

theorem surrogateDiagonalTailChunk000Sub000Block194Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block194Part006CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block194Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block194Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block194Part006CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block194Part006SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block194Part006] using hcert

def TailChunk000Sub000Block194Part007SupportExplicit : Finset ℕ :=
  ([8038] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block194Part007 : ℚ :=
  (252380640625 : ℚ) / 162932078285287122

def SurrogateDiagonalTailChunk000Sub000Block194Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8038
    = surrogateDiagTailX0RatChunk000Sub000Block194Part007

theorem surrogateDiagonalTailChunk000Sub000Block194Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block194Part007CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block194Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block194Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block194Part007CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block194Part007SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block194Part007] using hcert

def TailChunk000Sub000Block194Part008SupportExplicit : Finset ℕ :=
  ([8039] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block194Part008 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub000Block194Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8039
    = surrogateDiagTailX0RatChunk000Sub000Block194Part008

theorem surrogateDiagonalTailChunk000Sub000Block194Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block194Part008CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block194Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block194Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block194Part008CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block194Part008SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block194Part008] using hcert

def TailChunk000Sub000Block194Part009SupportExplicit : Finset ℕ :=
  ([8041] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block194Part009 : ℚ :=
  (234193583 : ℚ) / 3237601502822400

def SurrogateDiagonalTailChunk000Sub000Block194Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8041
    = surrogateDiagTailX0RatChunk000Sub000Block194Part009

theorem surrogateDiagonalTailChunk000Sub000Block194Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block194Part009CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block194Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block194Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block194Part009CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block194Part009SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block194Part009] using hcert

def TailChunk000Sub000Block194Part010SupportExplicit : Finset ℕ :=
  ([8042] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block194Part010 : ℚ :=
  (404211025 : ℚ) / 261210759865632

def SurrogateDiagonalTailChunk000Sub000Block194Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8042
    = surrogateDiagTailX0RatChunk000Sub000Block194Part010

theorem surrogateDiagonalTailChunk000Sub000Block194Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block194Part010CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block194Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block194Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block194Part010CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block194Part010SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block194Part010] using hcert

def TailChunk000Sub000Block194Part011SupportExplicit : Finset ℕ :=
  ([8043] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block194Part011 : ℚ :=
  (870030840325 : ℚ) / 1104092080409069568

def SurrogateDiagonalTailChunk000Sub000Block194Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8043
    = surrogateDiagTailX0RatChunk000Sub000Block194Part011

theorem surrogateDiagonalTailChunk000Sub000Block194Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block194Part011CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block194Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block194Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block194Part011CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block194Part011SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block194Part011] using hcert

def TailChunk000Sub000Block194Part012SupportExplicit : Finset ℕ :=
  ([8045] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block194Part012 : ℚ :=
  (242934146525 : ℚ) / 2139838544819257344

def SurrogateDiagonalTailChunk000Sub000Block194Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8045
    = surrogateDiagTailX0RatChunk000Sub000Block194Part012

theorem surrogateDiagonalTailChunk000Sub000Block194Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block194Part012CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block194Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block194Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block194Part012CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block194Part012SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block194Part012] using hcert

def TailChunk000Sub000Block194Part013SupportExplicit : Finset ℕ :=
  ([8047] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block194Part013 : ℚ :=
  (1350325825 : ℚ) / 52522241387167872

def SurrogateDiagonalTailChunk000Sub000Block194Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8047
    = surrogateDiagTailX0RatChunk000Sub000Block194Part013

theorem surrogateDiagonalTailChunk000Sub000Block194Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block194Part013CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block194Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block194Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block194Part013CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block194Part013SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block194Part013] using hcert

def TailChunk000Sub000Block194Part014SupportExplicit : Finset ℕ :=
  ([8049] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block194Part014 : ℚ :=
  (449792764325 : ℚ) / 1035027621719037504

def SurrogateDiagonalTailChunk000Sub000Block194Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8049
    = surrogateDiagTailX0RatChunk000Sub000Block194Part014

theorem surrogateDiagonalTailChunk000Sub000Block194Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block194Part014CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block194Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block194Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block194Part014CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block194Part014SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block194Part014] using hcert

def TailChunk000Sub000Block194Part015SupportExplicit : Finset ℕ :=
  ([8051] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block194Part015 : ℚ :=
  (6896034425 : ℚ) / 1200265197404553216

def SurrogateDiagonalTailChunk000Sub000Block194Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8051
    = surrogateDiagTailX0RatChunk000Sub000Block194Part015

theorem surrogateDiagonalTailChunk000Sub000Block194Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block194Part015CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block194Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block194Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block194Part015CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block194Part015SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block194Part015] using hcert

def TailChunk000Sub000Block194Part016SupportExplicit : Finset ℕ :=
  ([8053] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block194Part016 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub000Block194Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8053
    = surrogateDiagTailX0RatChunk000Sub000Block194Part016

theorem surrogateDiagonalTailChunk000Sub000Block194Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block194Part016CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block194Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block194Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block194Part016CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block194Part016SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block194Part016] using hcert

def TailChunk000Sub000Block194Part017SupportExplicit : Finset ℕ :=
  ([8054] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block194Part017 : ℚ :=
  (253386390625 : ℚ) / 164233576192819122

def SurrogateDiagonalTailChunk000Sub000Block194Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8054
    = surrogateDiagTailX0RatChunk000Sub000Block194Part017

theorem surrogateDiagonalTailChunk000Sub000Block194Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block194Part017CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block194Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block194Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block194Part017CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block194Part017SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block194Part017] using hcert

def TailChunk000Sub000Block194Part018SupportExplicit : Finset ℕ :=
  ([8057] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block194Part018 : ℚ :=
  (13292042893 : ℚ) / 226716544242000000

def SurrogateDiagonalTailChunk000Sub000Block194Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8057
    = surrogateDiagTailX0RatChunk000Sub000Block194Part018

theorem surrogateDiagonalTailChunk000Sub000Block194Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block194Part018CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block194Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block194Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block194Part018CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block194Part018SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block194Part018] using hcert

def TailChunk000Sub000Block194Part019SupportExplicit : Finset ℕ :=
  ([8058] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block194Part019 : ℚ :=
  (736659448825 : ℚ) / 97052154950320128

def SurrogateDiagonalTailChunk000Sub000Block194Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8058
    = surrogateDiagTailX0RatChunk000Sub000Block194Part019

theorem surrogateDiagonalTailChunk000Sub000Block194Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block194Part019CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block194Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block194Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block194Part019CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block194Part019SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block194Part019] using hcert

def TailChunk000Sub000Block194Part020SupportExplicit : Finset ℕ :=
  ([8059] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block194Part020 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub000Block194Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8059
    = surrogateDiagTailX0RatChunk000Sub000Block194Part020

theorem surrogateDiagonalTailChunk000Sub000Block194Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block194Part020CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block194Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block194Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block194Part020CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block194Part020SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block194Part020] using hcert

def TailChunk000Sub000Block194Part021SupportExplicit : Finset ℕ :=
  ([8061] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block194Part021 : ℚ :=
  (225768685175 : ℚ) / 1041216110446092864

def SurrogateDiagonalTailChunk000Sub000Block194Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8061
    = surrogateDiagTailX0RatChunk000Sub000Block194Part021

theorem surrogateDiagonalTailChunk000Sub000Block194Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block194Part021CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block194Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block194Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block194Part021CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block194Part021SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block194Part021] using hcert

def TailChunk000Sub000Block194Part022SupportExplicit : Finset ℕ :=
  ([8062] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block194Part022 : ℚ :=
  (12144179675 : ℚ) / 6881614035437568

def SurrogateDiagonalTailChunk000Sub000Block194Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8062
    = surrogateDiagTailX0RatChunk000Sub000Block194Part022

theorem surrogateDiagonalTailChunk000Sub000Block194Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block194Part022CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block194Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block194Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block194Part022CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block194Part022SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block194Part022] using hcert

def TailChunk000Sub000Block194Part023SupportExplicit : Finset ℕ :=
  ([8063] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block194Part023 : ℚ :=
  (815440369 : ℚ) / 28716478044779520

def SurrogateDiagonalTailChunk000Sub000Block194Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8063
    = surrogateDiagTailX0RatChunk000Sub000Block194Part023

theorem surrogateDiagonalTailChunk000Sub000Block194Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block194Part023CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block194Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block194Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block194Part023CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block194Part023SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block194Part023] using hcert

def TailChunk000Sub000Block194Part024SupportExplicit : Finset ℕ :=
  ([8065] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block194Part024 : ℚ :=
  (1543802927825 : ℚ) / 2161210049958395904

def SurrogateDiagonalTailChunk000Sub000Block194Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8065
    = surrogateDiagTailX0RatChunk000Sub000Block194Part024

theorem surrogateDiagonalTailChunk000Sub000Block194Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block194Part024CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block194Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block194Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block194Part024CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block194Part024SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block194Part024] using hcert

def surrogateDiagonalTailChunk000Sub000Block194HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block194Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block194Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block194Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block194Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block194Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block194Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block194Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block194Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block194Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block194Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block194Head : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block194Part000
    + surrogateDiagTailX0RatChunk000Sub000Block194Part001
    + surrogateDiagTailX0RatChunk000Sub000Block194Part002
    + surrogateDiagTailX0RatChunk000Sub000Block194Part003
    + surrogateDiagTailX0RatChunk000Sub000Block194Part004
    + surrogateDiagTailX0RatChunk000Sub000Block194Part005
    + surrogateDiagTailX0RatChunk000Sub000Block194Part006
    + surrogateDiagTailX0RatChunk000Sub000Block194Part007
    + surrogateDiagTailX0RatChunk000Sub000Block194Part008
    + surrogateDiagTailX0RatChunk000Sub000Block194Part009

def surrogateDiagonalTailChunk000Sub000Block194MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block194Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block194Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block194Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block194Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block194Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block194Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block194Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block194Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block194Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block194Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block194Mid : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block194Part010
    + surrogateDiagTailX0RatChunk000Sub000Block194Part011
    + surrogateDiagTailX0RatChunk000Sub000Block194Part012
    + surrogateDiagTailX0RatChunk000Sub000Block194Part013
    + surrogateDiagTailX0RatChunk000Sub000Block194Part014
    + surrogateDiagTailX0RatChunk000Sub000Block194Part015
    + surrogateDiagTailX0RatChunk000Sub000Block194Part016
    + surrogateDiagTailX0RatChunk000Sub000Block194Part017
    + surrogateDiagTailX0RatChunk000Sub000Block194Part018
    + surrogateDiagTailX0RatChunk000Sub000Block194Part019

def surrogateDiagonalTailChunk000Sub000Block194TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block194Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block194Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block194Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block194Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block194Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block194Tail : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block194Part020
    + surrogateDiagTailX0RatChunk000Sub000Block194Part021
    + surrogateDiagTailX0RatChunk000Sub000Block194Part022
    + surrogateDiagTailX0RatChunk000Sub000Block194Part023
    + surrogateDiagTailX0RatChunk000Sub000Block194Part024

def surrogateDiagonalTailChunk000Sub000Block194Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub000Block194HeadSum X0
    + surrogateDiagonalTailChunk000Sub000Block194MidSum X0
    + surrogateDiagonalTailChunk000Sub000Block194TailSum X0

def surrogateDiagTailX0RatChunk000Sub000Block194 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block194Part000
    + surrogateDiagTailX0RatChunk000Sub000Block194Part001
    + surrogateDiagTailX0RatChunk000Sub000Block194Part002
    + surrogateDiagTailX0RatChunk000Sub000Block194Part003
    + surrogateDiagTailX0RatChunk000Sub000Block194Part004
    + surrogateDiagTailX0RatChunk000Sub000Block194Part005
    + surrogateDiagTailX0RatChunk000Sub000Block194Part006
    + surrogateDiagTailX0RatChunk000Sub000Block194Part007
    + surrogateDiagTailX0RatChunk000Sub000Block194Part008
    + surrogateDiagTailX0RatChunk000Sub000Block194Part009
    + surrogateDiagTailX0RatChunk000Sub000Block194Part010
    + surrogateDiagTailX0RatChunk000Sub000Block194Part011
    + surrogateDiagTailX0RatChunk000Sub000Block194Part012
    + surrogateDiagTailX0RatChunk000Sub000Block194Part013
    + surrogateDiagTailX0RatChunk000Sub000Block194Part014
    + surrogateDiagTailX0RatChunk000Sub000Block194Part015
    + surrogateDiagTailX0RatChunk000Sub000Block194Part016
    + surrogateDiagTailX0RatChunk000Sub000Block194Part017
    + surrogateDiagTailX0RatChunk000Sub000Block194Part018
    + surrogateDiagTailX0RatChunk000Sub000Block194Part019
    + surrogateDiagTailX0RatChunk000Sub000Block194Part020
    + surrogateDiagTailX0RatChunk000Sub000Block194Part021
    + surrogateDiagTailX0RatChunk000Sub000Block194Part022
    + surrogateDiagTailX0RatChunk000Sub000Block194Part023
    + surrogateDiagTailX0RatChunk000Sub000Block194Part024

theorem surrogateDiagTailX0RatChunk000Sub000Block194_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk000Sub000Block194Head + surrogateDiagTailX0RatChunk000Sub000Block194Mid + surrogateDiagTailX0RatChunk000Sub000Block194Tail =
      surrogateDiagTailX0RatChunk000Sub000Block194 := by
  unfold surrogateDiagTailX0RatChunk000Sub000Block194Head surrogateDiagTailX0RatChunk000Sub000Block194Mid surrogateDiagTailX0RatChunk000Sub000Block194Tail surrogateDiagTailX0RatChunk000Sub000Block194
  ring

def SurrogateDiagonalTailChunk000Sub000Block194HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block194HeadSum X0 = surrogateDiagTailX0RatChunk000Sub000Block194Head

def SurrogateDiagonalTailChunk000Sub000Block194MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block194MidSum X0 = surrogateDiagTailX0RatChunk000Sub000Block194Mid

def SurrogateDiagonalTailChunk000Sub000Block194TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block194TailSum X0 = surrogateDiagTailX0RatChunk000Sub000Block194Tail

theorem surrogateDiagonalTailChunk000Sub000Block194_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk000Sub000Block194HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk000Sub000Block194MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk000Sub000Block194TailCertificateAt X0) :
    surrogateDiagonalTailChunk000Sub000Block194Sum X0 = surrogateDiagTailX0RatChunk000Sub000Block194 := by
  unfold SurrogateDiagonalTailChunk000Sub000Block194HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk000Sub000Block194MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk000Sub000Block194TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk000Sub000Block194Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk000Sub000Block194_eq_head_add_mid_add_tail

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

/-- Block 196 covers tail-support indices [4900,4925) and q from 8106 to 8147. -/

def TailChunk000Sub000Block196Part000SupportExplicit : Finset ℕ :=
  ([8106] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block196Part000 : ℚ :=
  (609805908775 : ℚ) / 70462290712854528

def SurrogateDiagonalTailChunk000Sub000Block196Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8106
    = surrogateDiagTailX0RatChunk000Sub000Block196Part000

theorem surrogateDiagonalTailChunk000Sub000Block196Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block196Part000CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block196Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block196Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block196Part000CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block196Part000SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block196Part000] using hcert

def TailChunk000Sub000Block196Part001SupportExplicit : Finset ℕ :=
  ([8110] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block196Part001 : ℚ :=
  (6900360887 : ℚ) / 2204432913623040

def SurrogateDiagonalTailChunk000Sub000Block196Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8110
    = surrogateDiagTailX0RatChunk000Sub000Block196Part001

theorem surrogateDiagonalTailChunk000Sub000Block196Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block196Part001CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block196Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block196Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block196Part001CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block196Part001SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block196Part001] using hcert

def TailChunk000Sub000Block196Part002SupportExplicit : Finset ℕ :=
  ([8111] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block196Part002 : ℚ :=
  (1644708025 : ℚ) / 4326834332237682

def SurrogateDiagonalTailChunk000Sub000Block196Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8111
    = surrogateDiagTailX0RatChunk000Sub000Block196Part002

theorem surrogateDiagonalTailChunk000Sub000Block196Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block196Part002CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block196Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block196Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block196Part002CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block196Part002SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block196Part002] using hcert

def TailChunk000Sub000Block196Part003SupportExplicit : Finset ℕ :=
  ([8113] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block196Part003 : ℚ :=
  (119209277671 : ℚ) / 176354633089843200

def SurrogateDiagonalTailChunk000Sub000Block196Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8113
    = surrogateDiagTailX0RatChunk000Sub000Block196Part003

theorem surrogateDiagonalTailChunk000Sub000Block196Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block196Part003CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block196Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block196Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block196Part003CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block196Part003SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block196Part003] using hcert

def TailChunk000Sub000Block196Part004SupportExplicit : Finset ℕ :=
  ([8114] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block196Part004 : ℚ :=
  (257175765625 : ℚ) / 169183752291021312

def SurrogateDiagonalTailChunk000Sub000Block196Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8114
    = surrogateDiagTailX0RatChunk000Sub000Block196Part004

theorem surrogateDiagonalTailChunk000Sub000Block196Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block196Part004CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block196Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block196Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block196Part004CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block196Part004SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block196Part004] using hcert

def TailChunk000Sub000Block196Part005SupportExplicit : Finset ℕ :=
  ([8115] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block196Part005 : ℚ :=
  (3772592569 : ℚ) / 1935304615526400

def SurrogateDiagonalTailChunk000Sub000Block196Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8115
    = surrogateDiagTailX0RatChunk000Sub000Block196Part005

theorem surrogateDiagonalTailChunk000Sub000Block196Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block196Part005CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block196Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block196Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block196Part005CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block196Part005SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block196Part005] using hcert

def TailChunk000Sub000Block196Part006SupportExplicit : Finset ℕ :=
  ([8117] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block196Part006 : ℚ :=
  (1029463890625 : ℚ) / 2712283119239176992

def SurrogateDiagonalTailChunk000Sub000Block196Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8117
    = surrogateDiagTailX0RatChunk000Sub000Block196Part006

theorem surrogateDiagonalTailChunk000Sub000Block196Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block196Part006CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block196Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block196Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block196Part006CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block196Part006SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block196Part006] using hcert

def TailChunk000Sub000Block196Part007SupportExplicit : Finset ℕ :=
  ([8119] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block196Part007 : ℚ :=
  (3856244345425 : ℚ) / 8992661292762267648

def SurrogateDiagonalTailChunk000Sub000Block196Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8119
    = surrogateDiagTailX0RatChunk000Sub000Block196Part007

theorem surrogateDiagonalTailChunk000Sub000Block196Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block196Part007CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block196Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block196Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block196Part007CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block196Part007SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block196Part007] using hcert

def TailChunk000Sub000Block196Part008SupportExplicit : Finset ℕ :=
  ([8121] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block196Part008 : ℚ :=
  (35769566275 : ℚ) / 33517995367431762

def SurrogateDiagonalTailChunk000Sub000Block196Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8121
    = surrogateDiagTailX0RatChunk000Sub000Block196Part008

theorem surrogateDiagonalTailChunk000Sub000Block196Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block196Part008CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block196Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block196Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block196Part008CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block196Part008SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block196Part008] using hcert

def TailChunk000Sub000Block196Part009SupportExplicit : Finset ℕ :=
  ([8122] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block196Part009 : ℚ :=
  (39967838227 : ℚ) / 23139036882000000

def SurrogateDiagonalTailChunk000Sub000Block196Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8122
    = surrogateDiagTailX0RatChunk000Sub000Block196Part009

theorem surrogateDiagonalTailChunk000Sub000Block196Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block196Part009CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block196Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block196Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block196Part009CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block196Part009SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block196Part009] using hcert

def TailChunk000Sub000Block196Part010SupportExplicit : Finset ℕ :=
  ([8123] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block196Part010 : ℚ :=
  (1030986390625 : ℚ) / 2720312569141493682

def SurrogateDiagonalTailChunk000Sub000Block196Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8123
    = surrogateDiagTailX0RatChunk000Sub000Block196Part010

theorem surrogateDiagonalTailChunk000Sub000Block196Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block196Part010CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block196Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block196Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block196Part010CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block196Part010SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block196Part010] using hcert

def TailChunk000Sub000Block196Part011SupportExplicit : Finset ℕ :=
  ([8126] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block196Part011 : ℚ :=
  (4797740625 : ℚ) / 2577415585267712

def SurrogateDiagonalTailChunk000Sub000Block196Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8126
    = surrogateDiagTailX0RatChunk000Sub000Block196Part011

theorem surrogateDiagonalTailChunk000Sub000Block196Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block196Part011CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block196Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block196Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block196Part011CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block196Part011SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block196Part011] using hcert

def TailChunk000Sub000Block196Part012SupportExplicit : Finset ℕ :=
  ([8129] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block196Part012 : ℚ :=
  (963200293 : ℚ) / 1977976094355648

def SurrogateDiagonalTailChunk000Sub000Block196Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8129
    = surrogateDiagTailX0RatChunk000Sub000Block196Part012

theorem surrogateDiagonalTailChunk000Sub000Block196Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block196Part012CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block196Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block196Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block196Part012CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block196Part012SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block196Part012] using hcert

def TailChunk000Sub000Block196Part013SupportExplicit : Finset ℕ :=
  ([8130] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block196Part013 : ℚ :=
  (5766950647 : ℚ) / 544304423116800

def SurrogateDiagonalTailChunk000Sub000Block196Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8130
    = surrogateDiagTailX0RatChunk000Sub000Block196Part013

theorem surrogateDiagonalTailChunk000Sub000Block196Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block196Part013CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block196Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block196Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block196Part013CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block196Part013SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block196Part013] using hcert

def TailChunk000Sub000Block196Part014SupportExplicit : Finset ℕ :=
  ([8131] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block196Part014 : ℚ :=
  (3979119430675 : ℚ) / 9798779236138272768

def SurrogateDiagonalTailChunk000Sub000Block196Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8131
    = surrogateDiagTailX0RatChunk000Sub000Block196Part014

theorem surrogateDiagonalTailChunk000Sub000Block196Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block196Part014CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block196Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block196Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block196Part014CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block196Part014SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block196Part014] using hcert

def TailChunk000Sub000Block196Part015SupportExplicit : Finset ℕ :=
  ([8133] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block196Part015 : ℚ :=
  (22960233247 : ℚ) / 21578636788384800

def SurrogateDiagonalTailChunk000Sub000Block196Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8133
    = surrogateDiagTailX0RatChunk000Sub000Block196Part015

theorem surrogateDiagonalTailChunk000Sub000Block196Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block196Part015CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block196Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block196Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block196Part015CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block196Part015SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block196Part015] using hcert

def TailChunk000Sub000Block196Part016SupportExplicit : Finset ℕ :=
  ([8135] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block196Part016 : ℚ :=
  (2976073465825 : ℚ) / 4474546124439472128

def SurrogateDiagonalTailChunk000Sub000Block196Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8135
    = surrogateDiagTailX0RatChunk000Sub000Block196Part016

theorem surrogateDiagonalTailChunk000Sub000Block196Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block196Part016CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block196Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block196Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block196Part016CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block196Part016SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block196Part016] using hcert

def TailChunk000Sub000Block196Part017SupportExplicit : Finset ℕ :=
  ([8137] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block196Part017 : ℚ :=
  (4011236686675 : ℚ) / 10018575069001170048

def SurrogateDiagonalTailChunk000Sub000Block196Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8137
    = surrogateDiagTailX0RatChunk000Sub000Block196Part017

theorem surrogateDiagonalTailChunk000Sub000Block196Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block196Part017CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block196Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block196Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block196Part017CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block196Part017SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block196Part017] using hcert

def TailChunk000Sub000Block196Part018SupportExplicit : Finset ℕ :=
  ([8138] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block196Part018 : ℚ :=
  (204594299675 : ℚ) / 54591837159555072

def SurrogateDiagonalTailChunk000Sub000Block196Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8138
    = surrogateDiagTailX0RatChunk000Sub000Block196Part018

theorem surrogateDiagonalTailChunk000Sub000Block196Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block196Part018CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block196Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block196Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block196Part018CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block196Part018SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block196Part018] using hcert

def TailChunk000Sub000Block196Part019SupportExplicit : Finset ℕ :=
  ([8139] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block196Part019 : ℚ :=
  (1149706308425 : ℚ) / 1082120405667692544

def SurrogateDiagonalTailChunk000Sub000Block196Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8139
    = surrogateDiagTailX0RatChunk000Sub000Block196Part019

theorem surrogateDiagonalTailChunk000Sub000Block196Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block196Part019CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block196Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block196Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block196Part019CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block196Part019SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block196Part019] using hcert

def TailChunk000Sub000Block196Part020SupportExplicit : Finset ℕ :=
  ([8141] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block196Part020 : ℚ :=
  (3378089630875 : ℚ) / 5908216111837619328

def SurrogateDiagonalTailChunk000Sub000Block196Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8141
    = surrogateDiagTailX0RatChunk000Sub000Block196Part020

theorem surrogateDiagonalTailChunk000Sub000Block196Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block196Part020CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block196Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block196Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block196Part020CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block196Part020SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block196Part020] using hcert

def TailChunk000Sub000Block196Part021SupportExplicit : Finset ℕ :=
  ([8142] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block196Part021 : ℚ :=
  (32278226025 : ℚ) / 3213923973810176

def SurrogateDiagonalTailChunk000Sub000Block196Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8142
    = surrogateDiagTailX0RatChunk000Sub000Block196Part021

theorem surrogateDiagonalTailChunk000Sub000Block196Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block196Part021CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block196Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block196Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block196Part021CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block196Part021SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block196Part021] using hcert

def TailChunk000Sub000Block196Part022SupportExplicit : Finset ℕ :=
  ([8143] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block196Part022 : ℚ :=
  (19813465125 : ℚ) / 44557123621249024

def SurrogateDiagonalTailChunk000Sub000Block196Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8143
    = surrogateDiagTailX0RatChunk000Sub000Block196Part022

theorem surrogateDiagonalTailChunk000Sub000Block196Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block196Part022CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block196Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block196Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block196Part022CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block196Part022SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block196Part022] using hcert

def TailChunk000Sub000Block196Part023SupportExplicit : Finset ℕ :=
  ([8146] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block196Part023 : ℚ :=
  (259208265625 : ℚ) / 171869156234015232

def SurrogateDiagonalTailChunk000Sub000Block196Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8146
    = surrogateDiagTailX0RatChunk000Sub000Block196Part023

theorem surrogateDiagonalTailChunk000Sub000Block196Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block196Part023CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block196Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block196Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block196Part023CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block196Part023SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block196Part023] using hcert

def TailChunk000Sub000Block196Part024SupportExplicit : Finset ℕ :=
  ([8147] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block196Part024 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub000Block196Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8147
    = surrogateDiagTailX0RatChunk000Sub000Block196Part024

theorem surrogateDiagonalTailChunk000Sub000Block196Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block196Part024CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block196Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block196Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block196Part024CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block196Part024SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block196Part024] using hcert

def surrogateDiagonalTailChunk000Sub000Block196HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block196Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block196Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block196Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block196Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block196Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block196Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block196Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block196Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block196Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block196Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block196Head : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block196Part000
    + surrogateDiagTailX0RatChunk000Sub000Block196Part001
    + surrogateDiagTailX0RatChunk000Sub000Block196Part002
    + surrogateDiagTailX0RatChunk000Sub000Block196Part003
    + surrogateDiagTailX0RatChunk000Sub000Block196Part004
    + surrogateDiagTailX0RatChunk000Sub000Block196Part005
    + surrogateDiagTailX0RatChunk000Sub000Block196Part006
    + surrogateDiagTailX0RatChunk000Sub000Block196Part007
    + surrogateDiagTailX0RatChunk000Sub000Block196Part008
    + surrogateDiagTailX0RatChunk000Sub000Block196Part009

def surrogateDiagonalTailChunk000Sub000Block196MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block196Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block196Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block196Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block196Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block196Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block196Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block196Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block196Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block196Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block196Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block196Mid : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block196Part010
    + surrogateDiagTailX0RatChunk000Sub000Block196Part011
    + surrogateDiagTailX0RatChunk000Sub000Block196Part012
    + surrogateDiagTailX0RatChunk000Sub000Block196Part013
    + surrogateDiagTailX0RatChunk000Sub000Block196Part014
    + surrogateDiagTailX0RatChunk000Sub000Block196Part015
    + surrogateDiagTailX0RatChunk000Sub000Block196Part016
    + surrogateDiagTailX0RatChunk000Sub000Block196Part017
    + surrogateDiagTailX0RatChunk000Sub000Block196Part018
    + surrogateDiagTailX0RatChunk000Sub000Block196Part019

def surrogateDiagonalTailChunk000Sub000Block196TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block196Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block196Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block196Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block196Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block196Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block196Tail : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block196Part020
    + surrogateDiagTailX0RatChunk000Sub000Block196Part021
    + surrogateDiagTailX0RatChunk000Sub000Block196Part022
    + surrogateDiagTailX0RatChunk000Sub000Block196Part023
    + surrogateDiagTailX0RatChunk000Sub000Block196Part024

def surrogateDiagonalTailChunk000Sub000Block196Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub000Block196HeadSum X0
    + surrogateDiagonalTailChunk000Sub000Block196MidSum X0
    + surrogateDiagonalTailChunk000Sub000Block196TailSum X0

def surrogateDiagTailX0RatChunk000Sub000Block196 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block196Part000
    + surrogateDiagTailX0RatChunk000Sub000Block196Part001
    + surrogateDiagTailX0RatChunk000Sub000Block196Part002
    + surrogateDiagTailX0RatChunk000Sub000Block196Part003
    + surrogateDiagTailX0RatChunk000Sub000Block196Part004
    + surrogateDiagTailX0RatChunk000Sub000Block196Part005
    + surrogateDiagTailX0RatChunk000Sub000Block196Part006
    + surrogateDiagTailX0RatChunk000Sub000Block196Part007
    + surrogateDiagTailX0RatChunk000Sub000Block196Part008
    + surrogateDiagTailX0RatChunk000Sub000Block196Part009
    + surrogateDiagTailX0RatChunk000Sub000Block196Part010
    + surrogateDiagTailX0RatChunk000Sub000Block196Part011
    + surrogateDiagTailX0RatChunk000Sub000Block196Part012
    + surrogateDiagTailX0RatChunk000Sub000Block196Part013
    + surrogateDiagTailX0RatChunk000Sub000Block196Part014
    + surrogateDiagTailX0RatChunk000Sub000Block196Part015
    + surrogateDiagTailX0RatChunk000Sub000Block196Part016
    + surrogateDiagTailX0RatChunk000Sub000Block196Part017
    + surrogateDiagTailX0RatChunk000Sub000Block196Part018
    + surrogateDiagTailX0RatChunk000Sub000Block196Part019
    + surrogateDiagTailX0RatChunk000Sub000Block196Part020
    + surrogateDiagTailX0RatChunk000Sub000Block196Part021
    + surrogateDiagTailX0RatChunk000Sub000Block196Part022
    + surrogateDiagTailX0RatChunk000Sub000Block196Part023
    + surrogateDiagTailX0RatChunk000Sub000Block196Part024

theorem surrogateDiagTailX0RatChunk000Sub000Block196_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk000Sub000Block196Head + surrogateDiagTailX0RatChunk000Sub000Block196Mid + surrogateDiagTailX0RatChunk000Sub000Block196Tail =
      surrogateDiagTailX0RatChunk000Sub000Block196 := by
  unfold surrogateDiagTailX0RatChunk000Sub000Block196Head surrogateDiagTailX0RatChunk000Sub000Block196Mid surrogateDiagTailX0RatChunk000Sub000Block196Tail surrogateDiagTailX0RatChunk000Sub000Block196
  ring

def SurrogateDiagonalTailChunk000Sub000Block196HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block196HeadSum X0 = surrogateDiagTailX0RatChunk000Sub000Block196Head

def SurrogateDiagonalTailChunk000Sub000Block196MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block196MidSum X0 = surrogateDiagTailX0RatChunk000Sub000Block196Mid

def SurrogateDiagonalTailChunk000Sub000Block196TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block196TailSum X0 = surrogateDiagTailX0RatChunk000Sub000Block196Tail

theorem surrogateDiagonalTailChunk000Sub000Block196_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk000Sub000Block196HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk000Sub000Block196MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk000Sub000Block196TailCertificateAt X0) :
    surrogateDiagonalTailChunk000Sub000Block196Sum X0 = surrogateDiagTailX0RatChunk000Sub000Block196 := by
  unfold SurrogateDiagonalTailChunk000Sub000Block196HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk000Sub000Block196MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk000Sub000Block196TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk000Sub000Block196Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk000Sub000Block196_eq_head_add_mid_add_tail

/-- Block 197 covers tail-support indices [4925,4950) and q from 8149 to 8189. -/

def TailChunk000Sub000Block197Part000SupportExplicit : Finset ℕ :=
  ([8149] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block197Part000 : ℚ :=
  (3865196917 : ℚ) / 377877558735667200

def SurrogateDiagonalTailChunk000Sub000Block197Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8149
    = surrogateDiagTailX0RatChunk000Sub000Block197Part000

theorem surrogateDiagonalTailChunk000Sub000Block197Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block197Part000CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block197Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block197Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block197Part000CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block197Part000SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block197Part000] using hcert

def TailChunk000Sub000Block197Part001SupportExplicit : Finset ℕ :=
  ([8151] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block197Part001 : ℚ :=
  (7822374797 : ℚ) / 11611827693158400

def SurrogateDiagonalTailChunk000Sub000Block197Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8151
    = surrogateDiagTailX0RatChunk000Sub000Block197Part001

theorem surrogateDiagonalTailChunk000Sub000Block197Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block197Part001CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block197Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block197Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block197Part001CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block197Part001SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block197Part001] using hcert

def TailChunk000Sub000Block197Part002SupportExplicit : Finset ℕ :=
  ([8153] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block197Part002 : ℚ :=
  (1811592197 : ℚ) / 190874115997761600

def SurrogateDiagonalTailChunk000Sub000Block197Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8153
    = surrogateDiagTailX0RatChunk000Sub000Block197Part002

theorem surrogateDiagonalTailChunk000Sub000Block197Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block197Part002CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block197Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block197Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block197Part002CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block197Part002SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block197Part002] using hcert

def TailChunk000Sub000Block197Part003SupportExplicit : Finset ℕ :=
  ([8155] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block197Part003 : ℚ :=
  (636443376025 : ℚ) / 2403387318560882688

def SurrogateDiagonalTailChunk000Sub000Block197Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8155
    = surrogateDiagTailX0RatChunk000Sub000Block197Part003

theorem surrogateDiagonalTailChunk000Sub000Block197Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block197Part003CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block197Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block197Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block197Part003CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block197Part003SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block197Part003] using hcert

def TailChunk000Sub000Block197Part004SupportExplicit : Finset ℕ :=
  ([8157] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block197Part004 : ℚ :=
  (461940332525 : ℚ) / 1091728519054922304

def SurrogateDiagonalTailChunk000Sub000Block197Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8157
    = surrogateDiagTailX0RatChunk000Sub000Block197Part004

theorem surrogateDiagonalTailChunk000Sub000Block197Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block197Part004CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block197Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block197Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block197Part004CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block197Part004SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block197Part004] using hcert

def TailChunk000Sub000Block197Part005SupportExplicit : Finset ℕ :=
  ([8158] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block197Part005 : ℚ :=
  (259972515625 : ℚ) / 172884378616140882

def SurrogateDiagonalTailChunk000Sub000Block197Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8158
    = surrogateDiagTailX0RatChunk000Sub000Block197Part005

theorem surrogateDiagonalTailChunk000Sub000Block197Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block197Part005CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block197Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block197Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block197Part005CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block197Part005SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block197Part005] using hcert

def TailChunk000Sub000Block197Part006SupportExplicit : Finset ℕ :=
  ([8159] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block197Part006 : ℚ :=
  (2938594789 : ℚ) / 393538817721139200

def SurrogateDiagonalTailChunk000Sub000Block197Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8159
    = surrogateDiagTailX0RatChunk000Sub000Block197Part006

theorem surrogateDiagonalTailChunk000Sub000Block197Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block197Part006CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block197Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block197Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block197Part006CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block197Part006SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block197Part006] using hcert

def TailChunk000Sub000Block197Part007SupportExplicit : Finset ℕ :=
  ([8161] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block197Part007 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub000Block197Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8161
    = surrogateDiagTailX0RatChunk000Sub000Block197Part007

theorem surrogateDiagonalTailChunk000Sub000Block197Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block197Part007CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block197Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block197Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block197Part007CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block197Part007SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block197Part007] using hcert

def TailChunk000Sub000Block197Part008SupportExplicit : Finset ℕ :=
  ([8162] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block197Part008 : ℚ :=
  (26265697 : ℚ) / 7290576543744

def SurrogateDiagonalTailChunk000Sub000Block197Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8162
    = surrogateDiagTailX0RatChunk000Sub000Block197Part008

theorem surrogateDiagonalTailChunk000Sub000Block197Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block197Part008CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block197Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block197Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block197Part008CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block197Part008SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block197Part008] using hcert

def TailChunk000Sub000Block197Part009SupportExplicit : Finset ℕ :=
  ([8165] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block197Part009 : ℚ :=
  (22277081341 : ℚ) / 144015653307187200

def SurrogateDiagonalTailChunk000Sub000Block197Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8165
    = surrogateDiagTailX0RatChunk000Sub000Block197Part009

theorem surrogateDiagonalTailChunk000Sub000Block197Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block197Part009CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block197Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block197Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block197Part009CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block197Part009SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block197Part009] using hcert

def TailChunk000Sub000Block197Part010SupportExplicit : Finset ℕ :=
  ([8166] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block197Part010 : ℚ :=
  (32398539937 : ℚ) / 5474726982451200

def SurrogateDiagonalTailChunk000Sub000Block197Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8166
    = surrogateDiagTailX0RatChunk000Sub000Block197Part010

theorem surrogateDiagonalTailChunk000Sub000Block197Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block197Part010CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block197Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block197Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block197Part010CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block197Part010SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block197Part010] using hcert

def TailChunk000Sub000Block197Part011SupportExplicit : Finset ℕ :=
  ([8167] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block197Part011 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub000Block197Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8167
    = surrogateDiagTailX0RatChunk000Sub000Block197Part011

theorem surrogateDiagonalTailChunk000Sub000Block197Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block197Part011CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block197Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block197Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block197Part011CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block197Part011SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block197Part011] using hcert

def TailChunk000Sub000Block197Part012SupportExplicit : Finset ℕ :=
  ([8169] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block197Part012 : ℚ :=
  (897457791475 : ℚ) / 1175110604448104448

def SurrogateDiagonalTailChunk000Sub000Block197Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8169
    = surrogateDiagTailX0RatChunk000Sub000Block197Part012

theorem surrogateDiagonalTailChunk000Sub000Block197Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block197Part012CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block197Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block197Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block197Part012CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block197Part012SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block197Part012] using hcert

def TailChunk000Sub000Block197Part013SupportExplicit : Finset ℕ :=
  ([8170] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block197Part013 : ℚ :=
  (26760911375 : ℚ) / 6534374599517184

def SurrogateDiagonalTailChunk000Sub000Block197Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8170
    = surrogateDiagTailX0RatChunk000Sub000Block197Part013

theorem surrogateDiagonalTailChunk000Sub000Block197Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block197Part013CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block197Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block197Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block197Part013CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block197Part013SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block197Part013] using hcert

def TailChunk000Sub000Block197Part014SupportExplicit : Finset ℕ :=
  ([8171] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block197Part014 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub000Block197Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8171
    = surrogateDiagTailX0RatChunk000Sub000Block197Part014

theorem surrogateDiagonalTailChunk000Sub000Block197Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block197Part014CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block197Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block197Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block197Part014CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block197Part014SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block197Part014] using hcert

def TailChunk000Sub000Block197Part015SupportExplicit : Finset ℕ :=
  ([8173] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block197Part015 : ℚ :=
  (464208261 : ℚ) / 14437206773315200

def SurrogateDiagonalTailChunk000Sub000Block197Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8173
    = surrogateDiagTailX0RatChunk000Sub000Block197Part015

theorem surrogateDiagonalTailChunk000Sub000Block197Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block197Part015CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block197Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block197Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block197Part015CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block197Part015SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block197Part015] using hcert

def TailChunk000Sub000Block197Part016SupportExplicit : Finset ℕ :=
  ([8174] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block197Part016 : ℚ :=
  (2264371213 : ℚ) / 1366454228198400

def SurrogateDiagonalTailChunk000Sub000Block197Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8174
    = surrogateDiagTailX0RatChunk000Sub000Block197Part016

theorem surrogateDiagonalTailChunk000Sub000Block197Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block197Part016CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block197Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block197Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block197Part016CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block197Part016SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block197Part016] using hcert

def TailChunk000Sub000Block197Part017SupportExplicit : Finset ℕ :=
  ([8177] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block197Part017 : ℚ :=
  (176202106325 : ℚ) / 2853722773870608384

def SurrogateDiagonalTailChunk000Sub000Block197Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8177
    = surrogateDiagTailX0RatChunk000Sub000Block197Part017

theorem surrogateDiagonalTailChunk000Sub000Block197Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block197Part017CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block197Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block197Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block197Part017CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block197Part017SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block197Part017] using hcert

def TailChunk000Sub000Block197Part018SupportExplicit : Finset ℕ :=
  ([8178] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block197Part018 : ℚ :=
  (11158770975 : ℚ) / 1595736587927552

def SurrogateDiagonalTailChunk000Sub000Block197Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8178
    = surrogateDiagTailX0RatChunk000Sub000Block197Part018

theorem surrogateDiagonalTailChunk000Sub000Block197Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block197Part018CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block197Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block197Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block197Part018CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block197Part018SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block197Part018] using hcert

def TailChunk000Sub000Block197Part019SupportExplicit : Finset ℕ :=
  ([8179] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block197Part019 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub000Block197Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8179
    = surrogateDiagTailX0RatChunk000Sub000Block197Part019

theorem surrogateDiagonalTailChunk000Sub000Block197Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block197Part019CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block197Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block197Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block197Part019CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block197Part019SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block197Part019] using hcert

def TailChunk000Sub000Block197Part020SupportExplicit : Finset ℕ :=
  ([8182] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block197Part020 : ℚ :=
  (418407025 : ℚ) / 279885295475922

def SurrogateDiagonalTailChunk000Sub000Block197Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8182
    = surrogateDiagTailX0RatChunk000Sub000Block197Part020

theorem surrogateDiagonalTailChunk000Sub000Block197Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block197Part020CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block197Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block197Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block197Part020CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block197Part020SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block197Part020] using hcert

def TailChunk000Sub000Block197Part021SupportExplicit : Finset ℕ :=
  ([8185] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block197Part021 : ℚ :=
  (251446232975 : ℚ) / 2292820340538753024

def SurrogateDiagonalTailChunk000Sub000Block197Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8185
    = surrogateDiagTailX0RatChunk000Sub000Block197Part021

theorem surrogateDiagonalTailChunk000Sub000Block197Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block197Part021CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block197Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block197Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block197Part021CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block197Part021SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block197Part021] using hcert

def TailChunk000Sub000Block197Part022SupportExplicit : Finset ℕ :=
  ([8186] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block197Part022 : ℚ :=
  (261760140625 : ℚ) / 175270718788890912

def SurrogateDiagonalTailChunk000Sub000Block197Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8186
    = surrogateDiagTailX0RatChunk000Sub000Block197Part022

theorem surrogateDiagonalTailChunk000Sub000Block197Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block197Part022CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block197Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block197Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block197Part022CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block197Part022SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block197Part022] using hcert

def TailChunk000Sub000Block197Part023SupportExplicit : Finset ℕ :=
  ([8187] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block197Part023 : ℚ :=
  (465343401275 : ℚ) / 1107884049628545024

def SurrogateDiagonalTailChunk000Sub000Block197Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8187
    = surrogateDiagTailX0RatChunk000Sub000Block197Part023

theorem surrogateDiagonalTailChunk000Sub000Block197Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block197Part023CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block197Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block197Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block197Part023CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block197Part023SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block197Part023] using hcert

def TailChunk000Sub000Block197Part024SupportExplicit : Finset ℕ :=
  ([8189] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block197Part024 : ℚ :=
  (353295989 : ℚ) / 23930922145783680

def SurrogateDiagonalTailChunk000Sub000Block197Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8189
    = surrogateDiagTailX0RatChunk000Sub000Block197Part024

theorem surrogateDiagonalTailChunk000Sub000Block197Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block197Part024CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block197Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block197Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block197Part024CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block197Part024SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block197Part024] using hcert

def surrogateDiagonalTailChunk000Sub000Block197HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block197Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block197Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block197Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block197Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block197Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block197Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block197Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block197Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block197Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block197Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block197Head : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block197Part000
    + surrogateDiagTailX0RatChunk000Sub000Block197Part001
    + surrogateDiagTailX0RatChunk000Sub000Block197Part002
    + surrogateDiagTailX0RatChunk000Sub000Block197Part003
    + surrogateDiagTailX0RatChunk000Sub000Block197Part004
    + surrogateDiagTailX0RatChunk000Sub000Block197Part005
    + surrogateDiagTailX0RatChunk000Sub000Block197Part006
    + surrogateDiagTailX0RatChunk000Sub000Block197Part007
    + surrogateDiagTailX0RatChunk000Sub000Block197Part008
    + surrogateDiagTailX0RatChunk000Sub000Block197Part009

def surrogateDiagonalTailChunk000Sub000Block197MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block197Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block197Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block197Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block197Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block197Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block197Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block197Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block197Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block197Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block197Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block197Mid : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block197Part010
    + surrogateDiagTailX0RatChunk000Sub000Block197Part011
    + surrogateDiagTailX0RatChunk000Sub000Block197Part012
    + surrogateDiagTailX0RatChunk000Sub000Block197Part013
    + surrogateDiagTailX0RatChunk000Sub000Block197Part014
    + surrogateDiagTailX0RatChunk000Sub000Block197Part015
    + surrogateDiagTailX0RatChunk000Sub000Block197Part016
    + surrogateDiagTailX0RatChunk000Sub000Block197Part017
    + surrogateDiagTailX0RatChunk000Sub000Block197Part018
    + surrogateDiagTailX0RatChunk000Sub000Block197Part019

def surrogateDiagonalTailChunk000Sub000Block197TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block197Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block197Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block197Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block197Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block197Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block197Tail : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block197Part020
    + surrogateDiagTailX0RatChunk000Sub000Block197Part021
    + surrogateDiagTailX0RatChunk000Sub000Block197Part022
    + surrogateDiagTailX0RatChunk000Sub000Block197Part023
    + surrogateDiagTailX0RatChunk000Sub000Block197Part024

def surrogateDiagonalTailChunk000Sub000Block197Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub000Block197HeadSum X0
    + surrogateDiagonalTailChunk000Sub000Block197MidSum X0
    + surrogateDiagonalTailChunk000Sub000Block197TailSum X0

def surrogateDiagTailX0RatChunk000Sub000Block197 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block197Part000
    + surrogateDiagTailX0RatChunk000Sub000Block197Part001
    + surrogateDiagTailX0RatChunk000Sub000Block197Part002
    + surrogateDiagTailX0RatChunk000Sub000Block197Part003
    + surrogateDiagTailX0RatChunk000Sub000Block197Part004
    + surrogateDiagTailX0RatChunk000Sub000Block197Part005
    + surrogateDiagTailX0RatChunk000Sub000Block197Part006
    + surrogateDiagTailX0RatChunk000Sub000Block197Part007
    + surrogateDiagTailX0RatChunk000Sub000Block197Part008
    + surrogateDiagTailX0RatChunk000Sub000Block197Part009
    + surrogateDiagTailX0RatChunk000Sub000Block197Part010
    + surrogateDiagTailX0RatChunk000Sub000Block197Part011
    + surrogateDiagTailX0RatChunk000Sub000Block197Part012
    + surrogateDiagTailX0RatChunk000Sub000Block197Part013
    + surrogateDiagTailX0RatChunk000Sub000Block197Part014
    + surrogateDiagTailX0RatChunk000Sub000Block197Part015
    + surrogateDiagTailX0RatChunk000Sub000Block197Part016
    + surrogateDiagTailX0RatChunk000Sub000Block197Part017
    + surrogateDiagTailX0RatChunk000Sub000Block197Part018
    + surrogateDiagTailX0RatChunk000Sub000Block197Part019
    + surrogateDiagTailX0RatChunk000Sub000Block197Part020
    + surrogateDiagTailX0RatChunk000Sub000Block197Part021
    + surrogateDiagTailX0RatChunk000Sub000Block197Part022
    + surrogateDiagTailX0RatChunk000Sub000Block197Part023
    + surrogateDiagTailX0RatChunk000Sub000Block197Part024

theorem surrogateDiagTailX0RatChunk000Sub000Block197_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk000Sub000Block197Head + surrogateDiagTailX0RatChunk000Sub000Block197Mid + surrogateDiagTailX0RatChunk000Sub000Block197Tail =
      surrogateDiagTailX0RatChunk000Sub000Block197 := by
  unfold surrogateDiagTailX0RatChunk000Sub000Block197Head surrogateDiagTailX0RatChunk000Sub000Block197Mid surrogateDiagTailX0RatChunk000Sub000Block197Tail surrogateDiagTailX0RatChunk000Sub000Block197
  ring

def SurrogateDiagonalTailChunk000Sub000Block197HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block197HeadSum X0 = surrogateDiagTailX0RatChunk000Sub000Block197Head

def SurrogateDiagonalTailChunk000Sub000Block197MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block197MidSum X0 = surrogateDiagTailX0RatChunk000Sub000Block197Mid

def SurrogateDiagonalTailChunk000Sub000Block197TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block197TailSum X0 = surrogateDiagTailX0RatChunk000Sub000Block197Tail

theorem surrogateDiagonalTailChunk000Sub000Block197_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk000Sub000Block197HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk000Sub000Block197MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk000Sub000Block197TailCertificateAt X0) :
    surrogateDiagonalTailChunk000Sub000Block197Sum X0 = surrogateDiagTailX0RatChunk000Sub000Block197 := by
  unfold SurrogateDiagonalTailChunk000Sub000Block197HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk000Sub000Block197MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk000Sub000Block197TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk000Sub000Block197Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk000Sub000Block197_eq_head_add_mid_add_tail

/-- Block 198 covers tail-support indices [4950,4975) and q from 8191 to 8230. -/

def TailChunk000Sub000Block198Part000SupportExplicit : Finset ℕ :=
  ([8191] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block198Part000 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub000Block198Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8191
    = surrogateDiagTailX0RatChunk000Sub000Block198Part000

theorem surrogateDiagonalTailChunk000Sub000Block198Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block198Part000CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block198Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block198Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block198Part000CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block198Part000SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block198Part000] using hcert

def TailChunk000Sub000Block198Part001SupportExplicit : Finset ℕ :=
  ([8193] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block198Part001 : ℚ :=
  (266532211 : ℚ) / 1269870344084160

def SurrogateDiagonalTailChunk000Sub000Block198Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8193
    = surrogateDiagTailX0RatChunk000Sub000Block198Part001

theorem surrogateDiagonalTailChunk000Sub000Block198Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block198Part001CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block198Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block198Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block198Part001CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block198Part001SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block198Part001] using hcert

def TailChunk000Sub000Block198Part002SupportExplicit : Finset ℕ :=
  ([8194] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block198Part002 : ℚ :=
  (39950764387 : ℚ) / 21747620590387200

def SurrogateDiagonalTailChunk000Sub000Block198Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8194
    = surrogateDiagTailX0RatChunk000Sub000Block198Part002

theorem surrogateDiagonalTailChunk000Sub000Block198Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block198Part002CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block198Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block198Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block198Part002CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block198Part002SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block198Part002] using hcert

def TailChunk000Sub000Block198Part003SupportExplicit : Finset ℕ :=
  ([8195] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block198Part003 : ℚ :=
  (1569919329 : ℚ) / 8189972019937280

def SurrogateDiagonalTailChunk000Sub000Block198Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8195
    = surrogateDiagTailX0RatChunk000Sub000Block198Part003

theorem surrogateDiagonalTailChunk000Sub000Block198Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block198Part003CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block198Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block198Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block198Part003CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block198Part003SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block198Part003] using hcert

def TailChunk000Sub000Block198Part004SupportExplicit : Finset ℕ :=
  ([8197] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block198Part004 : ℚ :=
  (136989520963 : ℚ) / 242904353572483200

def SurrogateDiagonalTailChunk000Sub000Block198Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8197
    = surrogateDiagTailX0RatChunk000Sub000Block198Part004

theorem surrogateDiagonalTailChunk000Sub000Block198Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block198Part004CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block198Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block198Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block198Part004CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block198Part004SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block198Part004] using hcert

def TailChunk000Sub000Block198Part005SupportExplicit : Finset ℕ :=
  ([8198] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block198Part005 : ℚ :=
  (2099805079975 : ℚ) / 705203850839694408

def SurrogateDiagonalTailChunk000Sub000Block198Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8198
    = surrogateDiagTailX0RatChunk000Sub000Block198Part005

theorem surrogateDiagonalTailChunk000Sub000Block198Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block198Part005CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block198Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block198Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block198Part005CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block198Part005SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block198Part005] using hcert

def TailChunk000Sub000Block198Part006SupportExplicit : Finset ℕ :=
  ([8201] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block198Part006 : ℚ :=
  (8362781675 : ℚ) / 21116352806982848

def SurrogateDiagonalTailChunk000Sub000Block198Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8201
    = surrogateDiagTailX0RatChunk000Sub000Block198Part006

theorem surrogateDiagonalTailChunk000Sub000Block198Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block198Part006CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block198Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block198Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block198Part006CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block198Part006SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block198Part006] using hcert

def TailChunk000Sub000Block198Part007SupportExplicit : Finset ℕ :=
  ([8202] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block198Part007 : ℚ :=
  (583493467475 : ℚ) / 69649763045895744

def SurrogateDiagonalTailChunk000Sub000Block198Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8202
    = surrogateDiagTailX0RatChunk000Sub000Block198Part007

theorem surrogateDiagonalTailChunk000Sub000Block198Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block198Part007CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block198Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block198Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block198Part007CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block198Part007SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block198Part007] using hcert

def TailChunk000Sub000Block198Part008SupportExplicit : Finset ℕ :=
  ([8203] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block198Part008 : ℚ :=
  (75002272001 : ℚ) / 163359364987929600

def SurrogateDiagonalTailChunk000Sub000Block198Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8203
    = surrogateDiagTailX0RatChunk000Sub000Block198Part008

theorem surrogateDiagonalTailChunk000Sub000Block198Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block198Part008CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block198Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block198Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block198Part008CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block198Part008SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block198Part008] using hcert

def TailChunk000Sub000Block198Part009SupportExplicit : Finset ℕ :=
  ([8205] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block198Part009 : ℚ :=
  (1854216275 : ℚ) / 972481904529408

def SurrogateDiagonalTailChunk000Sub000Block198Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8205
    = surrogateDiagTailX0RatChunk000Sub000Block198Part009

theorem surrogateDiagonalTailChunk000Sub000Block198Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block198Part009CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block198Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block198Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block198Part009CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block198Part009SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block198Part009] using hcert

def TailChunk000Sub000Block198Part010SupportExplicit : Finset ℕ :=
  ([8206] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block198Part010 : ℚ :=
  (94362775 : ℚ) / 24714789009408

def SurrogateDiagonalTailChunk000Sub000Block198Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8206
    = surrogateDiagTailX0RatChunk000Sub000Block198Part010

theorem surrogateDiagonalTailChunk000Sub000Block198Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block198Part010CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block198Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block198Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block198Part010CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block198Part010SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block198Part010] using hcert

def TailChunk000Sub000Block198Part011SupportExplicit : Finset ℕ :=
  ([8207] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block198Part011 : ℚ :=
  (73898626325 : ℚ) / 179995504186616832

def SurrogateDiagonalTailChunk000Sub000Block198Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8207
    = surrogateDiagTailX0RatChunk000Sub000Block198Part011

theorem surrogateDiagonalTailChunk000Sub000Block198Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block198Part011CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block198Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block198Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block198Part011CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block198Part011SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block198Part011] using hcert

def TailChunk000Sub000Block198Part012SupportExplicit : Finset ℕ :=
  ([8209] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block198Part012 : ℚ :=
  (1052932515625 : ℚ) / 2837371869000179712

def SurrogateDiagonalTailChunk000Sub000Block198Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8209
    = surrogateDiagTailX0RatChunk000Sub000Block198Part012

theorem surrogateDiagonalTailChunk000Sub000Block198Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block198Part012CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block198Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block198Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block198Part012CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block198Part012SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block198Part012] using hcert

def TailChunk000Sub000Block198Part013SupportExplicit : Finset ℕ :=
  ([8210] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block198Part013 : ℚ :=
  (6057268399 : ℚ) / 1157663191941120

def SurrogateDiagonalTailChunk000Sub000Block198Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8210
    = surrogateDiagTailX0RatChunk000Sub000Block198Part013

theorem surrogateDiagonalTailChunk000Sub000Block198Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block198Part013CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block198Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block198Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block198Part013CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block198Part013SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block198Part013] using hcert

def TailChunk000Sub000Block198Part014SupportExplicit : Finset ℕ :=
  ([8211] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block198Part014 : ℚ :=
  (1677262452625 : ℚ) / 796017282659647488

def SurrogateDiagonalTailChunk000Sub000Block198Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8211
    = surrogateDiagTailX0RatChunk000Sub000Block198Part014

theorem surrogateDiagonalTailChunk000Sub000Block198Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block198Part014CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block198Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block198Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block198Part014CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block198Part014SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block198Part014] using hcert

def TailChunk000Sub000Block198Part015SupportExplicit : Finset ℕ :=
  ([8213] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block198Part015 : ℚ :=
  (162008179147 : ℚ) / 405600438282883200

def SurrogateDiagonalTailChunk000Sub000Block198Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8213
    = surrogateDiagTailX0RatChunk000Sub000Block198Part015

theorem surrogateDiagonalTailChunk000Sub000Block198Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block198Part015CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block198Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block198Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block198Part015CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block198Part015SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block198Part015] using hcert

def TailChunk000Sub000Block198Part016SupportExplicit : Finset ℕ :=
  ([8215] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block198Part016 : ℚ :=
  (22691958329 : ℚ) / 30328798421975040

def SurrogateDiagonalTailChunk000Sub000Block198Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8215
    = surrogateDiagTailX0RatChunk000Sub000Block198Part016

theorem surrogateDiagonalTailChunk000Sub000Block198Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block198Part016CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block198Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block198Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block198Part016CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block198Part016SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block198Part016] using hcert

def TailChunk000Sub000Block198Part017SupportExplicit : Finset ℕ :=
  ([8218] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block198Part017 : ℚ :=
  (946382789125 : ℚ) / 382139846210544768

def SurrogateDiagonalTailChunk000Sub000Block198Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8218
    = surrogateDiagTailX0RatChunk000Sub000Block198Part017

theorem surrogateDiagonalTailChunk000Sub000Block198Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block198Part017CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block198Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block198Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block198Part017CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block198Part017SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block198Part017] using hcert

def TailChunk000Sub000Block198Part018SupportExplicit : Finset ℕ :=
  ([8219] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block198Part018 : ℚ :=
  (1055499390625 : ℚ) / 2851224507096854322

def SurrogateDiagonalTailChunk000Sub000Block198Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8219
    = surrogateDiagTailX0RatChunk000Sub000Block198Part018

theorem surrogateDiagonalTailChunk000Sub000Block198Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block198Part018CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block198Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block198Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block198Part018CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block198Part018SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block198Part018] using hcert

def TailChunk000Sub000Block198Part019SupportExplicit : Finset ℕ :=
  ([8221] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block198Part019 : ℚ :=
  (1689621025 : ℚ) / 4566401776295712

def SurrogateDiagonalTailChunk000Sub000Block198Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8221
    = surrogateDiagTailX0RatChunk000Sub000Block198Part019

theorem surrogateDiagonalTailChunk000Sub000Block198Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block198Part019CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block198Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block198Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block198Part019CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block198Part019SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block198Part019] using hcert

def TailChunk000Sub000Block198Part020SupportExplicit : Finset ℕ :=
  ([8222] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block198Part020 : ℚ :=
  (422508025 : ℚ) / 285400111018482

def SurrogateDiagonalTailChunk000Sub000Block198Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8222
    = surrogateDiagTailX0RatChunk000Sub000Block198Part020

theorem surrogateDiagonalTailChunk000Sub000Block198Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block198Part020CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block198Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block198Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block198Part020CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block198Part020SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block198Part020] using hcert

def TailChunk000Sub000Block198Part021SupportExplicit : Finset ℕ :=
  ([8223] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block198Part021 : ℚ :=
  (46942504979 : ℚ) / 45100264457241600

def SurrogateDiagonalTailChunk000Sub000Block198Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8223
    = surrogateDiagTailX0RatChunk000Sub000Block198Part021

theorem surrogateDiagonalTailChunk000Sub000Block198Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block198Part021CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block198Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block198Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block198Part021CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block198Part021SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block198Part021] using hcert

def TailChunk000Sub000Block198Part022SupportExplicit : Finset ℕ :=
  ([8227] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block198Part022 : ℚ :=
  (3913708405375 : ℚ) / 9142224179377471488

def SurrogateDiagonalTailChunk000Sub000Block198Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8227
    = surrogateDiagTailX0RatChunk000Sub000Block198Part022

theorem surrogateDiagonalTailChunk000Sub000Block198Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block198Part022CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block198Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block198Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block198Part022CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block198Part022SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block198Part022] using hcert

def TailChunk000Sub000Block198Part023SupportExplicit : Finset ℕ :=
  ([8229] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block198Part023 : ℚ :=
  (16886370197 : ℚ) / 12907406616330240

def SurrogateDiagonalTailChunk000Sub000Block198Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8229
    = surrogateDiagTailX0RatChunk000Sub000Block198Part023

theorem surrogateDiagonalTailChunk000Sub000Block198Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block198Part023CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block198Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block198Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block198Part023CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block198Part023SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block198Part023] using hcert

def TailChunk000Sub000Block198Part024SupportExplicit : Finset ℕ :=
  ([8230] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block198Part024 : ℚ :=
  (888254005375 : ℚ) / 292249713682925568

def SurrogateDiagonalTailChunk000Sub000Block198Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8230
    = surrogateDiagTailX0RatChunk000Sub000Block198Part024

theorem surrogateDiagonalTailChunk000Sub000Block198Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block198Part024CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block198Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block198Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block198Part024CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block198Part024SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block198Part024] using hcert

def surrogateDiagonalTailChunk000Sub000Block198HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block198Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block198Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block198Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block198Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block198Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block198Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block198Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block198Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block198Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block198Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block198Head : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block198Part000
    + surrogateDiagTailX0RatChunk000Sub000Block198Part001
    + surrogateDiagTailX0RatChunk000Sub000Block198Part002
    + surrogateDiagTailX0RatChunk000Sub000Block198Part003
    + surrogateDiagTailX0RatChunk000Sub000Block198Part004
    + surrogateDiagTailX0RatChunk000Sub000Block198Part005
    + surrogateDiagTailX0RatChunk000Sub000Block198Part006
    + surrogateDiagTailX0RatChunk000Sub000Block198Part007
    + surrogateDiagTailX0RatChunk000Sub000Block198Part008
    + surrogateDiagTailX0RatChunk000Sub000Block198Part009

def surrogateDiagonalTailChunk000Sub000Block198MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block198Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block198Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block198Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block198Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block198Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block198Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block198Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block198Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block198Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block198Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block198Mid : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block198Part010
    + surrogateDiagTailX0RatChunk000Sub000Block198Part011
    + surrogateDiagTailX0RatChunk000Sub000Block198Part012
    + surrogateDiagTailX0RatChunk000Sub000Block198Part013
    + surrogateDiagTailX0RatChunk000Sub000Block198Part014
    + surrogateDiagTailX0RatChunk000Sub000Block198Part015
    + surrogateDiagTailX0RatChunk000Sub000Block198Part016
    + surrogateDiagTailX0RatChunk000Sub000Block198Part017
    + surrogateDiagTailX0RatChunk000Sub000Block198Part018
    + surrogateDiagTailX0RatChunk000Sub000Block198Part019

def surrogateDiagonalTailChunk000Sub000Block198TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block198Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block198Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block198Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block198Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block198Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block198Tail : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block198Part020
    + surrogateDiagTailX0RatChunk000Sub000Block198Part021
    + surrogateDiagTailX0RatChunk000Sub000Block198Part022
    + surrogateDiagTailX0RatChunk000Sub000Block198Part023
    + surrogateDiagTailX0RatChunk000Sub000Block198Part024

def surrogateDiagonalTailChunk000Sub000Block198Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub000Block198HeadSum X0
    + surrogateDiagonalTailChunk000Sub000Block198MidSum X0
    + surrogateDiagonalTailChunk000Sub000Block198TailSum X0

def surrogateDiagTailX0RatChunk000Sub000Block198 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block198Part000
    + surrogateDiagTailX0RatChunk000Sub000Block198Part001
    + surrogateDiagTailX0RatChunk000Sub000Block198Part002
    + surrogateDiagTailX0RatChunk000Sub000Block198Part003
    + surrogateDiagTailX0RatChunk000Sub000Block198Part004
    + surrogateDiagTailX0RatChunk000Sub000Block198Part005
    + surrogateDiagTailX0RatChunk000Sub000Block198Part006
    + surrogateDiagTailX0RatChunk000Sub000Block198Part007
    + surrogateDiagTailX0RatChunk000Sub000Block198Part008
    + surrogateDiagTailX0RatChunk000Sub000Block198Part009
    + surrogateDiagTailX0RatChunk000Sub000Block198Part010
    + surrogateDiagTailX0RatChunk000Sub000Block198Part011
    + surrogateDiagTailX0RatChunk000Sub000Block198Part012
    + surrogateDiagTailX0RatChunk000Sub000Block198Part013
    + surrogateDiagTailX0RatChunk000Sub000Block198Part014
    + surrogateDiagTailX0RatChunk000Sub000Block198Part015
    + surrogateDiagTailX0RatChunk000Sub000Block198Part016
    + surrogateDiagTailX0RatChunk000Sub000Block198Part017
    + surrogateDiagTailX0RatChunk000Sub000Block198Part018
    + surrogateDiagTailX0RatChunk000Sub000Block198Part019
    + surrogateDiagTailX0RatChunk000Sub000Block198Part020
    + surrogateDiagTailX0RatChunk000Sub000Block198Part021
    + surrogateDiagTailX0RatChunk000Sub000Block198Part022
    + surrogateDiagTailX0RatChunk000Sub000Block198Part023
    + surrogateDiagTailX0RatChunk000Sub000Block198Part024

theorem surrogateDiagTailX0RatChunk000Sub000Block198_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk000Sub000Block198Head + surrogateDiagTailX0RatChunk000Sub000Block198Mid + surrogateDiagTailX0RatChunk000Sub000Block198Tail =
      surrogateDiagTailX0RatChunk000Sub000Block198 := by
  unfold surrogateDiagTailX0RatChunk000Sub000Block198Head surrogateDiagTailX0RatChunk000Sub000Block198Mid surrogateDiagTailX0RatChunk000Sub000Block198Tail surrogateDiagTailX0RatChunk000Sub000Block198
  ring

def SurrogateDiagonalTailChunk000Sub000Block198HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block198HeadSum X0 = surrogateDiagTailX0RatChunk000Sub000Block198Head

def SurrogateDiagonalTailChunk000Sub000Block198MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block198MidSum X0 = surrogateDiagTailX0RatChunk000Sub000Block198Mid

def SurrogateDiagonalTailChunk000Sub000Block198TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block198TailSum X0 = surrogateDiagTailX0RatChunk000Sub000Block198Tail

theorem surrogateDiagonalTailChunk000Sub000Block198_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk000Sub000Block198HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk000Sub000Block198MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk000Sub000Block198TailCertificateAt X0) :
    surrogateDiagonalTailChunk000Sub000Block198Sum X0 = surrogateDiagTailX0RatChunk000Sub000Block198 := by
  unfold SurrogateDiagonalTailChunk000Sub000Block198HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk000Sub000Block198MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk000Sub000Block198TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk000Sub000Block198Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk000Sub000Block198_eq_head_add_mid_add_tail

/-- Block 199 covers tail-support indices [4975,5000) and q from 8231 to 8269. -/

def TailChunk000Sub000Block199Part000SupportExplicit : Finset ℕ :=
  ([8231] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block199Part000 : ℚ :=
  (1693734025 : ℚ) / 4588663291558482

def SurrogateDiagonalTailChunk000Sub000Block199Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8231
    = surrogateDiagTailX0RatChunk000Sub000Block199Part000

theorem surrogateDiagonalTailChunk000Sub000Block199Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block199Part000CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block199Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block199Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block199Part000CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block199Part000SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block199Part000] using hcert

def TailChunk000Sub000Block199Part001SupportExplicit : Finset ℕ :=
  ([8233] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block199Part001 : ℚ :=
  (1059098265625 : ℚ) / 2870703339862159872

def SurrogateDiagonalTailChunk000Sub000Block199Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8233
    = surrogateDiagTailX0RatChunk000Sub000Block199Part001

theorem surrogateDiagonalTailChunk000Sub000Block199Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block199Part001CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block199Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block199Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block199Part001CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block199Part001SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block199Part001] using hcert

def TailChunk000Sub000Block199Part002SupportExplicit : Finset ℕ :=
  ([8234] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block199Part002 : ℚ :=
  (10613885625 : ℚ) / 6125285815407308

def SurrogateDiagonalTailChunk000Sub000Block199Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8234
    = surrogateDiagTailX0RatChunk000Sub000Block199Part002

theorem surrogateDiagonalTailChunk000Sub000Block199Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block199Part002CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block199Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block199Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block199Part002CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block199Part002SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block199Part002] using hcert

def TailChunk000Sub000Block199Part003SupportExplicit : Finset ℕ :=
  ([8237] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block199Part003 : ℚ :=
  (1060127640625 : ℚ) / 2876287006270539552

def SurrogateDiagonalTailChunk000Sub000Block199Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8237
    = surrogateDiagTailX0RatChunk000Sub000Block199Part003

theorem surrogateDiagonalTailChunk000Sub000Block199Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block199Part003CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block199Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block199Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block199Part003CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block199Part003SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block199Part003] using hcert

def TailChunk000Sub000Block199Part004SupportExplicit : Finset ℕ :=
  ([8238] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block199Part004 : ℚ :=
  (1441875 : ℚ) / 289254654976

def SurrogateDiagonalTailChunk000Sub000Block199Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8238
    = surrogateDiagTailX0RatChunk000Sub000Block199Part004

theorem surrogateDiagonalTailChunk000Sub000Block199Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block199Part004CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block199Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block199Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block199Part004CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block199Part004SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block199Part004] using hcert

def TailChunk000Sub000Block199Part005SupportExplicit : Finset ℕ :=
  ([8239] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block199Part005 : ℚ :=
  (15025056857 : ℚ) / 20456217177350400

def SurrogateDiagonalTailChunk000Sub000Block199Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8239
    = surrogateDiagTailX0RatChunk000Sub000Block199Part005

theorem surrogateDiagonalTailChunk000Sub000Block199Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block199Part005CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block199Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block199Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block199Part005CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block199Part005SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block199Part005] using hcert

def TailChunk000Sub000Block199Part006SupportExplicit : Finset ℕ :=
  ([8241] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block199Part006 : ℚ :=
  (72260881507 : ℚ) / 77736062759731200

def SurrogateDiagonalTailChunk000Sub000Block199Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8241
    = surrogateDiagTailX0RatChunk000Sub000Block199Part006

theorem surrogateDiagonalTailChunk000Sub000Block199Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block199Part006CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block199Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block199Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block199Part006CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block199Part006SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block199Part006] using hcert

def TailChunk000Sub000Block199Part007SupportExplicit : Finset ℕ :=
  ([8242] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block199Part007 : ℚ :=
  (249062593675 : ℚ) / 129252866142707712

def SurrogateDiagonalTailChunk000Sub000Block199Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8242
    = surrogateDiagTailX0RatChunk000Sub000Block199Part007

theorem surrogateDiagonalTailChunk000Sub000Block199Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block199Part007CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block199Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block199Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block199Part007CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block199Part007SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block199Part007] using hcert

def TailChunk000Sub000Block199Part008SupportExplicit : Finset ℕ :=
  ([8243] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block199Part008 : ℚ :=
  (1061672640625 : ℚ) / 2884677773539479762

def SurrogateDiagonalTailChunk000Sub000Block199Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8243
    = surrogateDiagTailX0RatChunk000Sub000Block199Part008

theorem surrogateDiagonalTailChunk000Sub000Block199Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block199Part008CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block199Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block199Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block199Part008CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block199Part008SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block199Part008] using hcert

def TailChunk000Sub000Block199Part009SupportExplicit : Finset ℕ :=
  ([8245] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block199Part009 : ℚ :=
  (929672846375 : ℚ) / 1187710052509679616

def SurrogateDiagonalTailChunk000Sub000Block199Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8245
    = surrogateDiagTailX0RatChunk000Sub000Block199Part009

theorem surrogateDiagonalTailChunk000Sub000Block199Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block199Part009CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block199Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block199Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block199Part009CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block199Part009SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block199Part009] using hcert

def TailChunk000Sub000Block199Part010SupportExplicit : Finset ℕ :=
  ([8246] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block199Part010 : ℚ :=
  (35452096111 : ℚ) / 11022164568115200

def SurrogateDiagonalTailChunk000Sub000Block199Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8246
    = surrogateDiagTailX0RatChunk000Sub000Block199Part010

theorem surrogateDiagonalTailChunk000Sub000Block199Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block199Part010CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block199Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block199Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block199Part010CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block199Part010SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block199Part010] using hcert

def TailChunk000Sub000Block199Part011SupportExplicit : Finset ℕ :=
  ([8247] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block199Part011 : ℚ :=
  (1180423721975 : ℚ) / 1140732354090968064

def SurrogateDiagonalTailChunk000Sub000Block199Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8247
    = surrogateDiagTailX0RatChunk000Sub000Block199Part011

theorem surrogateDiagonalTailChunk000Sub000Block199Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block199Part011CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block199Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block199Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block199Part011CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block199Part011SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block199Part011] using hcert

def TailChunk000Sub000Block199Part012SupportExplicit : Finset ℕ :=
  ([8249] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block199Part012 : ℚ :=
  (85863784075 : ℚ) / 220286406252036096

def SurrogateDiagonalTailChunk000Sub000Block199Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8249
    = surrogateDiagTailX0RatChunk000Sub000Block199Part012

theorem surrogateDiagonalTailChunk000Sub000Block199Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block199Part012CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block199Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block199Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block199Part012CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block199Part012SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block199Part012] using hcert

def TailChunk000Sub000Block199Part013SupportExplicit : Finset ℕ :=
  ([8251] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block199Part013 : ℚ :=
  (113014424075 : ℚ) / 283365033870279168

def SurrogateDiagonalTailChunk000Sub000Block199Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8251
    = surrogateDiagTailX0RatChunk000Sub000Block199Part013

theorem surrogateDiagonalTailChunk000Sub000Block199Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block199Part013CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block199Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block199Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block199Part013CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block199Part013SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block199Part013] using hcert

def TailChunk000Sub000Block199Part014SupportExplicit : Finset ℕ :=
  ([8254] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block199Part014 : ℚ :=
  (266127015625 : ℚ) / 181168947833867922

def SurrogateDiagonalTailChunk000Sub000Block199Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8254
    = surrogateDiagTailX0RatChunk000Sub000Block199Part014

theorem surrogateDiagonalTailChunk000Sub000Block199Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block199Part014CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block199Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block199Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block199Part014CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block199Part014SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block199Part014] using hcert

def TailChunk000Sub000Block199Part015SupportExplicit : Finset ℕ :=
  ([8255] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block199Part015 : ℚ :=
  (2727082194625 : ℚ) / 3345599794952798208

def SurrogateDiagonalTailChunk000Sub000Block199Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8255
    = surrogateDiagTailX0RatChunk000Sub000Block199Part015

theorem surrogateDiagonalTailChunk000Sub000Block199Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block199Part015CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block199Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block199Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block199Part015CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block199Part015SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block199Part015] using hcert

def TailChunk000Sub000Block199Part016SupportExplicit : Finset ℕ :=
  ([8257] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block199Part016 : ℚ :=
  (3988592721775 : ℚ) / 9621652966937666688

def SurrogateDiagonalTailChunk000Sub000Block199Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8257
    = surrogateDiagTailX0RatChunk000Sub000Block199Part016

theorem surrogateDiagonalTailChunk000Sub000Block199Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block199Part016CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block199Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block199Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block199Part016CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block199Part016SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block199Part016] using hcert

def TailChunk000Sub000Block199Part017SupportExplicit : Finset ℕ :=
  ([8258] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block199Part017 : ℚ :=
  (266385015625 : ℚ) / 181520476128018432

def SurrogateDiagonalTailChunk000Sub000Block199Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8258
    = surrogateDiagTailX0RatChunk000Sub000Block199Part017

theorem surrogateDiagonalTailChunk000Sub000Block199Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block199Part017CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block199Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block199Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block199Part017CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block199Part017SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block199Part017] using hcert

def TailChunk000Sub000Block199Part018SupportExplicit : Finset ℕ :=
  ([8259] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block199Part018 : ℚ :=
  (1183861771925 : ℚ) / 1147388688611672064

def SurrogateDiagonalTailChunk000Sub000Block199Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8259
    = surrogateDiagTailX0RatChunk000Sub000Block199Part018

theorem surrogateDiagonalTailChunk000Sub000Block199Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block199Part018CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block199Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block199Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block199Part018CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block199Part018SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block199Part018] using hcert

def TailChunk000Sub000Block199Part019SupportExplicit : Finset ℕ :=
  ([8261] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block199Part019 : ℚ :=
  (4973756249 : ℚ) / 10548984375000000

def SurrogateDiagonalTailChunk000Sub000Block199Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8261
    = surrogateDiagTailX0RatChunk000Sub000Block199Part019

theorem surrogateDiagonalTailChunk000Sub000Block199Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block199Part019CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block199Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block199Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block199Part019CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block199Part019SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block199Part019] using hcert

def TailChunk000Sub000Block199Part020SupportExplicit : Finset ℕ :=
  ([8263] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block199Part020 : ℚ :=
  (1066830765625 : ℚ) / 2912779638999121842

def SurrogateDiagonalTailChunk000Sub000Block199Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8263
    = surrogateDiagTailX0RatChunk000Sub000Block199Part020

theorem surrogateDiagonalTailChunk000Sub000Block199Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block199Part020CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block199Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block199Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block199Part020CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block199Part020SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block199Part020] using hcert

def TailChunk000Sub000Block199Part021SupportExplicit : Finset ℕ :=
  ([8265] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block199Part021 : ℚ :=
  (1580535370675 : ℚ) / 660859218756108288

def SurrogateDiagonalTailChunk000Sub000Block199Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8265
    = surrogateDiagTailX0RatChunk000Sub000Block199Part021

theorem surrogateDiagonalTailChunk000Sub000Block199Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block199Part021CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block199Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block199Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block199Part021CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block199Part021SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block199Part021] using hcert

def TailChunk000Sub000Block199Part022SupportExplicit : Finset ℕ :=
  ([8266] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block199Part022 : ℚ :=
  (2134784082775 : ℚ) / 728900268612981888

def SurrogateDiagonalTailChunk000Sub000Block199Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8266
    = surrogateDiagTailX0RatChunk000Sub000Block199Part022

theorem surrogateDiagonalTailChunk000Sub000Block199Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block199Part022CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block199Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block199Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block199Part022CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block199Part022SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block199Part022] using hcert

def TailChunk000Sub000Block199Part023SupportExplicit : Finset ℕ :=
  ([8267] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block199Part023 : ℚ :=
  (7547486651 : ℚ) / 13961991711974400

def SurrogateDiagonalTailChunk000Sub000Block199Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8267
    = surrogateDiagTailX0RatChunk000Sub000Block199Part023

theorem surrogateDiagonalTailChunk000Sub000Block199Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block199Part023CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block199Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block199Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block199Part023CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block199Part023SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block199Part023] using hcert

def TailChunk000Sub000Block199Part024SupportExplicit : Finset ℕ :=
  ([8269] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block199Part024 : ℚ :=
  (1068380640625 : ℚ) / 2921250094011523872

def SurrogateDiagonalTailChunk000Sub000Block199Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8269
    = surrogateDiagTailX0RatChunk000Sub000Block199Part024

theorem surrogateDiagonalTailChunk000Sub000Block199Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block199Part024CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block199Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block199Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block199Part024CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block199Part024SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block199Part024] using hcert

def surrogateDiagonalTailChunk000Sub000Block199HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block199Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block199Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block199Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block199Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block199Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block199Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block199Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block199Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block199Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block199Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block199Head : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block199Part000
    + surrogateDiagTailX0RatChunk000Sub000Block199Part001
    + surrogateDiagTailX0RatChunk000Sub000Block199Part002
    + surrogateDiagTailX0RatChunk000Sub000Block199Part003
    + surrogateDiagTailX0RatChunk000Sub000Block199Part004
    + surrogateDiagTailX0RatChunk000Sub000Block199Part005
    + surrogateDiagTailX0RatChunk000Sub000Block199Part006
    + surrogateDiagTailX0RatChunk000Sub000Block199Part007
    + surrogateDiagTailX0RatChunk000Sub000Block199Part008
    + surrogateDiagTailX0RatChunk000Sub000Block199Part009

def surrogateDiagonalTailChunk000Sub000Block199MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block199Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block199Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block199Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block199Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block199Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block199Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block199Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block199Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block199Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block199Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block199Mid : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block199Part010
    + surrogateDiagTailX0RatChunk000Sub000Block199Part011
    + surrogateDiagTailX0RatChunk000Sub000Block199Part012
    + surrogateDiagTailX0RatChunk000Sub000Block199Part013
    + surrogateDiagTailX0RatChunk000Sub000Block199Part014
    + surrogateDiagTailX0RatChunk000Sub000Block199Part015
    + surrogateDiagTailX0RatChunk000Sub000Block199Part016
    + surrogateDiagTailX0RatChunk000Sub000Block199Part017
    + surrogateDiagTailX0RatChunk000Sub000Block199Part018
    + surrogateDiagTailX0RatChunk000Sub000Block199Part019

def surrogateDiagonalTailChunk000Sub000Block199TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block199Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block199Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block199Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block199Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block199Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block199Tail : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block199Part020
    + surrogateDiagTailX0RatChunk000Sub000Block199Part021
    + surrogateDiagTailX0RatChunk000Sub000Block199Part022
    + surrogateDiagTailX0RatChunk000Sub000Block199Part023
    + surrogateDiagTailX0RatChunk000Sub000Block199Part024

def surrogateDiagonalTailChunk000Sub000Block199Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub000Block199HeadSum X0
    + surrogateDiagonalTailChunk000Sub000Block199MidSum X0
    + surrogateDiagonalTailChunk000Sub000Block199TailSum X0

def surrogateDiagTailX0RatChunk000Sub000Block199 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block199Part000
    + surrogateDiagTailX0RatChunk000Sub000Block199Part001
    + surrogateDiagTailX0RatChunk000Sub000Block199Part002
    + surrogateDiagTailX0RatChunk000Sub000Block199Part003
    + surrogateDiagTailX0RatChunk000Sub000Block199Part004
    + surrogateDiagTailX0RatChunk000Sub000Block199Part005
    + surrogateDiagTailX0RatChunk000Sub000Block199Part006
    + surrogateDiagTailX0RatChunk000Sub000Block199Part007
    + surrogateDiagTailX0RatChunk000Sub000Block199Part008
    + surrogateDiagTailX0RatChunk000Sub000Block199Part009
    + surrogateDiagTailX0RatChunk000Sub000Block199Part010
    + surrogateDiagTailX0RatChunk000Sub000Block199Part011
    + surrogateDiagTailX0RatChunk000Sub000Block199Part012
    + surrogateDiagTailX0RatChunk000Sub000Block199Part013
    + surrogateDiagTailX0RatChunk000Sub000Block199Part014
    + surrogateDiagTailX0RatChunk000Sub000Block199Part015
    + surrogateDiagTailX0RatChunk000Sub000Block199Part016
    + surrogateDiagTailX0RatChunk000Sub000Block199Part017
    + surrogateDiagTailX0RatChunk000Sub000Block199Part018
    + surrogateDiagTailX0RatChunk000Sub000Block199Part019
    + surrogateDiagTailX0RatChunk000Sub000Block199Part020
    + surrogateDiagTailX0RatChunk000Sub000Block199Part021
    + surrogateDiagTailX0RatChunk000Sub000Block199Part022
    + surrogateDiagTailX0RatChunk000Sub000Block199Part023
    + surrogateDiagTailX0RatChunk000Sub000Block199Part024

theorem surrogateDiagTailX0RatChunk000Sub000Block199_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk000Sub000Block199Head + surrogateDiagTailX0RatChunk000Sub000Block199Mid + surrogateDiagTailX0RatChunk000Sub000Block199Tail =
      surrogateDiagTailX0RatChunk000Sub000Block199 := by
  unfold surrogateDiagTailX0RatChunk000Sub000Block199Head surrogateDiagTailX0RatChunk000Sub000Block199Mid surrogateDiagTailX0RatChunk000Sub000Block199Tail surrogateDiagTailX0RatChunk000Sub000Block199
  ring

def SurrogateDiagonalTailChunk000Sub000Block199HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block199HeadSum X0 = surrogateDiagTailX0RatChunk000Sub000Block199Head

def SurrogateDiagonalTailChunk000Sub000Block199MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block199MidSum X0 = surrogateDiagTailX0RatChunk000Sub000Block199Mid

def SurrogateDiagonalTailChunk000Sub000Block199TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block199TailSum X0 = surrogateDiagTailX0RatChunk000Sub000Block199Tail

theorem surrogateDiagonalTailChunk000Sub000Block199_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk000Sub000Block199HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk000Sub000Block199MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk000Sub000Block199TailCertificateAt X0) :
    surrogateDiagonalTailChunk000Sub000Block199Sum X0 = surrogateDiagTailX0RatChunk000Sub000Block199 := by
  unfold SurrogateDiagonalTailChunk000Sub000Block199HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk000Sub000Block199MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk000Sub000Block199TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk000Sub000Block199Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk000Sub000Block199_eq_head_add_mid_add_tail

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

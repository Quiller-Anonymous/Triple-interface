import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0TailPilot25

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

open scoped BigOperators

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

/- Generated direct-term certificate blocks for tail chunk 000, subchunk 000, blocks [190,191). -/

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

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0TailPilot25

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

open scoped BigOperators

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

/- Generated direct-term certificate blocks for tail chunk 000, subchunk 001, blocks [13,14). -/

/-- Block 013 covers tail-support indices [5325,5350) and q from 8803 to 8842. -/

def TailChunk000Sub001Block013Part000SupportExplicit : Finset ℕ :=
  ([8803] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block013Part000 : ℚ :=
  (1210825140625 : ℚ) / 3752254822680365202

def SurrogateDiagonalTailChunk000Sub001Block013Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8803
    = surrogateDiagTailX0RatChunk000Sub001Block013Part000

theorem surrogateDiagonalTailChunk000Sub001Block013Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block013Part000CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block013Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block013Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block013Part000CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block013Part000SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block013Part000] using hcert

def TailChunk000Sub001Block013Part001SupportExplicit : Finset ℕ :=
  ([8805] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block013Part001 : ℚ :=
  (31230856975 : ℚ) / 18871103516570112

def SurrogateDiagonalTailChunk000Sub001Block013Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8805
    = surrogateDiagTailX0RatChunk000Sub001Block013Part001

theorem surrogateDiagonalTailChunk000Sub001Block013Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block013Part001CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block013Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block013Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block013Part001CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block013Part001SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block013Part001] using hcert

def TailChunk000Sub001Block013Part002SupportExplicit : Finset ℕ :=
  ([8806] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block013Part002 : ℚ :=
  (327470142175 : ℚ) / 118905115577942016

def SurrogateDiagonalTailChunk000Sub001Block013Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8806
    = surrogateDiagTailX0RatChunk000Sub001Block013Part002

theorem surrogateDiagonalTailChunk000Sub001Block013Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block013Part002CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block013Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block013Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block013Part002CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block013Part002SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block013Part002] using hcert

def TailChunk000Sub001Block013Part003SupportExplicit : Finset ℕ :=
  ([8807] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block013Part003 : ℚ :=
  (1211925765625 : ℚ) / 3759080204860640562

def SurrogateDiagonalTailChunk000Sub001Block013Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8807
    = surrogateDiagTailX0RatChunk000Sub001Block013Part003

theorem surrogateDiagonalTailChunk000Sub001Block013Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block013Part003CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block013Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block013Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block013Part003CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block013Part003SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block013Part003] using hcert

def TailChunk000Sub001Block013Part004SupportExplicit : Finset ℕ :=
  ([8809] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block013Part004 : ℚ :=
  (755199670875 : ℚ) / 2078833866932765888

def SurrogateDiagonalTailChunk000Sub001Block013Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8809
    = surrogateDiagTailX0RatChunk000Sub001Block013Part004

theorem surrogateDiagonalTailChunk000Sub001Block013Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block013Part004CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block013Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block013Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block013Part004CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block013Part004SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block013Part004] using hcert

def TailChunk000Sub001Block013Part005SupportExplicit : Finset ℕ :=
  ([8810] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block013Part005 : ℚ :=
  (2714249139 : ℚ) / 1023684777082880

def SurrogateDiagonalTailChunk000Sub001Block013Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8810
    = surrogateDiagTailX0RatChunk000Sub001Block013Part005

theorem surrogateDiagonalTailChunk000Sub001Block013Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block013Part005CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block013Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block013Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block013Part005CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block013Part005SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block013Part005] using hcert

def TailChunk000Sub001Block013Part006SupportExplicit : Finset ℕ :=
  ([8813] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block013Part006 : ℚ :=
  (214442501075 : ℚ) / 450901748854587456

def SurrogateDiagonalTailChunk000Sub001Block013Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8813
    = surrogateDiagTailX0RatChunk000Sub001Block013Part006

theorem surrogateDiagonalTailChunk000Sub001Block013Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block013Part006CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block013Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block013Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block013Part006CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block013Part006SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block013Part006] using hcert

def TailChunk000Sub001Block013Part007SupportExplicit : Finset ℕ :=
  ([8814] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block013Part007 : ℚ :=
  (375410472275 : ℚ) / 65270046296899584

def SurrogateDiagonalTailChunk000Sub001Block013Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8814
    = surrogateDiagTailX0RatChunk000Sub001Block013Part007

theorem surrogateDiagonalTailChunk000Sub001Block013Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block013Part007CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block013Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block013Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block013Part007CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block013Part007SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block013Part007] using hcert

def TailChunk000Sub001Block013Part008SupportExplicit : Finset ℕ :=
  ([8815] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block013Part008 : ℚ :=
  (130889101351 : ℚ) / 203968894677811200

def SurrogateDiagonalTailChunk000Sub001Block013Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8815
    = surrogateDiagTailX0RatChunk000Sub001Block013Part008

theorem surrogateDiagonalTailChunk000Sub001Block013Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block013Part008CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block013Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block013Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block013Part008CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block013Part008SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block013Part008] using hcert

def TailChunk000Sub001Block013Part009SupportExplicit : Finset ℕ :=
  ([8817] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block013Part009 : ℚ :=
  (2158585706125 : ℚ) / 2980945303460162688

def SurrogateDiagonalTailChunk000Sub001Block013Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8817
    = surrogateDiagTailX0RatChunk000Sub001Block013Part009

theorem surrogateDiagonalTailChunk000Sub001Block013Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block013Part009CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block013Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block013Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block013Part009CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block013Part009SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block013Part009] using hcert

def TailChunk000Sub001Block013Part010SupportExplicit : Finset ℕ :=
  ([8818] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block013Part010 : ℚ :=
  (303738765625 : ℚ) / 236011524900966912

def SurrogateDiagonalTailChunk000Sub001Block013Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8818
    = surrogateDiagTailX0RatChunk000Sub001Block013Part010

theorem surrogateDiagonalTailChunk000Sub001Block013Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block013Part010CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block013Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block013Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block013Part010CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block013Part010SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block013Part010] using hcert

def TailChunk000Sub001Block013Part011SupportExplicit : Finset ℕ :=
  ([8819] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block013Part011 : ℚ :=
  (1215230640625 : ℚ) / 3779612229261203922

def SurrogateDiagonalTailChunk000Sub001Block013Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8819
    = surrogateDiagTailX0RatChunk000Sub001Block013Part011

theorem surrogateDiagonalTailChunk000Sub001Block013Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block013Part011CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block013Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block013Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block013Part011CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block013Part011SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block013Part011] using hcert

def TailChunk000Sub001Block013Part012SupportExplicit : Finset ℕ :=
  ([8821] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block013Part012 : ℚ :=
  (1945251025 : ℚ) / 6052867829259552

def SurrogateDiagonalTailChunk000Sub001Block013Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8821
    = surrogateDiagTailX0RatChunk000Sub001Block013Part012

theorem surrogateDiagonalTailChunk000Sub001Block013Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block013Part012CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block013Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block013Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block013Part012CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block013Part012SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block013Part012] using hcert

def TailChunk000Sub001Block013Part013SupportExplicit : Finset ℕ :=
  ([8822] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block013Part013 : ℚ :=
  (44933495149 : ℚ) / 25605120000000000

def SurrogateDiagonalTailChunk000Sub001Block013Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8822
    = surrogateDiagTailX0RatChunk000Sub001Block013Part013

theorem surrogateDiagonalTailChunk000Sub001Block013Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block013Part013CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block013Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block013Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block013Part013CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block013Part013SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block013Part013] using hcert

def TailChunk000Sub001Block013Part014SupportExplicit : Finset ℕ :=
  ([8823] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block013Part014 : ℚ :=
  (668331176325 : ℚ) / 764925792407781376

def SurrogateDiagonalTailChunk000Sub001Block013Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8823
    = surrogateDiagTailX0RatChunk000Sub001Block013Part014

theorem surrogateDiagonalTailChunk000Sub001Block013Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block013Part014CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block013Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block013Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block013Part014CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block013Part014SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block013Part014] using hcert

def TailChunk000Sub001Block013Part015SupportExplicit : Finset ℕ :=
  ([8826] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block013Part015 : ℚ :=
  (37847223727 : ℚ) / 7472676332419200

def SurrogateDiagonalTailChunk000Sub001Block013Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8826
    = surrogateDiagTailX0RatChunk000Sub001Block013Part015

theorem surrogateDiagonalTailChunk000Sub001Block013Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block013Part015CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block013Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block013Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block013Part015CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block013Part015SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block013Part015] using hcert

def TailChunk000Sub001Block013Part016SupportExplicit : Finset ℕ :=
  ([8827] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block013Part016 : ℚ :=
  (378450098875 : ℚ) / 634160616415690752

def SurrogateDiagonalTailChunk000Sub001Block013Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8827
    = surrogateDiagTailX0RatChunk000Sub001Block013Part016

theorem surrogateDiagonalTailChunk000Sub001Block013Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block013Part016CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block013Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block013Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block013Part016CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block013Part016SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block013Part016] using hcert

def TailChunk000Sub001Block013Part017SupportExplicit : Finset ℕ :=
  ([8830] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block013Part017 : ℚ :=
  (486924740375 : ℚ) / 193691770536305664

def SurrogateDiagonalTailChunk000Sub001Block013Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8830
    = surrogateDiagTailX0RatChunk000Sub001Block013Part017

theorem surrogateDiagonalTailChunk000Sub001Block013Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block013Part017CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block013Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block013Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block013Part017CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block013Part017SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block013Part017] using hcert

def TailChunk000Sub001Block013Part018SupportExplicit : Finset ℕ :=
  ([8831] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block013Part018 : ℚ :=
  (1949664025 : ℚ) / 6080365197083442

def SurrogateDiagonalTailChunk000Sub001Block013Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8831
    = surrogateDiagTailX0RatChunk000Sub001Block013Part018

theorem surrogateDiagonalTailChunk000Sub001Block013Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block013Part018CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block013Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block013Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block013Part018CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block013Part018SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block013Part018] using hcert

def TailChunk000Sub001Block013Part019SupportExplicit : Finset ℕ :=
  ([8834] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block013Part019 : ℚ :=
  (10687492783 : ℚ) / 5104980155872800

def SurrogateDiagonalTailChunk000Sub001Block013Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8834
    = surrogateDiagTailX0RatChunk000Sub001Block013Part019

theorem surrogateDiagonalTailChunk000Sub001Block013Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block013Part019CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block013Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block013Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block013Part019CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block013Part019SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block013Part019] using hcert

def TailChunk000Sub001Block013Part020SupportExplicit : Finset ℕ :=
  ([8835] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block013Part020 : ℚ :=
  (72246469153 : ℚ) / 34835483079475200

def SurrogateDiagonalTailChunk000Sub001Block013Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8835
    = surrogateDiagTailX0RatChunk000Sub001Block013Part020

theorem surrogateDiagonalTailChunk000Sub001Block013Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block013Part020CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block013Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block013Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block013Part020CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block013Part020SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block013Part020] using hcert

def TailChunk000Sub001Block013Part021SupportExplicit : Finset ℕ :=
  ([8837] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block013Part021 : ℚ :=
  (1220196390625 : ℚ) / 3810567827054936352

def SurrogateDiagonalTailChunk000Sub001Block013Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8837
    = surrogateDiagTailX0RatChunk000Sub001Block013Part021

theorem surrogateDiagonalTailChunk000Sub001Block013Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block013Part021CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block013Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block013Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block013Part021CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block013Part021SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block013Part021] using hcert

def TailChunk000Sub001Block013Part022SupportExplicit : Finset ℕ :=
  ([8839] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block013Part022 : ℚ :=
  (1220748765625 : ℚ) / 3814019037364427442

def SurrogateDiagonalTailChunk000Sub001Block013Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8839
    = surrogateDiagTailX0RatChunk000Sub001Block013Part022

theorem surrogateDiagonalTailChunk000Sub001Block013Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block013Part022CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block013Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block013Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block013Part022CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block013Part022SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block013Part022] using hcert

def TailChunk000Sub001Block013Part023SupportExplicit : Finset ℕ :=
  ([8841] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block013Part023 : ℚ :=
  (87921696787 : ℚ) / 64537033081651200

def SurrogateDiagonalTailChunk000Sub001Block013Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8841
    = surrogateDiagTailX0RatChunk000Sub001Block013Part023

theorem surrogateDiagonalTailChunk000Sub001Block013Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block013Part023CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block013Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block013Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block013Part023CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block013Part023SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block013Part023] using hcert

def TailChunk000Sub001Block013Part024SupportExplicit : Finset ℕ :=
  ([8842] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block013Part024 : ℚ :=
  (488631025 : ℚ) / 381747259144992

def SurrogateDiagonalTailChunk000Sub001Block013Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8842
    = surrogateDiagTailX0RatChunk000Sub001Block013Part024

theorem surrogateDiagonalTailChunk000Sub001Block013Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block013Part024CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block013Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block013Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block013Part024CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block013Part024SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block013Part024] using hcert

def surrogateDiagonalTailChunk000Sub001Block013HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block013Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block013Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block013Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block013Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block013Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block013Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block013Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block013Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block013Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block013Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block013Head : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block013Part000
    + surrogateDiagTailX0RatChunk000Sub001Block013Part001
    + surrogateDiagTailX0RatChunk000Sub001Block013Part002
    + surrogateDiagTailX0RatChunk000Sub001Block013Part003
    + surrogateDiagTailX0RatChunk000Sub001Block013Part004
    + surrogateDiagTailX0RatChunk000Sub001Block013Part005
    + surrogateDiagTailX0RatChunk000Sub001Block013Part006
    + surrogateDiagTailX0RatChunk000Sub001Block013Part007
    + surrogateDiagTailX0RatChunk000Sub001Block013Part008
    + surrogateDiagTailX0RatChunk000Sub001Block013Part009

def surrogateDiagonalTailChunk000Sub001Block013MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block013Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block013Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block013Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block013Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block013Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block013Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block013Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block013Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block013Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block013Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block013Mid : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block013Part010
    + surrogateDiagTailX0RatChunk000Sub001Block013Part011
    + surrogateDiagTailX0RatChunk000Sub001Block013Part012
    + surrogateDiagTailX0RatChunk000Sub001Block013Part013
    + surrogateDiagTailX0RatChunk000Sub001Block013Part014
    + surrogateDiagTailX0RatChunk000Sub001Block013Part015
    + surrogateDiagTailX0RatChunk000Sub001Block013Part016
    + surrogateDiagTailX0RatChunk000Sub001Block013Part017
    + surrogateDiagTailX0RatChunk000Sub001Block013Part018
    + surrogateDiagTailX0RatChunk000Sub001Block013Part019

def surrogateDiagonalTailChunk000Sub001Block013TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block013Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block013Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block013Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block013Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block013Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block013Tail : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block013Part020
    + surrogateDiagTailX0RatChunk000Sub001Block013Part021
    + surrogateDiagTailX0RatChunk000Sub001Block013Part022
    + surrogateDiagTailX0RatChunk000Sub001Block013Part023
    + surrogateDiagTailX0RatChunk000Sub001Block013Part024

def surrogateDiagonalTailChunk000Sub001Block013Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub001Block013HeadSum X0
    + surrogateDiagonalTailChunk000Sub001Block013MidSum X0
    + surrogateDiagonalTailChunk000Sub001Block013TailSum X0

def surrogateDiagTailX0RatChunk000Sub001Block013 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block013Part000
    + surrogateDiagTailX0RatChunk000Sub001Block013Part001
    + surrogateDiagTailX0RatChunk000Sub001Block013Part002
    + surrogateDiagTailX0RatChunk000Sub001Block013Part003
    + surrogateDiagTailX0RatChunk000Sub001Block013Part004
    + surrogateDiagTailX0RatChunk000Sub001Block013Part005
    + surrogateDiagTailX0RatChunk000Sub001Block013Part006
    + surrogateDiagTailX0RatChunk000Sub001Block013Part007
    + surrogateDiagTailX0RatChunk000Sub001Block013Part008
    + surrogateDiagTailX0RatChunk000Sub001Block013Part009
    + surrogateDiagTailX0RatChunk000Sub001Block013Part010
    + surrogateDiagTailX0RatChunk000Sub001Block013Part011
    + surrogateDiagTailX0RatChunk000Sub001Block013Part012
    + surrogateDiagTailX0RatChunk000Sub001Block013Part013
    + surrogateDiagTailX0RatChunk000Sub001Block013Part014
    + surrogateDiagTailX0RatChunk000Sub001Block013Part015
    + surrogateDiagTailX0RatChunk000Sub001Block013Part016
    + surrogateDiagTailX0RatChunk000Sub001Block013Part017
    + surrogateDiagTailX0RatChunk000Sub001Block013Part018
    + surrogateDiagTailX0RatChunk000Sub001Block013Part019
    + surrogateDiagTailX0RatChunk000Sub001Block013Part020
    + surrogateDiagTailX0RatChunk000Sub001Block013Part021
    + surrogateDiagTailX0RatChunk000Sub001Block013Part022
    + surrogateDiagTailX0RatChunk000Sub001Block013Part023
    + surrogateDiagTailX0RatChunk000Sub001Block013Part024

theorem surrogateDiagTailX0RatChunk000Sub001Block013_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk000Sub001Block013Head + surrogateDiagTailX0RatChunk000Sub001Block013Mid + surrogateDiagTailX0RatChunk000Sub001Block013Tail =
      surrogateDiagTailX0RatChunk000Sub001Block013 := by
  unfold surrogateDiagTailX0RatChunk000Sub001Block013Head surrogateDiagTailX0RatChunk000Sub001Block013Mid surrogateDiagTailX0RatChunk000Sub001Block013Tail surrogateDiagTailX0RatChunk000Sub001Block013
  ring

def SurrogateDiagonalTailChunk000Sub001Block013HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block013HeadSum X0 = surrogateDiagTailX0RatChunk000Sub001Block013Head

def SurrogateDiagonalTailChunk000Sub001Block013MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block013MidSum X0 = surrogateDiagTailX0RatChunk000Sub001Block013Mid

def SurrogateDiagonalTailChunk000Sub001Block013TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block013TailSum X0 = surrogateDiagTailX0RatChunk000Sub001Block013Tail

theorem surrogateDiagonalTailChunk000Sub001Block013_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk000Sub001Block013HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk000Sub001Block013MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk000Sub001Block013TailCertificateAt X0) :
    surrogateDiagonalTailChunk000Sub001Block013Sum X0 = surrogateDiagTailX0RatChunk000Sub001Block013 := by
  unfold SurrogateDiagonalTailChunk000Sub001Block013HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk000Sub001Block013MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk000Sub001Block013TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk000Sub001Block013Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk000Sub001Block013_eq_head_add_mid_add_tail

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

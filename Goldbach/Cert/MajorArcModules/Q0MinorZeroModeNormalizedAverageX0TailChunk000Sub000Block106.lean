import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0TailPilot25

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

open scoped BigOperators

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

/- Generated direct-term certificate blocks for tail chunk 000, subchunk 000, blocks [106,107). -/

/- Block 106 covers tail-support indices [2650,2675) and q from 4407 to 4447. -/

def TailChunk000Sub000Block106Part000SupportExplicit : Finset ℕ :=
  ([4407] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block106Part000 : ℚ :=
  (375410472275 : ℚ) / 65270046296899584

def SurrogateDiagonalTailChunk000Sub000Block106Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4407
    = surrogateDiagTailX0RatChunk000Sub000Block106Part000

theorem surrogateDiagonalTailChunk000Sub000Block106Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block106Part000CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block106Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block106Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block106Part000CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block106Part000SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block106Part000] using hcert

def TailChunk000Sub000Block106Part001SupportExplicit : Finset ℕ :=
  ([4409] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block106Part001 : ℚ :=
  (303738765625 : ℚ) / 236011524900966912

def SurrogateDiagonalTailChunk000Sub000Block106Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4409
    = surrogateDiagTailX0RatChunk000Sub000Block106Part001

theorem surrogateDiagonalTailChunk000Sub000Block106Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block106Part001CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block106Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block106Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block106Part001CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block106Part001SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block106Part001] using hcert

def TailChunk000Sub000Block106Part002SupportExplicit : Finset ℕ :=
  ([4411] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block106Part002 : ℚ :=
  (44933495149 : ℚ) / 25605120000000000

def SurrogateDiagonalTailChunk000Sub000Block106Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4411
    = surrogateDiagTailX0RatChunk000Sub000Block106Part002

theorem surrogateDiagonalTailChunk000Sub000Block106Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block106Part002CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block106Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block106Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block106Part002CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block106Part002SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block106Part002] using hcert

def TailChunk000Sub000Block106Part003SupportExplicit : Finset ℕ :=
  ([4413] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block106Part003 : ℚ :=
  (37847223727 : ℚ) / 7472676332419200

def SurrogateDiagonalTailChunk000Sub000Block106Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4413
    = surrogateDiagTailX0RatChunk000Sub000Block106Part003

theorem surrogateDiagonalTailChunk000Sub000Block106Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block106Part003CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block106Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block106Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block106Part003CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block106Part003SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block106Part003] using hcert

def TailChunk000Sub000Block106Part004SupportExplicit : Finset ℕ :=
  ([4414] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block106Part004 : ℚ :=
  (608734353775 : ℚ) / 59217339454911048

def SurrogateDiagonalTailChunk000Sub000Block106Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4414
    = surrogateDiagTailX0RatChunk000Sub000Block106Part004

theorem surrogateDiagonalTailChunk000Sub000Block106Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block106Part004CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block106Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block106Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block106Part004CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block106Part004SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block106Part004] using hcert

def TailChunk000Sub000Block106Part005SupportExplicit : Finset ℕ :=
  ([4415] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block106Part005 : ℚ :=
  (486924740375 : ℚ) / 193691770536305664

def SurrogateDiagonalTailChunk000Sub000Block106Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4415
    = surrogateDiagTailX0RatChunk000Sub000Block106Part005

theorem surrogateDiagonalTailChunk000Sub000Block106Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block106Part005CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block106Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block106Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block106Part005CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block106Part005SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block106Part005] using hcert

def TailChunk000Sub000Block106Part006SupportExplicit : Finset ℕ :=
  ([4417] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block106Part006 : ℚ :=
  (10687492783 : ℚ) / 5104980155872800

def SurrogateDiagonalTailChunk000Sub000Block106Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4417
    = surrogateDiagTailX0RatChunk000Sub000Block106Part006

theorem surrogateDiagonalTailChunk000Sub000Block106Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block106Part006CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block106Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block106Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block106Part006CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block106Part006SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block106Part006] using hcert

def TailChunk000Sub000Block106Part007SupportExplicit : Finset ℕ :=
  ([4421] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block106Part007 : ℚ :=
  (488631025 : ℚ) / 381747259144992

def SurrogateDiagonalTailChunk000Sub000Block106Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4421
    = surrogateDiagTailX0RatChunk000Sub000Block106Part007

theorem surrogateDiagonalTailChunk000Sub000Block106Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block106Part007CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block106Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block106Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block106Part007CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block106Part007SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block106Part007] using hcert

def TailChunk000Sub000Block106Part008SupportExplicit : Finset ℕ :=
  ([4422] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block106Part008 : ℚ :=
  (15898714411 : ℚ) / 303656495155200

def SurrogateDiagonalTailChunk000Sub000Block106Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4422
    = surrogateDiagTailX0RatChunk000Sub000Block106Part008

theorem surrogateDiagonalTailChunk000Sub000Block106Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block106Part008CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block106Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block106Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block106Part008CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block106Part008SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block106Part008] using hcert

def TailChunk000Sub000Block106Part009SupportExplicit : Finset ℕ :=
  ([4423] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block106Part009 : ℚ :=
  (305670765625 : ℚ) / 239024170949544882

def SurrogateDiagonalTailChunk000Sub000Block106Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4423
    = surrogateDiagTailX0RatChunk000Sub000Block106Part009

theorem surrogateDiagonalTailChunk000Sub000Block106Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block106Part009CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block106Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block106Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block106Part009CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block106Part009SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block106Part009] using hcert

def TailChunk000Sub000Block106Part010SupportExplicit : Finset ℕ :=
  ([4426] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block106Part010 : ℚ :=
  (6244145475 : ℚ) / 407239611689344

def SurrogateDiagonalTailChunk000Sub000Block106Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4426
    = surrogateDiagTailX0RatChunk000Sub000Block106Part010

theorem surrogateDiagonalTailChunk000Sub000Block106Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block106Part010CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block106Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block106Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block106Part010CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block106Part010SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block106Part010] using hcert

def TailChunk000Sub000Block106Part011SupportExplicit : Finset ℕ :=
  ([4427] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block106Part011 : ℚ :=
  (751002857875 : ℚ) / 253482256254468096

def SurrogateDiagonalTailChunk000Sub000Block106Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4427
    = surrogateDiagTailX0RatChunk000Sub000Block106Part011

theorem surrogateDiagonalTailChunk000Sub000Block106Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block106Part011CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block106Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block106Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block106Part011CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block106Part011SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block106Part011] using hcert

def TailChunk000Sub000Block106Part012SupportExplicit : Finset ℕ :=
  ([4429] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block106Part012 : ℚ :=
  (2337253451725 : ℚ) / 842218365626967168

def SurrogateDiagonalTailChunk000Sub000Block106Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4429
    = surrogateDiagTailX0RatChunk000Sub000Block106Part012

theorem surrogateDiagonalTailChunk000Sub000Block106Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block106Part012CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block106Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block106Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block106Part012CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block106Part012SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block106Part012] using hcert

def TailChunk000Sub000Block106Part013SupportExplicit : Finset ℕ :=
  ([4430] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block106Part013 : ℚ :=
  (167322187875 : ℚ) / 8143941528426496

def SurrogateDiagonalTailChunk000Sub000Block106Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4430
    = surrogateDiagTailX0RatChunk000Sub000Block106Part013

theorem surrogateDiagonalTailChunk000Sub000Block106Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block106Part013CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block106Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block106Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block106Part013CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block106Part013SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block106Part013] using hcert

def TailChunk000Sub000Block106Part014SupportExplicit : Finset ℕ :=
  ([4431] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block106Part014 : ℚ :=
  (1681 : ℚ) / 237081600

def SurrogateDiagonalTailChunk000Sub000Block106Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4431
    = surrogateDiagTailX0RatChunk000Sub000Block106Part014

theorem surrogateDiagonalTailChunk000Sub000Block106Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block106Part014CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block106Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block106Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block106Part014CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block106Part014SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block106Part014] using hcert

def TailChunk000Sub000Block106Part015SupportExplicit : Finset ℕ :=
  ([4433] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block106Part015 : ℚ :=
  (6830392709 : ℚ) / 2799919872000000

def SurrogateDiagonalTailChunk000Sub000Block106Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4433
    = surrogateDiagTailX0RatChunk000Sub000Block106Part015

theorem surrogateDiagonalTailChunk000Sub000Block106Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block106Part015CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block106Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block106Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block106Part015CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block106Part015SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block106Part015] using hcert

def TailChunk000Sub000Block106Part016SupportExplicit : Finset ℕ :=
  ([4434] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block106Part016 : ℚ :=
  (110807341375 : ℚ) / 2966964141533472

def SurrogateDiagonalTailChunk000Sub000Block106Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4434
    = surrogateDiagTailX0RatChunk000Sub000Block106Part016

theorem surrogateDiagonalTailChunk000Sub000Block106Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block106Part016CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block106Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block106Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block106Part016CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block106Part016SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block106Part016] using hcert

def TailChunk000Sub000Block106Part017SupportExplicit : Finset ℕ :=
  ([4435] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block106Part017 : ℚ :=
  (343917775125 : ℚ) / 131486285602134016

def SurrogateDiagonalTailChunk000Sub000Block106Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4435
    = surrogateDiagTailX0RatChunk000Sub000Block106Part017

theorem surrogateDiagonalTailChunk000Sub000Block106Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block106Part017CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block106Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block106Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block106Part017CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block106Part017SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block106Part017] using hcert

def TailChunk000Sub000Block106Part018SupportExplicit : Finset ℕ :=
  ([4438] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block106Part018 : ℚ :=
  (134674451125 : ℚ) / 8078304133919232

def SurrogateDiagonalTailChunk000Sub000Block106Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4438
    = surrogateDiagTailX0RatChunk000Sub000Block106Part018

theorem surrogateDiagonalTailChunk000Sub000Block106Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block106Part018CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block106Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block106Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block106Part018CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block106Part018SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block106Part018] using hcert

def TailChunk000Sub000Block106Part019SupportExplicit : Finset ℕ :=
  ([4439] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block106Part019 : ℚ :=
  (1179799303975 : ℚ) / 796017282659647488

def SurrogateDiagonalTailChunk000Sub000Block106Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4439
    = surrogateDiagTailX0RatChunk000Sub000Block106Part019

theorem surrogateDiagonalTailChunk000Sub000Block106Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block106Part019CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block106Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block106Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block106Part019CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block106Part019SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block106Part019] using hcert

def TailChunk000Sub000Block106Part020SupportExplicit : Finset ℕ :=
  ([4441] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block106Part020 : ℚ :=
  (493062025 : ℚ) / 388703750164992

def SurrogateDiagonalTailChunk000Sub000Block106Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4441
    = surrogateDiagTailX0RatChunk000Sub000Block106Part020

theorem surrogateDiagonalTailChunk000Sub000Block106Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block106Part020CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block106Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block106Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block106Part020CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block106Part020SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block106Part020] using hcert

def TailChunk000Sub000Block106Part021SupportExplicit : Finset ℕ :=
  ([4442] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block106Part021 : ℚ :=
  (24659272159 : ℚ) / 2429398438531200

def SurrogateDiagonalTailChunk000Sub000Block106Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4442
    = surrogateDiagTailX0RatChunk000Sub000Block106Part021

theorem surrogateDiagonalTailChunk000Sub000Block106Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block106Part021CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block106Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block106Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block106Part021CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block106Part021SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block106Part021] using hcert

def TailChunk000Sub000Block106Part022SupportExplicit : Finset ℕ :=
  ([4443] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block106Part022 : ℚ :=
  (3288099 : ℚ) / 767656345600

def SurrogateDiagonalTailChunk000Sub000Block106Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4443
    = surrogateDiagTailX0RatChunk000Sub000Block106Part022

theorem surrogateDiagonalTailChunk000Sub000Block106Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block106Part022CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block106Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block106Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block106Part022CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block106Part022SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block106Part022] using hcert

def TailChunk000Sub000Block106Part023SupportExplicit : Finset ℕ :=
  ([4445] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block106Part023 : ℚ :=
  (894686612125 : ℚ) / 209099987184549888

def SurrogateDiagonalTailChunk000Sub000Block106Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4445
    = surrogateDiagTailX0RatChunk000Sub000Block106Part023

theorem surrogateDiagonalTailChunk000Sub000Block106Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block106Part023CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block106Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block106Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block106Part023CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block106Part023SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block106Part023] using hcert

def TailChunk000Sub000Block106Part024SupportExplicit : Finset ℕ :=
  ([4447] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block106Part024 : ℚ :=
  (308997015625 : ℚ) / 244255696465428882

def SurrogateDiagonalTailChunk000Sub000Block106Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4447
    = surrogateDiagTailX0RatChunk000Sub000Block106Part024

theorem surrogateDiagonalTailChunk000Sub000Block106Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block106Part024CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block106Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block106Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block106Part024CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block106Part024SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block106Part024] using hcert

def surrogateDiagonalTailChunk000Sub000Block106HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block106Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block106Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block106Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block106Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block106Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block106Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block106Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block106Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block106Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block106Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block106Head : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block106Part000
    + surrogateDiagTailX0RatChunk000Sub000Block106Part001
    + surrogateDiagTailX0RatChunk000Sub000Block106Part002
    + surrogateDiagTailX0RatChunk000Sub000Block106Part003
    + surrogateDiagTailX0RatChunk000Sub000Block106Part004
    + surrogateDiagTailX0RatChunk000Sub000Block106Part005
    + surrogateDiagTailX0RatChunk000Sub000Block106Part006
    + surrogateDiagTailX0RatChunk000Sub000Block106Part007
    + surrogateDiagTailX0RatChunk000Sub000Block106Part008
    + surrogateDiagTailX0RatChunk000Sub000Block106Part009

def surrogateDiagonalTailChunk000Sub000Block106MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block106Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block106Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block106Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block106Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block106Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block106Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block106Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block106Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block106Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block106Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block106Mid : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block106Part010
    + surrogateDiagTailX0RatChunk000Sub000Block106Part011
    + surrogateDiagTailX0RatChunk000Sub000Block106Part012
    + surrogateDiagTailX0RatChunk000Sub000Block106Part013
    + surrogateDiagTailX0RatChunk000Sub000Block106Part014
    + surrogateDiagTailX0RatChunk000Sub000Block106Part015
    + surrogateDiagTailX0RatChunk000Sub000Block106Part016
    + surrogateDiagTailX0RatChunk000Sub000Block106Part017
    + surrogateDiagTailX0RatChunk000Sub000Block106Part018
    + surrogateDiagTailX0RatChunk000Sub000Block106Part019

def surrogateDiagonalTailChunk000Sub000Block106TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block106Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block106Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block106Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block106Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block106Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block106Tail : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block106Part020
    + surrogateDiagTailX0RatChunk000Sub000Block106Part021
    + surrogateDiagTailX0RatChunk000Sub000Block106Part022
    + surrogateDiagTailX0RatChunk000Sub000Block106Part023
    + surrogateDiagTailX0RatChunk000Sub000Block106Part024

def surrogateDiagonalTailChunk000Sub000Block106Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub000Block106HeadSum X0
    + surrogateDiagonalTailChunk000Sub000Block106MidSum X0
    + surrogateDiagonalTailChunk000Sub000Block106TailSum X0

def surrogateDiagTailX0RatChunk000Sub000Block106 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block106Part000
    + surrogateDiagTailX0RatChunk000Sub000Block106Part001
    + surrogateDiagTailX0RatChunk000Sub000Block106Part002
    + surrogateDiagTailX0RatChunk000Sub000Block106Part003
    + surrogateDiagTailX0RatChunk000Sub000Block106Part004
    + surrogateDiagTailX0RatChunk000Sub000Block106Part005
    + surrogateDiagTailX0RatChunk000Sub000Block106Part006
    + surrogateDiagTailX0RatChunk000Sub000Block106Part007
    + surrogateDiagTailX0RatChunk000Sub000Block106Part008
    + surrogateDiagTailX0RatChunk000Sub000Block106Part009
    + surrogateDiagTailX0RatChunk000Sub000Block106Part010
    + surrogateDiagTailX0RatChunk000Sub000Block106Part011
    + surrogateDiagTailX0RatChunk000Sub000Block106Part012
    + surrogateDiagTailX0RatChunk000Sub000Block106Part013
    + surrogateDiagTailX0RatChunk000Sub000Block106Part014
    + surrogateDiagTailX0RatChunk000Sub000Block106Part015
    + surrogateDiagTailX0RatChunk000Sub000Block106Part016
    + surrogateDiagTailX0RatChunk000Sub000Block106Part017
    + surrogateDiagTailX0RatChunk000Sub000Block106Part018
    + surrogateDiagTailX0RatChunk000Sub000Block106Part019
    + surrogateDiagTailX0RatChunk000Sub000Block106Part020
    + surrogateDiagTailX0RatChunk000Sub000Block106Part021
    + surrogateDiagTailX0RatChunk000Sub000Block106Part022
    + surrogateDiagTailX0RatChunk000Sub000Block106Part023
    + surrogateDiagTailX0RatChunk000Sub000Block106Part024

theorem surrogateDiagTailX0RatChunk000Sub000Block106_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk000Sub000Block106Head + surrogateDiagTailX0RatChunk000Sub000Block106Mid + surrogateDiagTailX0RatChunk000Sub000Block106Tail =
      surrogateDiagTailX0RatChunk000Sub000Block106 := by
  unfold surrogateDiagTailX0RatChunk000Sub000Block106Head surrogateDiagTailX0RatChunk000Sub000Block106Mid surrogateDiagTailX0RatChunk000Sub000Block106Tail surrogateDiagTailX0RatChunk000Sub000Block106
  ring

def SurrogateDiagonalTailChunk000Sub000Block106HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block106HeadSum X0 = surrogateDiagTailX0RatChunk000Sub000Block106Head

def SurrogateDiagonalTailChunk000Sub000Block106MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block106MidSum X0 = surrogateDiagTailX0RatChunk000Sub000Block106Mid

def SurrogateDiagonalTailChunk000Sub000Block106TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block106TailSum X0 = surrogateDiagTailX0RatChunk000Sub000Block106Tail

theorem surrogateDiagonalTailChunk000Sub000Block106_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk000Sub000Block106HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk000Sub000Block106MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk000Sub000Block106TailCertificateAt X0) :
    surrogateDiagonalTailChunk000Sub000Block106Sum X0 = surrogateDiagTailX0RatChunk000Sub000Block106 := by
  unfold SurrogateDiagonalTailChunk000Sub000Block106HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk000Sub000Block106MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk000Sub000Block106TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk000Sub000Block106Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk000Sub000Block106_eq_head_add_mid_add_tail

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage
